import express from 'express';
import session from 'express-session';
import { spawn } from 'child_process';
import { promises as fs, createReadStream } from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import crypto from 'crypto';
import { MongoClient } from 'mongodb';
import { v4 as uuid } from 'uuid';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const DATA_DIR = path.join(__dirname, 'data');
const DOWNLOADS_ROOT = path.join(__dirname, 'user_downloads');
const DOWNLOADS_FILE = path.join(DATA_DIR, 'downloads.json');
const MONGODB_URI = process.env.MONGODB_URI || 'mongodb://127.0.0.1:27017';
const MONGODB_DB_NAME = process.env.MONGODB_DB_NAME || 'wt_downloader';

const app = express();
const PORT = process.env.PORT || 3000;

const MIME_TYPES = {
  mp3: 'audio/mpeg',
  wav: 'audio/wav',
  opus: 'audio/opus',
  m4a: 'audio/mp4',
  webm: 'video/webm',
  mp4: 'video/mp4',
  mkv: 'video/x-matroska'
};

async function inspectMedia(url) {
  return new Promise((resolve, reject) => {
    const infoProcess = spawn('yt-dlp', ['-J', url]);
    let stdout = '';
    let stderr = '';

    infoProcess.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });

    infoProcess.stderr.on('data', (chunk) => {
      stderr += chunk.toString();
    });

    infoProcess.on('error', (error) => {
      const failure = new Error('Failed to start yt-dlp for media inspection');
      failure.cause = error;
      reject(failure);
    });

    infoProcess.on('close', (code) => {
      if (code !== 0) {
        const failure = new Error('Unable to inspect media with yt-dlp');
        failure.stderr = stderr;
        return reject(failure);
      }

      try {
        const info = JSON.parse(stdout);
        resolve(info);
      } catch (error) {
        const failure = new Error('Failed to parse yt-dlp inspection result');
        failure.cause = error;
        failure.stderr = stderr;
        reject(failure);
      }
    });
  });
}

function formatHasDownloadUrl(format) {
  if (!format) return false;
  // ONLY check for DRM. Assume all other formats are valid for analysis.
  if (format.is_drm || (typeof format.drm === 'string' && format.drm !== 'none')) {
    return false;
  }
  // If it's not DRM, let it be included in the analysis.
  return true;
}

function partitionFormats(formats = []) {
  const videoOnly = [];
  const audioOnly = [];
  const progressive = [];
  for (const format of formats) {
    if (!formatHasDownloadUrl(format)) {
      continue;
    }
    const hasVideo = format?.vcodec && format.vcodec !== 'none';
    const hasAudio = format?.acodec && format.acodec !== 'none';
    if (hasVideo && hasAudio) {
      progressive.push(format);
    } else if (hasVideo) {
      videoOnly.push(format);
    } else if (hasAudio) {
      audioOnly.push(format);
    }
  }
  return { videoOnly, audioOnly, progressive };
}

function filterVideoByHeight(formats, maxHeight) {
  if (!maxHeight) {
    return formats.slice();
  }
  const bounded = formats.filter((format) => Number.isFinite(format.height) && format.height <= maxHeight + 1);
  return bounded.length ? bounded : formats.slice();
}

function selectBestProgressiveWithAudio(formats, videoPrefs) {
  const withAudio = formats.filter((format) => format?.acodec && format.acodec !== 'none');
  if (!withAudio.length) {
    return null;
  }
  const bounded = filterVideoByHeight(withAudio, videoPrefs?.maxHeight);
  return selectBestVideoFormat(bounded, videoPrefs);
}

function buildFallbackFormatSelector(presetConfig) {
  const prefersMp4 = String(presetConfig?.mergeOutputFormat ?? '').toLowerCase() === 'mp4'
    || (presetConfig?.videoSelection?.preferExts ?? []).some((ext) => String(ext).toLowerCase() === 'mp4');
  if (prefersMp4) {
    return 'bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best';
  }
  return 'bestvideo*+bestaudio/best';
}

function scorePreference(value, preferences) {
  if (!value || !Array.isArray(preferences) || !preferences.length) {
    return 0;
  }
  const normalized = String(value).toLowerCase();
  for (let index = 0; index < preferences.length; index += 1) {
    const pref = String(preferences[index]).toLowerCase();
    if (!pref) continue;
    if (normalized === pref || normalized.includes(pref)) {
      return (preferences.length - index) * 100;
    }
  }
  return 0;
}

function scoreVideoFormat(format, options = {}) {
  if (!format) return -Infinity;
  const height = Number.isFinite(format.height) ? format.height : 0;
  const fps = Number.isFinite(format.fps) ? format.fps : 0;
  const bitrate = Number.isFinite(format.tbr) ? format.tbr : Number.isFinite(format.vbr) ? format.vbr : 0;

  let score = height * 1000 + fps * 10 + bitrate;
  score += scorePreference(format.vcodec ?? '', options.preferCodecs) * 1000;
  score += scorePreference(format.ext ?? '', options.preferExts) * 1200;
  if (format.acodec && format.acodec !== 'none') {
    score -= 500;
  } else {
    score += 500;
  }
  return score;
}

function scoreAudioFormat(format, options = {}) {
  if (!format) return -Infinity;
  const abr = Number.isFinite(format.abr) ? format.abr : Number.isFinite(format.tbr) ? format.tbr : 0;
  let score = abr * 100;
  score += scorePreference(format.acodec ?? '', options.preferCodecs) * 600;
  score += scorePreference(format.ext ?? '', options.preferExts) * 400;
  if (!format.vcodec || format.vcodec === 'none') {
    score += 2000;
  } else {
    score -= 2000;
  }
  if (Number.isFinite(options.maxAbr) && abr > options.maxAbr) {
    score -= 5000;
  }
  return score;
}

function selectBestVideoFormat(formats, options = {}) {
  if (!Array.isArray(formats) || !formats.length) {
    return null;
  }
  const scored = formats.map((format) => ({ format, score: scoreVideoFormat(format, options) }));
  scored.sort((a, b) => b.score - a.score);
  return scored[0]?.format ?? null;
}

function selectBestAudioFormat(formats, options = {}) {
  if (!Array.isArray(formats) || !formats.length) {
    return null;
  }
  const scored = formats.map((format) => ({ format, score: scoreAudioFormat(format, options) }));
  scored.sort((a, b) => b.score - a.score);
  return scored[0]?.format ?? null;
}

function extractVideoDetails(format) {
  if (!format) return null;
  return {
    id: format.format_id ?? null,
    ext: format.ext ?? null,
    height: Number.isFinite(format.height) ? format.height : null,
    width: Number.isFinite(format.width) ? format.width : null,
    fps: Number.isFinite(format.fps) ? format.fps : null,
    vcodec: format.vcodec ?? null,
    tbr: Number.isFinite(format.tbr) ? format.tbr : Number.isFinite(format.vbr) ? format.vbr : null
  };
}

function extractAudioDetails(format) {
  if (!format) return null;
  return {
    id: format.format_id ?? null,
    ext: format.ext ?? null,
    acodec: format.acodec ?? null,
    abr: Number.isFinite(format.abr) ? format.abr : Number.isFinite(format.tbr) ? format.tbr : null,
    asr: Number.isFinite(format.asr) ? format.asr : null
  };
}

function buildQualitySummary(videoDetails, audioDetails, targetExtension = null) {
  const parts = [];
  if (videoDetails) {
    const videoParts = [];
    if (videoDetails.height) {
      videoParts.push(`${videoDetails.height}p`);
    }
    if (videoDetails.fps) {
      videoParts.push(`${Math.round(videoDetails.fps)}fps`);
    }
    if (videoDetails.vcodec) {
      videoParts.push(videoDetails.vcodec.split('.')[0].toUpperCase());
    }
    if (videoDetails.ext) {
      videoParts.push(videoDetails.ext.toUpperCase());
    }
    parts.push(videoParts.join(' '));
  }

  if (audioDetails) {
    const audioParts = [];
    if (audioDetails.acodec) {
      audioParts.push(audioDetails.acodec.split('.')[0].toUpperCase());
    }
    if (audioDetails.abr) {
      audioParts.push(`${Math.round(audioDetails.abr)} kbps`);
    }
    if (audioDetails.ext) {
      audioParts.push(audioDetails.ext.toUpperCase());
    }
    parts.push(audioParts.join(' '));
  }

  if (targetExtension && videoDetails && targetExtension.toLowerCase() !== (videoDetails.ext ?? '').toLowerCase()) {
    parts.push(`→ ${targetExtension.toUpperCase()}`);
  }

  if (targetExtension && !videoDetails && audioDetails) {
    const currentExt = audioDetails.ext ? audioDetails.ext.toLowerCase() : null;
    if (currentExt !== targetExtension.toLowerCase()) {
      parts.push(`→ ${targetExtension.toUpperCase()}`);
    }
  }

  return parts.filter(Boolean).join(' • ') || null;
}

function createAudioPlan(info, presetConfig) {
  const formats = Array.isArray(info?.formats) ? info.formats : [];
  const { audioOnly, progressive } = partitionFormats(formats);
  const preferences = presetConfig.audioSelection ?? {};

  let audio = selectBestAudioFormat(audioOnly, preferences);
  if (!audio) {
    audio = selectBestAudioFormat(progressive, preferences);
  }
  if (!audio) {
    throw new Error('No suitable audio format is available for this preset.');
  }

  const audioDetails = extractAudioDetails(audio);
  const targetExtension = presetConfig.targetExtension ?? audioDetails?.ext ?? null;
  const summary = buildQualitySummary(null, audioDetails, targetExtension);

  return {
    formatSelector: audio.format_id,
    mergeOutputFormat: null,
    extraArgs: [...(presetConfig.additionalArgs ?? [])],
    targetExtension,
    resolved: {
      summary,
      video: null,
      audio: audioDetails,
      targetExtension
    }
  };
}

function selectCompanionAudio(video, audioOnlyFormats, progressiveFormats, preferences) {
  if (!video) return null;
  const audioCandidates = audioOnlyFormats.slice();
  if (video.ext) {
    const sharedExt = audioCandidates.filter((format) => (format.ext ?? '').toLowerCase() === video.ext.toLowerCase());
    if (sharedExt.length) {
      const preferred = selectBestAudioFormat(sharedExt, preferences);
      if (preferred) {
        return preferred;
      }
    }
  }

  const preferredAudio = selectBestAudioFormat(audioCandidates, preferences);
  if (preferredAudio) {
    return preferredAudio;
  }

  if (video.acodec && video.acodec !== 'none') {
    return video;
  }

  return selectBestAudioFormat(progressiveFormats, preferences);
}

function createVideoPlan(info, presetConfig) {
  const formats = Array.isArray(info?.formats) ? info.formats : [];
  const { videoOnly, audioOnly, progressive } = partitionFormats(formats);
  const videoPrefs = presetConfig.videoSelection ?? {};
  const audioPrefs = presetConfig.audioSelection ?? {};

  const cappedVideoCandidates = filterVideoByHeight(videoOnly, videoPrefs.maxHeight);
  let video = selectBestVideoFormat(cappedVideoCandidates, videoPrefs);

  let audio = null;
  let usedBestAudioFallback = false;
  let usedGenericSelectorFallback = false;
  if (!video) {
    const progressiveCandidates = filterVideoByHeight(progressive, videoPrefs.maxHeight);
    video = selectBestVideoFormat(progressiveCandidates, videoPrefs);
    if (!video) {
      const progressiveWithAudio = selectBestProgressiveWithAudio(progressive, videoPrefs);
      if (!progressiveWithAudio) {
        throw new Error('No compatible video streams found for this preset.');
      }
      video = progressiveWithAudio;
    }
    if (!video.acodec || video.acodec === 'none') {
      audio = selectCompanionAudio(video, audioOnly, progressive, audioPrefs);
    }
  } else {
    audio = selectCompanionAudio(video, audioOnly, progressive, audioPrefs);
  }

  if (!audio && (!video.acodec || video.acodec === 'none')) {
    const progressiveWithAudio = selectBestProgressiveWithAudio(progressive, videoPrefs);
    if (progressiveWithAudio) {
      video = progressiveWithAudio;
      audio = progressiveWithAudio;
    }
  }

  if (!audio && (!video.acodec || video.acodec === 'none')) {
    audio = {
      format_id: 'bestaudio',
      ext: null,
      acodec: null,
      abr: null,
      asr: null
    };
    usedBestAudioFallback = true;
  }

  const videoDetails = extractVideoDetails(video);
  let audioDetails;
  if (audio && audio !== video) {
    audioDetails = usedBestAudioFallback ? { id: 'bestaudio', ext: null, acodec: 'best', abr: null, asr: null } : extractAudioDetails(audio);
  } else {
    audioDetails = extractAudioDetails(video);
  }

  let formatSelector;
  if (audio && audio !== video) {
    const videoId = video?.format_id ?? 'bestvideo';
    const audioId = audio?.format_id ?? 'bestaudio';
    formatSelector = `${videoId}+${audioId}`;
  } else {
    formatSelector = video.format_id;
  }

  let mergeOutputFormat = presetConfig.mergeOutputFormat ?? null;
  if (!mergeOutputFormat && audio && audio !== video && audio.ext && video.ext && audio.ext.toLowerCase() === video.ext.toLowerCase()) {
    mergeOutputFormat = audio.ext;
  }

  const expectedExtension = mergeOutputFormat ?? video.ext ?? audio?.ext ?? null;
  const summary = buildQualitySummary(videoDetails, audioDetails, expectedExtension);
  const extraArgs = [...(presetConfig.additionalArgs ?? [])];

  if (usedBestAudioFallback && !expectedExtension) {
    usedGenericSelectorFallback = true;
    formatSelector = buildFallbackFormatSelector(presetConfig);
    mergeOutputFormat = presetConfig.mergeOutputFormat ?? null;
  }

  return {
    formatSelector,
    mergeOutputFormat,
    extraArgs,
    targetExtension: expectedExtension,
    resolved: {
      summary,
      video: videoDetails,
      audio: audioDetails,
      targetExtension: expectedExtension,
      hints: {
        usedBestAudioFallback,
        usedGenericSelectorFallback
      }
    }
  };
}

function buildDownloadPlan(info, mode, presetConfig) {
  if (mode === 'audio') {
    return createAudioPlan(info, presetConfig);
  }
  try {
    return createVideoPlan(info, presetConfig);
  } catch (error) {
    if (error?.message && error.message.toLowerCase().includes('no compatible video')) {
      return {
        formatSelector: buildFallbackFormatSelector(presetConfig),
        mergeOutputFormat: presetConfig.mergeOutputFormat ?? null,
        extraArgs: [...(presetConfig.additionalArgs ?? [])],
        targetExtension: presetConfig.mergeOutputFormat ?? null,
        resolved: {
          summary: presetConfig.summary ?? presetConfig.label ?? 'best available video',
          video: null,
          audio: null,
          targetExtension: presetConfig.mergeOutputFormat ?? null,
          hints: {
            usedBestAudioFallback: true,
            usedGenericSelectorFallback: true,
            forcedPresetFallback: true
          }
        }
      };
    }
    throw error;
  }
}
const AUDIO_PRESETS = {
  best: {
    label: 'Best (Original Track)',
    additionalArgs: [],
    summary: 'best-available original audio',
    requiresExtraction: false,
    targetExtension: null,
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['webm', 'm4a', 'mp4', 'ogg'],
      maxAbr: null
    }
  },
  mp3_high: {
    label: 'MP3 • 320 kbps',
    additionalArgs: ['-x', '--audio-format', 'mp3', '--audio-quality', '0'],
    summary: 'MP3 320 kbps (universal)',
    requiresExtraction: true,
    targetExtension: 'mp3',
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['webm', 'm4a', 'mp4', 'ogg'],
      maxAbr: null
    }
  },
  aac_portable: {
    label: 'AAC • 256 kbps',
    additionalArgs: ['-x', '--audio-format', 'aac', '--audio-quality', '2'],
    summary: 'AAC 256 kbps (portable)',
    requiresExtraction: true,
    targetExtension: 'aac',
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['m4a', 'mp4', 'webm'],
      maxAbr: null
    }
  },
  flac_lossless: {
    label: 'FLAC • Lossless',
    additionalArgs: ['-x', '--audio-format', 'flac', '--audio-quality', '0'],
    summary: 'FLAC lossless audio',
    requiresExtraction: true,
    targetExtension: 'flac',
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['webm', 'm4a', 'mp4', 'ogg'],
      maxAbr: null
    }
  }
};

const VIDEO_PRESETS = {
  best_original: {
    label: 'Max Quality (Native Container)',
    additionalArgs: [],
    summary: 'maximum quality direct from YouTube (no container conversion)',
    mergeOutputFormat: null,
    expectsMerge: true,
    videoSelection: {
      maxHeight: null,
      preferCodecs: ['av01', 'vp09', 'vp9', 'vp8', 'hev1', 'h264'],
      preferExts: ['webm', 'mkv', 'mp4']
    },
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['webm', 'm4a', 'mp4']
    }
  },
  best_mp4: {
    label: 'Max Quality MP4 (up to 4K)',
    additionalArgs: [],
    summary: 'maximum quality merged into MP4 container',
    mergeOutputFormat: 'mp4',
    expectsMerge: true,
    videoSelection: {
      maxHeight: null,
      preferCodecs: ['avc1', 'h264'],
      preferExts: ['mp4']
    },
    audioSelection: {
      preferCodecs: ['mp4a', 'aac'],
      preferExts: ['m4a', 'mp4']
    }
  },
  '2160p': {
    label: '4K Cap • 2160p',
    additionalArgs: [],
    summary: 'up to 2160p direct container (VP9/AV1 preferred)',
    mergeOutputFormat: null,
    expectsMerge: true,
    videoSelection: {
      maxHeight: 2160,
      preferCodecs: ['av01', 'vp09', 'vp9', 'vp8', 'hev1', 'h264'],
      preferExts: ['webm', 'mkv', 'mp4']
    },
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['webm', 'm4a', 'mp4']
    }
  },
  '1440p': {
    label: 'QHD • 1440p',
    additionalArgs: [],
    summary: 'up to 1440p direct container (VP9/AV1 preferred)',
    mergeOutputFormat: null,
    expectsMerge: true,
    videoSelection: {
      maxHeight: 1440,
      preferCodecs: ['av01', 'vp09', 'vp9', 'vp8', 'hev1', 'h264'],
      preferExts: ['webm', 'mkv', 'mp4']
    },
    audioSelection: {
      preferCodecs: ['opus', 'vorbis', 'mp4a', 'aac'],
      preferExts: ['webm', 'm4a', 'mp4']
    }
  },
  '1080p_mp4': {
    label: 'Full HD MP4 • 1080p',
    additionalArgs: [],
    summary: '1080p H.264 in MP4 container',
    mergeOutputFormat: 'mp4',
    expectsMerge: true,
    videoSelection: {
      maxHeight: 1080,
      preferCodecs: ['avc1', 'h264'],
      preferExts: ['mp4']
    },
    audioSelection: {
      preferCodecs: ['mp4a', 'aac'],
      preferExts: ['m4a', 'mp4']
    }
  },
  '720p_mp4': {
    label: 'HD MP4 • 720p',
    additionalArgs: [],
    summary: '720p H.264 in MP4 container',
    mergeOutputFormat: 'mp4',
    expectsMerge: true,
    videoSelection: {
      maxHeight: 720,
      preferCodecs: ['avc1', 'h264'],
      preferExts: ['mp4']
    },
    audioSelection: {
      preferCodecs: ['mp4a', 'aac'],
      preferExts: ['m4a', 'mp4']
    }
  }
};

app.use(express.json());
app.use(express.urlencoded({ extended: true }));

app.use(
  session({
    name: 'yt_dlp_session',
    secret: process.env.SESSION_SECRET || 'yt-dlp-secret',
    resave: false,
    saveUninitialized: false,
    cookie: { httpOnly: true, sameSite: 'lax' }
  })
);

// Serve static assets (HTML/CSS/JS) from the project root.
app.use(express.static(__dirname));

const activeJobs = new Map();
let mongoClient;
let usersCollection;
let downloadsCache = new Map();

async function ensureSetup() {
  await fs.mkdir(DATA_DIR, { recursive: true });
  await fs.mkdir(DOWNLOADS_ROOT, { recursive: true });
  await initializeDownloadsStore();
  await connectToMongo();
}

async function initializeDownloadsStore() {
  try {
    const downloadsRaw = await fs.readFile(DOWNLOADS_FILE, 'utf-8');
    const parsed = JSON.parse(downloadsRaw);
    downloadsCache = new Map(Object.entries(parsed));
  } catch (error) {
    if (error?.code !== 'ENOENT') {
      console.warn('Failed to load downloads cache. Rebuilding.', error?.message ?? error);
    }
    downloadsCache = new Map();
    await persistDownloads();
  }
}

async function connectToMongo() {
  if (usersCollection) {
    return;
  }

  const client = new MongoClient(MONGODB_URI, { serverSelectionTimeoutMS: 5000 });
  try {
    await client.connect();
    mongoClient = client;
    const db = mongoClient.db(MONGODB_DB_NAME);
    usersCollection = db.collection('users');
    await usersCollection.createIndex({ username: 1 }, { unique: true });
  } catch (error) {
    await client.close().catch(() => {});
    mongoClient = undefined;
    usersCollection = undefined;
    throw new Error(`Failed to connect to MongoDB: ${error?.message ?? error}`);
  }
}


function hashPassword(password, salt) {
  return crypto.createHash('sha256').update(`${password}:${salt}`).digest('hex');
}

async function persistDownloads() {
  const downloadsObject = Object.fromEntries(downloadsCache);
  await fs.writeFile(DOWNLOADS_FILE, JSON.stringify(downloadsObject, null, 2));
}

function requireAuth(req, res, next) {
  if (!req.session?.user) {
    return res.status(401).json({ status: 'error', message: 'Authentication required.' });
  }
  return next();
}

function getUserDownloads(username) {
  if (!downloadsCache.has(username)) {
    downloadsCache.set(username, []);
  }
  return downloadsCache.get(username);
}

// Relay progress snapshots to every SSE listener subscribed to a job.
function broadcast(jobId, eventName, payload) {
  const job = activeJobs.get(jobId);
  if (!job) return;
  const data = payload ? `data: ${JSON.stringify(payload)}\n\n` : '\n';
  for (const client of job.clients) {
    try {
      client.write(`event: ${eventName}\n${data}`);
    } catch (err) {
      console.error('Failed to write to client', err);
    }
  }
}
function findGeneratedFile(jobId, userDir) {
  return fs
    .readdir(userDir)
    .then((files) => files.find((file) => file.startsWith(`${jobId}__`)))
    .then((name) => (name ? path.join(userDir, name) : null));
}

function resolveContentType(fileName, mode) {
  const ext = path.extname(fileName).slice(1).toLowerCase();
  if (ext && MIME_TYPES[ext]) {
    return MIME_TYPES[ext];
  }
  return mode === 'audio' ? 'audio/mpeg' : 'application/octet-stream';
}

function removeFileQuiet(filePath) {
  if (!filePath) return Promise.resolve();
  return fs.unlink(filePath).catch(() => {});
}

app.post('/api/register', async (req, res) => {
  const { username, password } = req.body;
  if (!username || !password) {
    return res.status(400).json({ status: 'error', message: 'Username and password are required.' });
  }

  if (!usersCollection) {
    return res.status(503).json({ status: 'error', message: 'User store is initializing. Try again shortly.' });
  }

  try {
    const existing = await usersCollection.findOne({ username });
    if (existing) {
      return res.status(409).json({ status: 'error', message: 'Username already exists.' });
    }
  } catch (error) {
    console.error('Failed to check existing user', error);
    return res.status(500).json({ status: 'error', message: 'Could not validate username availability.' });
  }

  const salt = crypto.randomBytes(16).toString('hex');
  const hashed = hashPassword(password, salt);
  const userRecord = {
    username,
    salt,
    passwordHash: hashed,
    createdAt: new Date()
  };

  try {
    await usersCollection.insertOne(userRecord);
  } catch (error) {
    if (error?.code === 11000) {
      return res.status(409).json({ status: 'error', message: 'Username already exists.' });
    }
    console.error('Failed to insert user record', error);
    return res.status(500).json({ status: 'error', message: 'Unable to register user. Please try again.' });
  }

  return res.json({ status: 'success', message: 'User registered successfully.' });
});

app.post('/api/login', async (req, res) => {
  const { username, password } = req.body;
  if (!username || !password) {
    return res.status(400).json({ status: 'error', message: 'Username and password are required.' });
  }

  if (!usersCollection) {
    return res.status(503).json({ status: 'error', message: 'User store is initializing. Try again shortly.' });
  }

  let user;
  try {
    user = await usersCollection.findOne({ username });
  } catch (error) {
    console.error('Failed to query user record', error);
    return res.status(500).json({ status: 'error', message: 'Unable to verify credentials at this time.' });
  }

  if (!user) {
    return res.status(401).json({ status: 'error', message: 'Invalid credentials.' });
  }

  const hashed = hashPassword(password, user.salt);
  if (hashed !== user.passwordHash) {
    return res.status(401).json({ status: 'error', message: 'Invalid credentials.' });
  }

  req.session.user = { username };
  return res.json({ status: 'success', username });
});

app.post('/api/logout', (req, res) => {
  req.session.destroy(() => {
    res.clearCookie('yt_dlp_session');
    res.json({ status: 'success' });
  });
});

app.get('/api/me', (req, res) => {
  if (req.session?.user) {
    return res.json({ isAuthenticated: true, username: req.session.user.username });
  }
  return res.json({ isAuthenticated: false });
});

app.post('/api/info', requireAuth, (req, res) => {
  const { url } = req.body;
  if (!url) {
    return res.status(400).json({ status: 'error', message: 'YouTube URL is required.' });
  }

  const infoProcess = spawn('yt-dlp', ['-J', url]);
  let stdout = '';
  let stderr = '';

  infoProcess.stdout.on('data', (chunk) => {
    stdout += chunk.toString();
  });

  infoProcess.stderr.on('data', (chunk) => {
    stderr += chunk.toString();
  });

  infoProcess.on('error', (error) => {
    console.error('yt-dlp info error', error);
    res.status(500).json({ status: 'error', message: 'Unable to inspect media. Ensure yt-dlp is installed.' });
  });

  infoProcess.on('close', (code) => {
    if (code !== 0) {
      console.error('yt-dlp info failed', stderr);
      return res.status(500).json({ status: 'error', message: 'Failed to analyze URL. Please verify the link.' });
    }

    try {
      const info = JSON.parse(stdout);
      const formats = Array.isArray(info.formats) ? info.formats : [];

      const audioFormats = formats
        .filter((format) => format.vcodec === 'none' && format.acodec && format.acodec !== 'none')
        .map((format) => ({
          id: format.format_id,
          ext: format.ext,
          abr: format.abr ?? null,
          asr: format.asr ?? null,
          filesize: format.filesize ?? format.filesize_approx ?? null,
          label: `${format.abr ? `${Math.round(format.abr)} kbps` : 'Unknown bitrate'} · ${format.ext.toUpperCase()}`
        }))
        .sort((a, b) => (b.abr ?? 0) - (a.abr ?? 0));

      const videoFormats = formats
        .filter((format) => format.vcodec && format.vcodec !== 'none' && format.acodec && format.acodec !== 'none')
        .map((format) => {
          const heightLabel = format.height ? `${format.height}p` : 'Unknown';
          const fpsLabel = format.fps ? `@${format.fps}fps` : '';
          const size = format.filesize ?? format.filesize_approx ?? null;
          const sizeLabel = size ? `${(size / (1024 * 1024)).toFixed(1)} MB` : 'Size n/a';
          return {
            id: format.format_id,
            ext: format.ext,
            height: format.height ?? null,
            fps: format.fps ?? null,
            filesize: size,
            label: `${heightLabel} ${fpsLabel}`.trim() + ` · ${format.ext.toUpperCase()} · ${sizeLabel}`
          };
        })
        .sort((a, b) => (b.height ?? 0) - (a.height ?? 0));

      const bestThumbnail = Array.isArray(info.thumbnails) && info.thumbnails.length
        ? info.thumbnails.reduce((best, thumb) => (!best || (thumb.height ?? 0) > (best.height ?? 0) ? thumb : best), null)
        : null;

      return res.json({
        status: 'success',
        info: {
          id: info.id,
          title: info.title,
          uploader: info.uploader ?? info.channel,
          duration: info.duration,
          viewCount: info.view_count,
          thumbnail: bestThumbnail?.url ?? info.thumbnail ?? null,
          webpageUrl: info.webpage_url ?? url,
          audioFormats,
          videoFormats
        }
      });
    } catch (error) {
      console.error('Failed to parse yt-dlp info JSON', error);
      return res.status(500).json({ status: 'error', message: 'Unexpected response while analyzing media.' });
    }
  });
});

app.get('/api/downloads', requireAuth, (req, res) => {
  const { username } = req.session.user;
  const downloads = getUserDownloads(username);
  return res.json({ status: 'success', downloads: downloads.slice().reverse() });
});

app.get('/api/downloads/:id/meta', requireAuth, (req, res) => {
  const { username } = req.session.user;
  const { id } = req.params;
  const downloads = getUserDownloads(username);
  const record = downloads.find((item) => item.id === id);
  if (!record) {
    return res.status(404).json({ status: 'error', message: 'Download not found.' });
  }

  return res.json({ status: 'success', download: record });
});

app.delete('/api/downloads/:id', requireAuth, async (req, res) => {
  const { username } = req.session.user;
  const { id } = req.params;
  const downloads = getUserDownloads(username);
  const index = downloads.findIndex((item) => item.id === id);
  if (index === -1) {
    return res.status(404).json({ status: 'error', message: 'Download not found.' });
  }

  const [removed] = downloads.splice(index, 1);
  try {
    await fs.unlink(path.join(DOWNLOADS_ROOT, username, removed.fileName));
  } catch (err) {
    console.warn('Failed to delete file', err.message);
  }
  await persistDownloads();
  return res.json({ status: 'success' });
});

app.get('/api/downloads/:id/file', requireAuth, async (req, res) => {
  const { username } = req.session.user;
  const { id } = req.params;
  const downloads = getUserDownloads(username);
  const record = downloads.find((item) => item.id === id);
  if (!record) {
    return res.status(404).json({ status: 'error', message: 'File not found.' });
  }

  const filePath = path.join(DOWNLOADS_ROOT, username, record.fileName);
  return res.download(filePath, record.originalName);
});

app.get('/api/downloads/:id/stream', requireAuth, async (req, res) => {
  const { username } = req.session.user;
  const { id } = req.params;
  const downloads = getUserDownloads(username);
  const record = downloads.find((item) => item.id === id);
  if (!record) {
    return res.status(404).json({ status: 'error', message: 'Media not found.' });
  }

  const filePath = path.join(DOWNLOADS_ROOT, username, record.fileName);

  let stat;
  try {
    stat = await fs.stat(filePath);
  } catch {
    return res.status(404).json({ status: 'error', message: 'File missing on server.' });
  }

  const contentType = resolveContentType(record.fileName, record.mode);
  const range = req.headers.range;
  if (!range) {
    res.setHeader('Content-Type', contentType);
    res.setHeader('Content-Length', stat.size);
    const stream = createReadStream(filePath);
    stream.pipe(res);
    return;
  }

  const bytesPrefix = 'bytes=';
  if (!range.startsWith(bytesPrefix)) {
    res.status(416).end();
    return;
  }

  const rangeParts = range.replace(bytesPrefix, '').split('-');
  const start = Number.parseInt(rangeParts[0], 10);
  const end = rangeParts[1] ? Number.parseInt(rangeParts[1], 10) : stat.size - 1;

  if (Number.isNaN(start) || Number.isNaN(end) || start >= stat.size || end >= stat.size) {
    res.status(416).end();
    return;
  }

  res.status(206);
  res.setHeader('Content-Type', contentType);
  res.setHeader('Content-Length', end - start + 1);
  res.setHeader('Content-Range', `bytes ${start}-${end}/${stat.size}`);
  res.setHeader('Accept-Ranges', 'bytes');
  const stream = createReadStream(filePath, { start, end });
  stream.pipe(res);
});

app.get('/api/downloads/:id/progress', requireAuth, (req, res) => {
  const { id } = req.params;
  res.setHeader('Content-Type', 'text/event-stream');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Connection', 'keep-alive');
  res.flushHeaders?.();
  res.write('retry: 1500\n\n');

  const job = activeJobs.get(id);
  if (!job) {
    // Job already finished; send completion event if record exists.
    const downloads = getUserDownloads(req.session.user.username);
    const record = downloads.find((item) => item.id === id);
    if (record) {
      res.write(`event: done\ndata: ${JSON.stringify(record)}\n\n`);
    } else {
      res.write('event: error\ndata: {"message":"Download not found."}\n\n');
    }
    res.end();
    return;
  }

  job.clients.add(res);
  if (job.lastProgress) {
    res.write(`data: ${JSON.stringify(job.lastProgress)}\n\n`);
  }

  req.on('close', () => {
    job.clients.delete(res);
  });
});

app.post('/api/analyze', requireAuth, async (req, res) => {
  const { url } = req.body;
  if (!url) {
    return res.status(400).json({ status: 'error', message: 'YouTube URL is required.' });
  }

  let mediaInfo;
  try {
    mediaInfo = await inspectMedia(url);
  } catch (error) {
    console.error('yt-dlp inspection failed', error?.stderr ?? error);
    return res.status(502).json({ status: 'error', message: 'Could not inspect the YouTube stream. Try again in a moment.' });
  }

  const formats = Array.isArray(mediaInfo?.formats) ? mediaInfo.formats : [];
  const { videoOnly, audioOnly, progressive } = partitionFormats(formats);

  const audioPresets = [];
  const videoPresets = [];

  // Build audio presets
  const uniqueAudioCodecs = new Set();
  const uniqueAudioExts = new Set();
  for (const format of [...audioOnly, ...progressive]) {
    if (format.acodec && format.acodec !== 'none') {
      uniqueAudioCodecs.add(format.acodec);
    }
    if (format.ext) {
      uniqueAudioExts.add(format.ext);
    }
  }

  if (uniqueAudioCodecs.size > 0) {
    audioPresets.push({
      key: 'best',
      label: 'Best (Original Track)',
      description: 'Original audio track at the highest bitrate YouTube provides.',
      summary: 'best-available original audio'
    });
    audioPresets.push({
      key: 'mp3_high',
      label: 'MP3 • 320 kbps',
      description: 'Extracts audio to MP3 at the highest quality setting for universal playback.',
      summary: 'MP3 320 kbps (universal)'
    });
    audioPresets.push({
      key: 'aac_portable',
      label: 'AAC • 256 kbps',
      description: 'Exports to AAC at roughly 256 kbps for great quality with smaller files.',
      summary: 'AAC 256 kbps (portable)'
    });
    audioPresets.push({
      key: 'flac_lossless',
      label: 'FLAC • Lossless',
      description: 'Preserves audio as FLAC for lossless listening (largest files).',
      summary: 'FLAC lossless audio'
    });
  }

  // Build video presets dynamically based on available resolutions
  const resolutions = new Set();
  const hasVP9 = videoOnly.some((f) => (f.vcodec ?? '').toLowerCase().includes('vp09') || (f.vcodec ?? '').toLowerCase().includes('vp9'));
  const hasAV1 = videoOnly.some((f) => (f.vcodec ?? '').toLowerCase().includes('av01'));
  const hasH264 = videoOnly.some((f) => (f.vcodec ?? '').toLowerCase().includes('avc1') || (f.vcodec ?? '').toLowerCase().includes('h264'));

  for (const format of videoOnly) {
    if (Number.isFinite(format.height)) {
      resolutions.add(format.height);
    }
  }

  const sortedResolutions = Array.from(resolutions).sort((a, b) => b - a);

  if (sortedResolutions.length > 0) {
    const maxRes = sortedResolutions[0];
    if (hasVP9 || hasAV1) {
      videoPresets.push({
        key: 'best_original',
        label: `Max Quality (Native Container) • up to ${maxRes}p`,
        description: `Maximum resolution (${maxRes}p) and bitrate available. Container may be WebM/MKV.`,
        summary: `maximum quality direct from YouTube (no container conversion)`
      });
    }
    if (hasH264) {
      videoPresets.push({
        key: 'best_mp4',
        label: `Max Quality MP4 • up to ${maxRes}p`,
        description: `Best quality (up to ${maxRes}p) while keeping output as MP4 for compatibility.`,
        summary: `maximum quality merged into MP4 container`
      });
    }

    for (const height of sortedResolutions) {
      if (height >= 2160) {
        videoPresets.push({
          key: '2160p',
          label: '4K • 2160p',
          description: 'Cap resolution at 4K (2160p) while keeping source container.',
          summary: 'up to 2160p direct container (VP9/AV1 preferred)'
        });
      } else if (height >= 1440 && !videoPresets.some((p) => p.key === '1440p')) {
        videoPresets.push({
          key: '1440p',
          label: 'QHD • 1440p',
          description: 'Cap resolution at 1440p for high detail with smaller files.',
          summary: 'up to 1440p direct container (VP9/AV1 preferred)'
        });
      } else if (height >= 1080 && !videoPresets.some((p) => p.key === '1080p_mp4')) {
        videoPresets.push({
          key: '1080p_mp4',
          label: 'Full HD MP4 • 1080p',
          description: 'Full HD MP4 output using H.264 for wide device support.',
          summary: '1080p H.264 in MP4 container'
        });
      } else if (height >= 720 && !videoPresets.some((p) => p.key === '720p_mp4')) {
        videoPresets.push({
          key: '720p_mp4',
          label: 'HD MP4 • 720p',
          description: 'HD MP4 output tuned for smaller file sizes.',
          summary: '720p H.264 in MP4 container'
        });
      }
    }
  }

  res.json({
    status: 'success',
    title: mediaInfo?.title ?? 'Unknown',
    audioPresets: audioPresets.length > 0 ? audioPresets : null,
    videoPresets: videoPresets.length > 0 ? videoPresets : null
  });
});

app.post('/api/download', requireAuth, async (req, res) => {
  const { url, mode, audioPreset, videoPreset } = req.body;
  if (!url) {
    return res.status(400).json({ status: 'error', message: 'YouTube URL is required.' });
  }

  const normalizedMode = mode === 'video' ? 'video' : 'audio';
  const audioPresetKey = typeof audioPreset === 'string' && AUDIO_PRESETS[audioPreset] ? audioPreset : 'best';
  const videoPresetKey = typeof videoPreset === 'string' && VIDEO_PRESETS[videoPreset] ? videoPreset : 'best_original';
  const audioConfig = AUDIO_PRESETS[audioPresetKey] ?? AUDIO_PRESETS.best;
  const videoConfig = VIDEO_PRESETS[videoPresetKey] ?? VIDEO_PRESETS.best_original;
  const presetKey = normalizedMode === 'audio' ? audioPresetKey : videoPresetKey;
  const presetConfig = normalizedMode === 'audio' ? audioConfig : videoConfig;
  const presetSummary = presetConfig?.summary ?? (normalizedMode === 'audio' ? 'best-available audio' : 'best-available video');
  const presetLabel = presetConfig?.label ?? presetSummary;
  let mediaInfo;
  try {
    mediaInfo = await inspectMedia(url);
  } catch (error) {
    console.error('yt-dlp inspection failed', error?.stderr ?? error);
    return res.status(502).json({ status: 'error', message: 'Could not inspect the YouTube stream. Try again in a moment.' });
  }

  let downloadPlan;
  try {
    downloadPlan = buildDownloadPlan(mediaInfo, normalizedMode, presetConfig);
  } catch (error) {
    console.error('Failed to build download plan', error);
    return res.status(400).json({ status: 'error', message: error?.message || 'No compatible formats were found for this preset.' });
  }

  const targetSummary = downloadPlan?.resolved?.summary || presetSummary;
  const jobPreset = { key: presetKey, label: presetLabel, summary: presetSummary, mode: normalizedMode, resolvedSummary: targetSummary };
  const jobId = uuid();
  const { username } = req.session.user;
  const userDir = path.join(DOWNLOADS_ROOT, username);
  await fs.mkdir(userDir, { recursive: true });

  const outputTemplate = path.join(userDir, `${jobId}__%(title)s.%(ext)s`);
  const downloadArgs = [
    '--newline',
    '--no-playlist',
    '--ignore-config',
    '--no-check-certificate',
    '--retries',
    '5',
    '--fragment-retries',
    '5',
    '--http-chunk-size',
    '1048576',
    '--geo-bypass',
    '--add-header',
    'User-Agent:Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36',
    '--add-header',
    'Accept-Language:en-US,en;q=0.9',
    '--add-header',
    'Referer:https://www.youtube.com/',
    '-o',
    outputTemplate
  ];

  if (downloadPlan?.formatSelector) {
    downloadArgs.push('-f', downloadPlan.formatSelector);
  }
  if (downloadPlan?.mergeOutputFormat) {
    downloadArgs.push('--merge-output-format', downloadPlan.mergeOutputFormat);
  }
  if (Array.isArray(downloadPlan?.extraArgs) && downloadPlan.extraArgs.length > 0) {
    downloadArgs.push(...downloadPlan.extraArgs);
  }

  downloadArgs.push(url);

  const jobState = {
    status: 'running',
    clients: new Set(),
    lastProgress: {
      phase: 'starting',
      percent: 0,
      message: `Preparing ${targetSummary}...`,
      preset: jobPreset,
      quality: downloadPlan?.resolved || null
    },
    preset: jobPreset,
    plan: downloadPlan
  };
  activeJobs.set(jobId, jobState);

  const pushProgress = (payload) => {
    const nextPayload = {
      ...payload,
      preset: jobState.preset,
      quality: jobState.plan?.resolved || null
    };
    jobState.lastProgress = nextPayload;
    broadcast(jobId, 'progress', nextPayload);
  };

  // Notify client that job accepted with id.
  res.json({
    status: 'started',
    jobId,
    preset: {
      key: presetKey,
      label: presetLabel,
      summary: presetSummary,
      mode: normalizedMode
    },
    quality: downloadPlan?.resolved || null
  });

  let title = mediaInfo?.title ?? 'Download';

  const ytProcess = spawn('yt-dlp', downloadArgs);

  ytProcess.stdout.on('data', (chunk) => {
    const lines = chunk.toString().split(/\r?\n/).filter(Boolean);
    for (const line of lines) {
      if (line.startsWith('[download] Destination:') || line.startsWith('[ExtractAudio] Destination:')) {
        const parts = line.split(':').pop()?.trim();
        if (parts) {
          title = path.basename(parts).replace(/^[^_]*__/, '').replace(/\.[^/.]+$/, '');
        }
      }

      const progressMatch = line.match(/\[download\]\s+([0-9.]+)%\s+of\s+~?([0-9.]+)([KMG]iB)?\s+at\s+([0-9.]+)([KMG]iB\/s)\s+ETA\s+([0-9:]+)/);
      if (progressMatch) {
        const percent = Number(progressMatch[1]);
        const downloadedSize = `${progressMatch[2]}${progressMatch[3] ?? ''}`;
        const speed = `${progressMatch[4]}${progressMatch[5]}`;
        const eta = progressMatch[6];
        const payload = {
          phase: 'downloading',
          percent,
          downloadedSize,
          speed,
          eta,
          message: `Downloading source for ${targetSummary}...`
        };
        pushProgress(payload);
        continue;
      }

      if (line.startsWith('[download] 100%')) {
        const payload = { phase: 'processing', percent: 100, message: `Source downloaded. Preparing ${targetSummary}...` };
        pushProgress(payload);
      }

      if (line.startsWith('[ExtractAudio]')) {
        const payload = { phase: 'processing', percent: 100, message: `Converting to ${targetSummary}...` };
        pushProgress(payload);
      }

      if (line.startsWith('[Merger]')) {
        const payload = { phase: 'processing', percent: 100, message: `Merging streams for ${targetSummary}...` };
        pushProgress(payload);
      }
    }
  });

  ytProcess.stderr.on('data', (chunk) => {
    console.error('yt-dlp stderr:', chunk.toString());
  });

  ytProcess.on('error', (error) => {
    console.error('Failed to start yt-dlp', error);
    broadcast(jobId, 'error', { message: 'Unable to start yt-dlp. Is it installed?' });
    for (const client of jobState.clients) {
      client.end();
    }
    activeJobs.delete(jobId);
  });

  ytProcess.on('close', async (code) => {
    if (code !== 0) {
      broadcast(jobId, 'error', { message: 'Unable to download source with yt-dlp.' });
      for (const client of jobState.clients) {
        client.end();
      }
      activeJobs.delete(jobId);
      return;
    }

    let sourcePath = null;
    try {
      sourcePath = await findGeneratedFile(jobId, userDir);
      if (!sourcePath) {
        throw new Error('Source file missing after download');
      }
      const finalizePayload = { phase: 'finalizing', percent: 100, message: `Finalizing ${targetSummary}...` };
      pushProgress(finalizePayload);

      const fileName = path.basename(sourcePath);
      const originalName = fileName.replace(/^[^_]*__/, '');
      const outputExt = path.extname(fileName).slice(1).toLowerCase();
      const format = outputExt || (normalizedMode === 'audio' ? 'audio' : 'video');
      const record = {
        id: jobId,
        url,
        mode: normalizedMode,
        format,
        createdAt: new Date().toISOString(),
        fileName,
        originalName,
        title,
        preset: {
          key: presetKey,
          label: presetLabel,
          summary: presetSummary,
          resolvedSummary: targetSummary
        },
        quality: jobState.plan?.resolved || null
      };

      const userDownloads = getUserDownloads(username);
      userDownloads.push(record);
      await persistDownloads();

      broadcast(jobId, 'done', record);
      for (const client of jobState.clients) {
        client.end();
      }
    } catch (err) {
      console.error('Post-download error', err);
      await removeFileQuiet(sourcePath);
      const errorMessage = err?.message || 'Failed after download completed.';
      broadcast(jobId, 'error', { message: errorMessage });
      for (const client of jobState.clients) {
        client.end();
      }
    } finally {
      activeJobs.delete(jobId);
    }
  });
});

app.get('/downloads', (req, res) => {
  res.sendFile(path.join(__dirname, 'Downloads.html'));
});

app.get('/player', (req, res) => {
  res.sendFile(path.join(__dirname, 'player.html'));
});

app.get('/login', (req, res) => {
  res.sendFile(path.join(__dirname, 'login.html'));
});

app.get('*', (req, res) => {
  res.sendFile(path.join(__dirname, 'index.html'));
});

const shutdown = async () => {
  if (mongoClient) {
    await mongoClient.close().catch(() => {});
  }
};

process.on('SIGINT', async () => {
  await shutdown();
  process.exit(0);
});

process.on('SIGTERM', async () => {
  await shutdown();
  process.exit(0);
});

ensureSetup()
  .then(() => {
    app.listen(PORT, () => {
      console.log(`Server listening on port ${PORT}`);
    });
  })
  .catch((error) => {
    console.error('Environment setup failed.', error);
    process.exit(1);
  });
