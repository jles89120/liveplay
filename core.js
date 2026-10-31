/* core.js — 純函式：音訊分析與樂理（瀏覽器與 Node 皆可使用） */
(function (root) {
  'use strict';
  const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
  const lerp = (a, b, t) => a + (b - a) * t;
  const smoothstep = (a, b, x) => { const t = clamp((x - a) / (b - a), 0, 1); return t * t * (3 - 2 * t); };
  const NOTE_NAMES = ['C', 'C♯', 'D', 'E♭', 'E', 'F', 'F♯', 'G', 'A♭', 'A', 'B♭', 'B'];
  const freqToMidi = f => 69 + 12 * Math.log2(f / 440);
  const midiToFreq = m => 440 * Math.pow(2, (m - 69) / 12);
  const mod = (n, m) => ((n % m) + m) % m;
  const noteName = m => NOTE_NAMES[mod(Math.round(m), 12)] + (Math.floor(Math.round(m) / 12) - 1);

  function rms(buf) { let s = 0; for (let i = 0; i < buf.length; i++) s += buf[i] * buf[i]; return Math.sqrt(s / buf.length); }

  // mags: 線性幅度陣列（bin i 頻率 = i*sr/fftSize）
  function spectralCentroid(mags, sr, fftSize, minF = 40) {
    let num = 0, den = 0; const binHz = sr / fftSize;
    for (let i = Math.max(1, Math.floor(minF / binHz)); i < mags.length; i++) { num += i * binHz * mags[i]; den += mags[i]; }
    return den > 1e-12 ? num / den : 0;
  }
  function logCompress(mags, out) { out = out || new Float32Array(mags.length); for (let i = 0; i < mags.length; i++) out[i] = Math.log1p(1000 * mags[i]); return out; }
  function spectralFlux(prevLog, curLog) { let f = 0; for (let i = 1; i < curLog.length; i++) { const d = curLog[i] - prevLog[i]; if (d > 0) f += d; } return f / curLog.length; }

  // 自適應門檻的起音偵測
  class OnsetDetector {
    constructor(opts = {}) { this.hist = []; this.size = opts.size || 40; this.k = opts.k || 1.6; this.minGap = opts.minGap || 0.11; this.floor = opts.floor || 0.004; this.last = -1e9; this.prev = 0; }
    push(flux, t) {
      const h = this.hist; let mean = 0, sd = 0;
      if (h.length) { for (const v of h) mean += v; mean /= h.length; for (const v of h) sd += (v - mean) ** 2; sd = Math.sqrt(sd / h.length); }
      const thr = mean + this.k * sd + this.floor;
      const isOnset = h.length >= 8 && flux > thr && flux > this.prev && (t - this.last) >= this.minGap;
      h.push(flux); if (h.length > this.size) h.shift(); this.prev = flux;
      if (isOnset) this.last = t; return isOnset;
    }
  }

  // 由起音時間估計速度（IOI 直方圖，折疊至 60–160 BPM）
  function estimateTempo(onsets, now, opts = {}) {
    const win = opts.window || 10, lo = opts.min || 60, hi = opts.max || 160, sigma = opts.sigma || 2.5;
    const ts = onsets.filter(t => now - t <= win);
    if (ts.length < 4) return { bpm: 0, confidence: 0 };
    const hist = new Float64Array(hi - lo + 1); let total = 0;
    for (let i = 0; i < ts.length; i++) {
      for (let j = i + 1; j < ts.length && j <= i + 4; j++) {
        const dt = ts[j] - ts[i]; if (dt < 0.2 || dt > 3) continue;
        let bpm = 60 / dt; while (bpm < lo) bpm *= 2; while (bpm >= hi + 0.5) bpm /= 2;
        const age = now - ts[j]; const w = Math.exp(-age / win) / (j - i);
        for (let b = Math.max(lo, Math.floor(bpm - 3 * sigma)); b <= Math.min(hi, Math.ceil(bpm + 3 * sigma)); b++) {
          const g = w * Math.exp(-0.5 * ((b - bpm) / sigma) ** 2); hist[b - lo] += g; total += g;
        }
      }
    }
    if (total <= 0) return { bpm: 0, confidence: 0 };
    let best = 0; for (let i = 1; i < hist.length; i++) if (hist[i] > hist[best]) best = i;
    // 拋物線內插
    let off = 0; if (best > 0 && best < hist.length - 1) { const a = hist[best - 1], b = hist[best], c = hist[best + 1]; const d = a - 2 * b + c; if (d !== 0) off = 0.5 * (a - c) / d; }
    return { bpm: lo + best + off, confidence: clamp(hist[best] / total * 8, 0, 1) };
  }

  // YIN 音高偵測
  function yin(buf, sr, opts = {}) {
    const thr = opts.threshold || 0.15, minF = opts.minF || 70, maxF = opts.maxF || 1200;
    const W = Math.floor(buf.length / 2);
    const maxTau = Math.min(W - 1, Math.floor(sr / minF)), minTau = Math.max(2, Math.floor(sr / maxF));
    const d = new Float32Array(maxTau + 2);
    for (let tau = 1; tau <= maxTau + 1 && tau < W; tau++) { let s = 0; for (let i = 0; i < W; i++) { const x = buf[i] - buf[i + tau]; s += x * x; } d[tau] = s; }
    const c = new Float32Array(maxTau + 2); c[0] = 1; let run = 0;
    for (let tau = 1; tau <= maxTau + 1; tau++) { run += d[tau]; c[tau] = run > 0 ? d[tau] * tau / run : 1; }
    let tau = -1;
    for (let t = minTau; t <= maxTau; t++) { if (c[t] < thr) { while (t + 1 <= maxTau && c[t + 1] < c[t]) t++; tau = t; break; } }
    if (tau < 0) return { freq: 0, prob: 0 };
    let bt = tau; if (tau > 1 && tau < maxTau + 1) { const a = c[tau - 1], b = c[tau], e = c[tau + 1]; const den = a - 2 * b + e; if (den !== 0) bt = tau + 0.5 * (a - e) / den; }
    return { freq: sr / bt, prob: clamp(1 - c[tau], 0, 1) };
  }

  // 由頻譜峰值計算 12 音級色度
  function spectrumChroma(mags, sr, fftSize, minF = 80, maxF = 2500) {
    const ch = new Float64Array(12), binHz = sr / fftSize; let sum = 0;
    const i0 = Math.max(2, Math.floor(minF / binHz)), i1 = Math.min(mags.length - 2, Math.ceil(maxF / binHz));
    for (let i = i0; i <= i1; i++) {
      const m = mags[i];
      if (m > mags[i - 1] && m >= mags[i + 1]) {
        const a = mags[i - 1], b = m, c = mags[i + 1]; const den = a - 2 * b + c; const off = den !== 0 ? 0.5 * (a - c) / den : 0;
        const f = (i + off) * binHz; const pc = mod(Math.round(freqToMidi(f)), 12); ch[pc] += m; sum += m;
      }
    }
    if (sum > 0) for (let i = 0; i < 12; i++) ch[i] /= sum;
    return ch;
  }

  // Krumhansl–Schmuckler 調性偵測
  const KS_MAJOR = [6.35, 2.23, 3.48, 2.33, 4.38, 4.09, 2.52, 5.19, 2.39, 3.66, 2.29, 2.88];
  const KS_MINOR = [6.33, 2.68, 3.52, 5.38, 2.60, 3.53, 2.54, 4.75, 3.98, 2.69, 3.34, 3.17];
  function pearson(x, y) { const n = x.length; let mx = 0, my = 0; for (let i = 0; i < n; i++) { mx += x[i]; my += y[i]; } mx /= n; my /= n; let sxy = 0, sxx = 0, syy = 0; for (let i = 0; i < n; i++) { const a = x[i] - mx, b = y[i] - my; sxy += a * b; sxx += a * a; syy += b * b; } return sxx > 0 && syy > 0 ? sxy / Math.sqrt(sxx * syy) : 0; }
  function detectKey(chroma) {
    const res = [];
    for (let t = 0; t < 12; t++) {
      const rot = new Array(12); for (let i = 0; i < 12; i++) rot[i] = chroma[mod(i + t, 12)];
      res.push({ tonic: t, mode: 'major', corr: pearson(rot, KS_MAJOR) });
      res.push({ tonic: t, mode: 'minor', corr: pearson(rot, KS_MINOR) });
    }
    res.sort((a, b) => b.corr - a.corr);
    return { tonic: res[0].tonic, mode: res[0].mode, corr: res[0].corr, confidence: res[0].corr - res[1].corr, ranking: res };
  }
  const keyName = (tonic, mode) => NOTE_NAMES[tonic] + (mode === 'major' ? ' 大調' : ' 小調');

  // 音階與和弦
  const SCALES = { major: [0, 2, 4, 5, 7, 9, 11], minor: [0, 2, 3, 5, 7, 8, 10] };
  function inScale(midi, root, mode) { return SCALES[mode].includes(mod(Math.round(midi) - root, 12)); }
  function quantizeToScale(midi, root, mode) {
    const m = Math.round(midi); if (inScale(m, root, mode)) return m;
    for (let d = 1; d < 12; d++) { const up = m + d, dn = m - d; const fu = inScale(up, root, mode), fd = inScale(dn, root, mode);
      if (fu && fd) return (midi - m) >= 0 ? up : dn; if (fu) return up; if (fd) return dn; }
    return m;
  }
  // 絕對音階度數（0 = 位於 MIDI 60 附近八度的主音）
  function degreeToMidi(deg, root, mode, baseMidi = 60) {
    const sc = SCALES[mode]; const o = Math.floor(deg / 7); const i = mod(deg, 7);
    const tonicBase = baseMidi - mod(baseMidi - root, 12); // 不高於 baseMidi 的主音
    return tonicBase + 12 * o + sc[i];
  }
  function midiToDegree(midi, root, mode, baseMidi = 60) {
    const q = quantizeToScale(midi, root, mode); const sc = SCALES[mode];
    const tonicBase = baseMidi - mod(baseMidi - root, 12); const rel = q - tonicBase;
    const o = Math.floor(rel / 12); const i = sc.indexOf(mod(rel, 12)); return o * 7 + i;
  }
  function diatonicChord(root, mode, degree, size = 3) {
    const sc = SCALES[mode]; const pcs = [];
    for (let k = 0; k < size; k++) { const d = degree + 2 * k; pcs.push(mod(root + sc[mod(d, 7)], 12)); }
    return pcs; // 第一個為和弦根音
  }
  // 接近 center 的緊密配置（自然形成平滑聲部進行）
  function voiceChord(pcs, center) {
    const notes = pcs.map(pc => { let m = center - 6 + mod(pc - (center - 6), 12); return m; });
    return notes.sort((a, b) => a - b);
  }
  const PROGRESSIONS = {
    major: [[0, 4, 5, 3], [0, 5, 3, 4], [1, 4, 0, 5], [0, 3, 5, 4], [3, 4, 2, 5], [0, 2, 3, 4]],
    minor: [[0, 5, 2, 6], [0, 3, 6, 2], [0, 6, 5, 6], [0, 3, 4, 0], [5, 6, 0, 0], [0, 5, 3, 4]]
  };
  function motifToIntervals(midis, root, mode) { // 以音階度數差表示動機
    const degs = midis.map(m => midiToDegree(m, root, mode)); const out = [];
    for (let i = 1; i < degs.length; i++) out.push(clamp(degs[i] - degs[i - 1], -5, 5));
    return out;
  }


  // ================= v2：流行樂理（純函式，可測試） =================
  function rng32(seed) { let a = (seed >>> 0) || 1; return function () { a = (a + 0x6D2B79F5) | 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }
  const pick = (rng, arr) => arr[Math.floor(rng() * arr.length) % arr.length];
  // 五聲音階（以七聲音階度數表示）：大調 1 2 3 5 6；小調 1 ♭3 4 5 ♭7
  const PENTA = { major: [0, 1, 2, 4, 5], minor: [0, 2, 3, 4, 6] };
  function chordToneDegs(chordDeg, size = 3) { const out = []; for (let k = 0; k < size; k++) out.push(mod(chordDeg + 2 * k, 7)); return out; }
  // 將度數吸附到 allowed（mod 7 集合）中最近者；dir 決定平手時的方向
  function snapDeg(deg, allowed, dir = 0) {
    if (!allowed || !allowed.length || allowed.includes(mod(deg, 7))) return deg;
    for (let d = 1; d < 7; d++) { const up = allowed.includes(mod(deg + d, 7)), dn = allowed.includes(mod(deg - d, 7));
      if (up && dn) return dir >= 0 ? deg + d : deg - d; if (up) return deg + d; if (dn) return deg - d; }
    return deg;
  }
  const intersect = (a, b) => a.filter(x => b.includes(x));

  // 一小節（16 個十六分音符）的節奏型：[起始步, 長度]
  const RHYTHMS = {
    ballad8a: [[0, 2], [2, 2], [4, 2], [6, 2], [8, 4], [12, 4]],
    ballad8b: [[2, 2], [4, 2], [6, 2], [8, 2], [10, 6]],
    ballad8c: [[0, 3], [3, 1], [4, 2], [6, 2], [8, 8]],
    pickup: [[4, 2], [6, 2], [8, 2], [10, 2], [12, 4]],
    story: [[0, 2], [2, 2], [4, 2], [6, 1], [7, 1], [8, 2], [10, 2], [12, 4]],
    long: [[0, 6], [6, 2], [8, 8]],
    long2: [[0, 10], [10, 2], [12, 4]],
    rnb16a: [[0, 1], [1, 1], [2, 2], [4, 1], [5, 1], [6, 1], [7, 1], [8, 1], [9, 1], [10, 2], [12, 1], [13, 3]],
    rnb16b: [[2, 1], [3, 1], [4, 1], [5, 1], [6, 2], [8, 1], [9, 1], [10, 1], [11, 2], [13, 3]],
    rnb16c: [[1, 1], [2, 1], [3, 2], [5, 1], [6, 1], [7, 2], [9, 1], [10, 1], [11, 1], [12, 4]],
    sync8: [[0, 2], [3, 2], [6, 2], [8, 2], [10, 3], [14, 2]],
    sync8b: [[0, 3], [3, 3], [6, 2], [8, 4], [12, 2], [14, 2]],
    kpopA: [[0, 1], [1, 1], [2, 2], [4, 2], [6, 1], [7, 3], [10, 2], [12, 2], [14, 2]],
    kpopB: [[0, 2], [2, 1], [3, 1], [4, 2], [6, 2], [8, 1], [9, 1], [10, 2], [12, 4]],
    anthemA: [[0, 4], [4, 2], [6, 2], [8, 6], [14, 2]],
    anthemB: [[0, 2], [2, 2], [4, 4], [8, 2], [10, 2], [12, 4]],
    rise8: [[0, 2], [2, 2], [4, 2], [6, 2], [8, 2], [10, 2], [12, 2], [14, 2]],
    rise16: [[0, 2], [2, 1], [3, 1], [4, 2], [6, 1], [7, 1], [8, 2], [10, 1], [11, 1], [12, 2], [14, 2]]
  };
  // 句尾小節：保留前半拍點，最後一個長音（像歌手拉長音）
  function endingBar(r, rng) {
    const longAt = rng() < 0.5 ? 8 : 6, out = [];
    for (const [s, l] of r) if (s < longAt) out.push([s, Math.min(l, longAt - s)]);
    out.push([longAt, (rng() < 0.6 ? 16 : 14) - longAt]);
    return out;
  }

  // 曲風（只取曲風特徵，不使用任何既有旋律）
  // feat = [強度, 亮度, 起音密度] 的中心點；prog 為音階度數（0 = I / i）
  const STYLES = {
    rnb: { label: 'R&B 流行', desc: 'R&B・中國風・切分鋼琴', color: '#a78bfa', feat: [0.42, 0.42, 0.55], minorBias: 1.35, bpm: [70, 96], penta: 0.8, seventh: 0.55, add9: 0.4, swing: 0.12,
      prog: { major: [[0, 5, 3, 4], [3, 4, 2, 5], [0, 4, 5, 2, 3, 0, 3, 4], [3, 4, 0, 5]], minor: [[0, 5, 2, 6], [0, 3, 6, 2], [5, 6, 4, 0], [0, 6, 5, 6]] },
      rhythm: { verse: ['rnb16a', 'rnb16b', 'rnb16c'], pre: ['rise16', 'sync8'], chorus: ['sync8', 'rnb16c', 'sync8b'], bridge: ['long', 'ballad8b'] }, reg: [0, 3], repeat: 0.18 },
    folk: { label: '民謠敘事', desc: '民謠流行・木吉他敘事', color: '#fbbf24', feat: [0.14, 0.32, 0.15], minorBias: 1.1, bpm: [64, 84], penta: 0.6, seventh: 0.15, add9: 0.2, swing: 0.03,
      prog: { major: [[0, 4, 5, 2, 3, 0, 3, 4], [0, 4, 5, 3], [0, 5, 3, 4], [3, 4, 0, 5]], minor: [[0, 5, 2, 6], [0, 3, 6, 2], [5, 6, 0, 0]] },
      rhythm: { verse: ['story', 'ballad8a', 'pickup'], pre: ['ballad8b', 'rise8'], chorus: ['ballad8c', 'ballad8a', 'long'], bridge: ['long', 'long2'] }, reg: [0, 2], repeat: 0.3 },
    power: { label: '力量情歌', desc: '抒情爆發・高音副歌', color: '#f472b6', feat: [0.7, 0.62, 0.35], minorBias: 1.15, bpm: [70, 92], penta: 0.2, seventh: 0.15, add9: 0.3, swing: 0,
      prog: { major: [[5, 3, 0, 4], [3, 4, 2, 5], [0, 4, 5, 3]], minor: [[0, 5, 2, 6], [5, 6, 0, 0], [0, 3, 5, 6]] },
      rhythm: { verse: ['ballad8a', 'pickup', 'sync8'], pre: ['rise8', 'rise16'], chorus: ['anthemA', 'anthemB', 'long'], bridge: ['long', 'long2'] }, reg: [0, 5], repeat: 0.15 },
    lyric: { label: '抒情鋼琴', desc: '鋼琴抒情・內斂到爆發', color: '#67e8f9', feat: [0.22, 0.62, 0.22], minorBias: 1.1, bpm: [62, 82], penta: 0.3, seventh: 0.45, add9: 0.5, swing: 0,
      prog: { major: [[3, 4, 2, 5], [1, 4, 0, 5], [0, 4, 5, 2, 3, 0, 1, 4], [0, 4, 5, 3]], minor: [[0, 5, 2, 6], [5, 6, 2, 5], [0, 3, 6, 2]] },
      rhythm: { verse: ['ballad8b', 'pickup', 'ballad8c'], pre: ['ballad8a', 'rise8'], chorus: ['long', 'anthemA', 'ballad8c'], bridge: ['long2', 'long'] }, reg: [0, 4], repeat: 0.2 },
    us: { label: '美式流行', desc: '四和弦循環・流行搖滾', color: '#ff7a59', feat: [0.68, 0.48, 0.7], minorBias: 0.85, bpm: [96, 124], penta: 0.25, seventh: 0.05, add9: 0.1, swing: 0.02,
      prog: { major: [[0, 4, 5, 3], [5, 3, 0, 4], [0, 3, 5, 4]], minor: [[0, 5, 2, 6], [5, 2, 6, 0], [0, 6, 5, 6]] },
      rhythm: { verse: ['sync8', 'ballad8a', 'kpopB'], pre: ['rise8'], chorus: ['sync8b', 'anthemB', 'sync8'], bridge: ['long', 'ballad8b'] }, reg: [0, 3], repeat: 0.25 },
    kpop: { label: '韓式流行', desc: '舞曲節拍・洗腦 Hook', color: '#4ade80', feat: [0.82, 0.78, 0.88], minorBias: 0.95, bpm: [104, 128], penta: 0.2, seventh: 0.35, add9: 0.2, swing: 0.04,
      prog: { major: [[5, 3, 0, 4], [3, 4, 2, 5], [1, 4, 0, 5]], minor: [[0, 5, 2, 6], [5, 6, 0, 0], [0, 3, 6, 2]] },
      rhythm: { verse: ['kpopB', 'rnb16b', 'sync8'], pre: ['rise16', 'rise8'], chorus: ['kpopA', 'kpopB'], bridge: ['long', 'ballad8b'] }, reg: [0, 4], repeat: 0.3 }
  };
  const STYLE_IDS = Object.keys(STYLES);
  // 由麥克風特徵（強度、亮度、起音密度 0–1）計算各風格權重（總和 1）
  function styleWeights(intensity, brightness, density, mode) {
    const w = {}; let tot = 0;
    for (const id of STYLE_IDS) { const st = STYLES[id], f = st.feat;
      const d2 = 1.4 * (intensity - f[0]) ** 2 + 0.8 * (brightness - f[1]) ** 2 + 0.9 * (density - f[2]) ** 2;
      let v = Math.exp(-d2 / (2 * 0.17 * 0.17)) + 1e-4; if (mode === 'minor') v *= st.minorBias; else v *= 2 - st.minorBias;
      w[id] = v; tot += v; }
    for (const id of STYLE_IDS) w[id] /= tot; return w;
  }
  const SONG_FORM = [
    { type: 'intro', bars: 4 }, { type: 'verse', bars: 8 }, { type: 'pre', bars: 4 }, { type: 'chorus', bars: 8 }, { type: 'inter', bars: 4 },
    { type: 'verse', bars: 8 }, { type: 'pre', bars: 4 }, { type: 'chorus', bars: 8 }, { type: 'bridge', bars: 8 }, { type: 'chorus', bars: 8, final: true }, { type: 'outro', bars: 4 }];
  const SECTION_LABEL = { intro: '前奏', verse: '主歌', pre: '導歌', chorus: '副歌', inter: '間奏', bridge: '橋段', outro: '尾奏' };
  const SECTION_LEVEL = { intro: 0.35, verse: 0.45, pre: 0.62, chorus: 0.92, inter: 0.5, bridge: 0.58, outro: 0.3 };
  const PRE_PROG = { major: [[3, 4, 3, 4], [1, 2, 3, 4], [3, 4, 2, 5], [5, 3, 1, 4], [1, 3, 4, 4]], minor: [[5, 6, 5, 6], [3, 4, 5, 6], [3, 6, 2, 5], [5, 3, 6, 4]] };
  // v4：指定低音線（斜線和弦，級進下行／上行）：以「調式:進行」為鍵，值為各小節低音的音階度數
  const BASS_HINTS = { 'major:0,4,5,0,3,0,1,4': [0, 6, 5, 4, 3, 2, 1, 4], 'major:0,4,5,2,3,0,3,4': [0, 6, 5, 4, 3, 2, 3, 4], 'major:0,4,5,2,3,0,1,4': [0, 6, 5, 4, 3, 2, 1, 4], 'major:0,1,0,3': [0, 1, 2, 3], 'minor:0,4,5,2': [0, 6, 5, 4] };
  const BRIDGE_PROG = { major: [[5, 2, 3, 4], [3, 2, 1, 4], [5, 3, 1, 4], [5, 4, 3, 4], [3, 5, 1, 4]], minor: [[3, 6, 2, 5], [5, 6, 3, 4], [2, 6, 3, 4], [5, 2, 3, 4]] };

  // 產生一句旋律：rhythm = [[bar, step, len]]；回傳 [{bar, step, len, deg}]
  function buildPhrase(rng, o) {
    const n = o.rhythm.length, out = []; const pen = o.penta || null; const rep = o.repeat == null ? 0.15 : o.repeat;
    let deg = o.start != null ? o.start : snapDeg(o.center + pick(rng, [-2, -1, 0, 1]), o.chordAt(o.rhythm[0][0]));
    const peak = o.leap && n >= 4 ? Math.floor(n * (0.35 + rng() * 0.25)) : -1; let prevMv = 0;
    for (let i = 0; i < n; i++) {
      const [bar, step, len] = o.rhythm[i]; const tones = o.chordAt(bar); let mv = 0;
      if (o.prefix && i < o.prefix.length) { deg = o.prefix[i]; mv = i ? o.prefix[i] - o.prefix[i - 1] : 0; }
      else if (i > 0) {
        const mi = o.prefix ? i - o.prefix.length : i - 1;
        if (o.motif && o.motif.length && mi < o.motif.length * 2) mv = o.motif[mi % o.motif.length];
        else if (i === peak) mv = pick(rng, [2, 3, 3, 4]);                  // 樂句高點：大跳
        else if (peak >= 0 && i > peak) mv = rng() < rep ? 0 : (rng() < 0.75 ? -1 : (rng() < 0.5 ? 1 : -2)); // 大跳後級進回落
        else { const up = i / n < 0.5 ? 0.62 : 0.4; mv = rng() < rep ? 0 : (rng() < 0.82 ? (rng() < up ? 1 : -1) : (rng() < up ? 2 : -2)); }
        if (Math.abs(prevMv) >= 3 && Math.abs(mv) >= 2 && Math.sign(mv) === Math.sign(prevMv)) mv = -Math.sign(prevMv); // 大跳後反向
        deg += mv;
      }
      const locked = !!o.lock && i < o.lock && i < n - 1; // v3：鎖定的靈感音（保持原音高，不吸附）
      if (!locked) { while (deg > o.hi) deg -= 2; while (deg < o.lo) deg += 2; }
      const strong = step % 8 === 0 || len >= 4, last = i === n - 1;
      if (locked) { /* keep */ }
      else if (last) {
        let allowed = o.ending === 'tonic' ? (tones.includes(0) ? [0] : [tones[0]]) : o.ending === 'close' ? [tones[0], tones[1]] : tones.slice(1);
        deg = snapDeg(deg, allowed, -1);
      } else if (strong) { const a = pen ? intersect(tones, pen) : tones; deg = snapDeg(deg, a.length ? a : tones, mv); }
      else if (pen) deg = snapDeg(deg, pen, mv);
      if (!locked) { while (deg > o.hi + 1) deg -= 7; while (deg < o.lo - 1) deg += 7; }
      prevMv = mv; out.push({ bar, step, len, deg, alt: locked && o.alts ? (o.alts[i] || 0) : 0, vel: strong ? 1 : len >= 2 ? 0.86 : 0.74, hook: locked || undefined });
    }
    return out;
  }
  // 產生一整段旋律（含呼應、重複的 Hook）
  // o: { bars, rhythms:[名稱], chordDegAt(bar), size, center, span, penta:[...]|null, motif, hook, repeat, final }
  function buildSectionMelody(rng, o) {
    const bars = o.bars, span = o.span || 5, lo = o.center - span, hi = o.center + span;
    const chordAt = b => chordToneDegs(o.chordDegAt(b), 3);
    const rA = RHYTHMS[pick(rng, o.rhythms)] || RHYTHMS.ballad8a;
    const rB = o.rhythms.length > 1 && rng() < 0.4 ? RHYTHMS[pick(rng, o.rhythms)] : rA;
    const mk = (r, off) => r.map(([s, l]) => [off, s, l]);
    const callR = mk(rA, 0).concat(mk(endingBar(rA, rng), 1));
    const respR = mk(rB, 0).concat(mk(endingBar(rB, rng), 1));
    const notes = []; const nP = Math.max(1, Math.floor(bars / 2)); let call = null;
    for (let p = 0; p < nP; p++) {
      const off = p * 2, ca = b => chordAt(b + off), isLast = p === nP - 1;
      let ph;
      const base = { chordAt: ca, center: o.center, lo, hi, penta: o.penta, repeat: o.repeat };
      if (p % 2 === 0) {
        if (call && (o.hook || rng() < 0.6)) {           // 重複 Hook（強拍重新對齊和弦）
          ph = buildPhrase(rng, Object.assign({}, base, { rhythm: callR, prefix: call.map(n => n.deg).slice(0, -1), ending: isLast ? 'tonic' : 'open' }));
        } else {
          ph = buildPhrase(rng, Object.assign({}, base, { rhythm: callR, motif: o.motif, leap: true, ending: isLast ? 'tonic' : 'open' }));
          if (!call) call = ph;
        }
      } else {                                             // 回應句：開頭模仿問句，結尾解決
        const k = Math.min(call.length, respR.length) >> 1;
        ph = buildPhrase(rng, Object.assign({}, base, { rhythm: respR, prefix: call.slice(0, k).map(n => n.deg), leap: p === 1 && !!o.hook, ending: isLast || p % 4 === 3 ? 'tonic' : 'close' }));
      }
      for (const n of ph) notes.push(Object.assign(n, { bar: n.bar + off }));
    }
    return notes;
  }
  function chordName(root, mode, deg, size = 3) {
    const pcs = diatonicChord(root, mode, deg, 3); const third = mod(pcs[1] - pcs[0], 12), fifth = mod(pcs[2] - pcs[0], 12);
    let q = third === 3 ? (fifth === 6 ? 'dim' : 'm') : ''; if (size >= 4) q += (q === 'm' ? '7' : (mod(diatonicChord(root, mode, deg, 4)[3] - pcs[0], 12) === 11 ? 'maj7' : '7'));
    return NOTE_NAMES[pcs[0]] + q;
  }


  // ================= v3：靈感音擷取（Seed）=================
  const median = a => { if (!a.length) return 0; const s = a.slice().sort((x, y) => x - y), h = s.length >> 1; return s.length % 2 ? s[h] : (s[h - 1] + s[h]) / 2; };
  const pcName = m => NOTE_NAMES[mod(Math.round(m), 12)];
  // 頻譜峰值（拋物線內插）：回傳 [{f, mag}]，依強度排序
  function spectralPeaks(mags, sr, fftSize, n = 6, minF = 90, maxF = 2000) {
    const binHz = sr / fftSize, i0 = Math.max(2, Math.floor(minF / binHz)), i1 = Math.min(mags.length - 3, Math.ceil(maxF / binHz));
    let mx = 0; for (let i = i0; i <= i1; i++) if (mags[i] > mx) mx = mags[i];
    const out = []; if (mx <= 1e-9) return out;
    for (let i = i0; i <= i1; i++) {
      const m = mags[i];
      if (m > mx * 0.12 && m > mags[i - 1] && m >= mags[i + 1] && m > mags[i - 2] && m >= mags[i + 2]) {
        const a = mags[i - 1], c = mags[i + 1], den = a - 2 * m + c, off = den !== 0 ? 0.5 * (a - c) / den : 0;
        let loc = 0, nl = 0; for (let j = Math.max(1, i - 10); j <= Math.min(mags.length - 1, i + 10); j++) if (Math.abs(j - i) > 2) { loc += mags[j]; nl++; }
        out.push({ f: (i + off) * binHz, mag: m, prom: m / (loc / Math.max(1, nl) + 1e-12) }); // prom：相對周圍頻帶的突出程度（音調性）
      }
    }
    out.sort((a, b) => b.mag - a.mag); return out.length > n ? out.slice(0, n) : out;
  }
  // 音高軌跡 → 音符（穩定的音高片段）
  class NoteTracker {
    constructor(o = {}) { this.minDur = o.minDur || 0.08; this.gap = o.gap || 0.07; this.tol = o.tol || 0.55; this.cur = null; this.prevT = null; this.dt = 0.025; }
    _end() {
      const k = this.cur; this.cur = null; if (!k) return null;
      const n = k.vals.length, dur = k.last - k.start + this.dt; if (dur < this.minDur || n < 3) return null;
      const md = median(k.vals); let sd = 0; for (const v of k.vals) sd += (v - md) ** 2; sd = Math.sqrt(sd / n);
      let w = 0; for (const x of k.w) w += x;
      return { m: Math.round(md), t: k.start, dur, sal: w / n, stab: clamp(1 - sd / 0.35, 0, 1) };
    }
    push(t, midi, prob = 1, level = 0.05, onset = false) {
      if (this.prevT != null) { const d = t - this.prevT; if (d > 0 && d < 0.2) this.dt += (d - this.dt) * 0.1; } this.prevT = t;
      const has = midi != null && isFinite(midi) && midi > 20; let ended = null; const c = this.cur;
      if (c && (!has ? t - c.last > this.gap : (Math.abs(midi - c.ref) > this.tol || (onset && t - c.start > 0.12)))) ended = this._end();
      if (has) {
        if (!this.cur) this.cur = { start: t, last: t, vals: [midi], w: [prob * level], ref: midi };
        else { const k = this.cur; k.vals.push(midi); k.w.push(prob * level); k.last = t; k.ref += (midi - k.ref) / Math.min(k.vals.length, 6); }
      }
      return ended;
    }
    flush() { return this._end(); }
  }
  const LENS = [1, 2, 3, 4, 6, 8];
  const snapLen = x => LENS.reduce((p, c) => Math.abs(c - x) < Math.abs(p - x) ? c : p, 2);
  // 起音間隔（秒）→ 十六分音符長度（相對節奏）
  function rhythmFromIOIs(iois, lastDur) {
    if (!iois.length) return [4];
    const med = median(iois) || 0.4, base = med < 0.55 ? 2 : 4;
    const out = iois.map(x => snapLen(x / med * base));
    out.push(clamp(snapLen((lastDur || med) / med * base), 4, 8));
    return out;
  }
  const NAMES_SHARP = ['C', 'C♯', 'D', 'D♯', 'E', 'F', 'F♯', 'G', 'G♯', 'A', 'A♯', 'B'], NAMES_FLAT = ['C', 'D♭', 'D', 'E♭', 'E', 'F', 'G♭', 'G', 'A♭', 'A', 'B♭', 'B'];
  // 依調號拼寫音名（E 大調寫 G♯、不寫 A♭）
  function spellPc(pc, key) {
    if (!key) return NOTE_NAMES[mod(pc, 12)];
    const r = mod(key.mode === 'minor' ? key.tonic + 3 : key.tonic, 12);
    return ([7, 2, 9, 4, 11, 6].includes(r) ? NAMES_SHARP : [5, 10, 3, 8, 1].includes(r) ? NAMES_FLAT : NOTE_NAMES)[mod(pc, 12)];
  }
  function makeSeed(notes, source, score, extra) {
    const s = Object.assign({ notes, source, score, midis: notes.map(n => n.m), pcs: notes.map(n => mod(n.m, 12)) }, extra || {});
    const k = fitKeys(s.midis, notes.map(n => n.len))[0];
    s.names = notes.map(n => spellPc(n.m, k)); s.label = s.names.join(' – '); return s;
  }
  function mergeNotes(notes) {
    const out = [];
    for (const n of notes.slice().sort((a, b) => a.t - b.t)) {
      const p = out[out.length - 1];
      if (p && p.m === n.m && n.t - (p.t + p.dur) < 0.12) { const tot = p.dur + n.dur; p.sal = (p.sal * p.dur + n.sal * n.dur) / tot; p.stab = Math.min(p.stab, n.stab); p.dur = n.t + n.dur - p.t; }
      else out.push(Object.assign({}, n));
    }
    return out;
  }
  const CONSONANT = [1, 2, 3, 4, 5, 7];
  // 由偵測到的音符挑出最顯著、最穩定的 3–5 個音（保留先後順序、節奏與輪廓）
  function extractSeed(notes, o = {}) {
    const now = o.now != null ? o.now : null;
    const ns = mergeNotes(notes).filter(n => n.dur >= 0.08 && n.m >= 36 && n.m <= 96);
    if (ns.length < 3) return null;
    let maxSal = 1e-9; for (const n of ns) maxSal = Math.max(maxSal, n.sal);
    const q = ns.map(n => (0.35 + 0.65 * n.sal / maxSal) * (0.4 + 0.6 * n.stab) * Math.min(1, n.dur / 0.25));
    let best = null;
    for (let i = 0; i < ns.length; i++) for (let k = 3; k <= 5 && i + k <= ns.length; k++) {
      const w = ns.slice(i, i + k); let okw = true, cons = 0;
      for (let j = 1; j < k; j++) {
        const gap = w[j].t - (w[j - 1].t + w[j - 1].dur), iv = Math.abs(w[j].m - w[j - 1].m);
        if (gap > 1.0 || iv > 9) { okw = false; break; } if (CONSONANT.includes(iv)) cons++;
      }
      if (!okw) continue;
      if (new Set(w.map(n => mod(n.m, 12))).size < 3) continue;
      let lo = 999, hi = 0; for (const n of w) { lo = Math.min(lo, n.m); hi = Math.max(hi, n.m); } if (hi - lo > 14) continue;
      const end = w[k - 1].t + w[k - 1].dur; if (end - w[0].t > 5) continue;
      let qs = 0; for (let j = 0; j < k; j++) qs += q[i + j]; qs /= k;
      const sc = qs * (k === 3 ? 1.12 : k === 4 ? 1.04 : 1) + 0.08 * cons / (k - 1) + (now != null ? 0.12 * Math.exp(-Math.max(0, now - end) / 6) : 0);
      if (!best || sc > best.score) best = { i, k, score: sc, end };
    }
    if (!best) return null;
    const w = ns.slice(best.i, best.i + best.k), iois = [];
    for (let j = 1; j < w.length; j++) iois.push(w[j].t - w[j - 1].t);
    const lens = rhythmFromIOIs(iois, w[w.length - 1].dur);
    return makeSeed(w.map((n, j) => ({ m: n.m, len: lens[j] })), 'pitch', best.score, { startT: w[0].t, endT: best.end });
  }
  function rhythmFromOnsets(onsets, now) {
    const rec = onsets.filter(t => now - t < 6), iois = [];
    for (let i = 1; i < rec.length; i++) { const d = rec[i] - rec[i - 1]; if (d > 0.08 && d < 1.5) iois.push(d); }
    if (iois.length < 2) return [2, 2, 4];
    const last = iois.slice(-2), r = rhythmFromIOIs(last, median(iois) * 2);
    return r.length >= 3 ? r.slice(-3) : [2, 2, 4];
  }
  const SILENT_SHAPES = [[0, 4, 7], [0, 2, 4], [7, 9, 12], [4, 2, 0], [0, 7, 4], [2, 4, 7], [9, 7, 4], [0, 5, 4], [4, 7, 9], [7, 4, 0]];
  // 沒有音高（純噪音）：由長時間累積的頻譜峰值／重心推導 3 個音；節奏取自起音
  function seedFromNoise(hist, histTW, onsets, now, rng) {
    rng = rng || Math.random;
    let tot = 0, cm = 0; for (let m = 0; m < hist.length; m++) { tot += hist[m]; cm += m * hist[m]; }
    const lens = rhythmFromOnsets(onsets || [], now);
    if (tot < 1e-6) {
      const sh = pick(rng, SILENT_SHAPES), base = 60 + pick(rng, [0, 2, 5, 7, -3, -5]);
      return makeSeed(sh.map((iv, j) => ({ m: base + iv, len: lens[j] || 4 })), 'silence', 0.05);
    }
    cm /= tot; const peaks = [];
    for (let m = 37; m < Math.min(hist.length - 1, 100); m++) if (hist[m] > 0 && hist[m] >= hist[m - 1] && hist[m] >= hist[m + 1]) peaks.push(m);
    peaks.sort((a, b) => hist[b] - hist[a]);
    const chosen = [];
    // 先挑彼此協和的峰（避開小二度、三全音），不夠再放寬
    for (const strict of [true, false]) for (const m of peaks) {
      if (chosen.length >= 3 || hist[m] < tot * 0.015) break;
      if (chosen.includes(m) || chosen.some(c => mod(c - m, 12) === 0 || Math.abs(c - m) < 2)) continue;
      if (strict && chosen.some(c => [1, 6, 11].includes(mod(c - m, 12)))) continue;
      chosen.push(m);
    }
    let derived = 0; const ctime = m => hist[m] > 0 ? histTW[m] / hist[m] : now;
    if (!chosen.length) chosen.push(Math.round(cm));
    for (const iv of [7, 4, -5, 3, 9, 2]) { if (chosen.length >= 3) break; const r = chosen[0] + iv; if (!chosen.some(c => mod(c - r, 12) === 0 || Math.abs(c - r) < 2)) { chosen.push(r); derived++; } }
    const ord = chosen.map(m => ({ m, ct: ctime(m) })).sort((a, b) => a.ct - b.ct).map(x => x.m);
    const out = []; let prev = 57 + mod(ord[0] - 57, 12);
    out.push(prev);
    for (let j = 1; j < ord.length; j++) { let m = prev + mod(ord[j] - prev, 12); if (m - prev > 6) m -= 12; out.push(m); prev = m; }
    return makeSeed(out.map((m, j) => ({ m, len: lens[j] || 4 })), 'noise', 0.3 - 0.06 * derived, { derived });
  }
  // 持續聆聽：每個分析影格 pushFrame，poll 時若有新的靈感音則回傳
  class SeedCapture {
    constructor(o = {}) {
      this.tracker = new NoteTracker(o); this.notes = []; this.hist = new Float64Array(128); this.histTW = new Float64Array(128); this.onsets = [];
      this.lastT = null; this.seed = null; this.lastSeedT = -1e9; this.lastNoteT = -1e9; this.lastEval = -1e9; this.count = 0;
      this.minGap = o.minGap || 5; this.window = o.window || 10; this.noiseAfter = o.noiseAfter || 8; this.minScore = o.minScore || 0.35; this.rng = rng32(o.seed || 7);
    }
    pushFrame(f) {
      const t = f.t, dt = this.lastT == null ? 0.025 : clamp(t - this.lastT, 0, 0.5); this.lastT = t;
      const midi = f.freq > 0 && (f.prob || 0) >= 0.8 ? freqToMidi(f.freq) : null;
      const n = this.tracker.push(t, midi, f.prob || 0, f.rms || 0.02, !!f.onset);
      if (n) { this.notes.push(n); this.lastNoteT = t; }
      while (this.notes.length && t - this.notes[0].t > this.window * 1.5) this.notes.shift();
      const dec = Math.exp(-dt / 6), H = this.hist, W = this.histTW;
      for (let m = 0; m < 128; m++) { H[m] *= dec; W[m] *= dec; }
      if (f.peaks) for (const p of f.peaks) { const m = Math.round(freqToMidi(p.f)); if (m >= 36 && m < 100) { const w = p.mag * clamp((p.prom == null ? 2 : p.prom) - 1, 0, 6) * dt; H[m] += w; W[m] += w * t; } }
      if (f.onset) { this.onsets.push(t); while (this.onsets.length && t - this.onsets[0] > this.window) this.onsets.shift(); }
    }
    _accept(s, t) {
      s.t = t; s.id = ++this.count; this.seed = s; this.lastSeedT = t;
      if (s.source === 'pitch') this.notes = this.notes.filter(n => n.t >= s.endT); // 用過的音不再重複使用
      return s;
    }
    poll(t) {
      if (t - this.lastEval < 0.5) return null; this.lastEval = t;
      if (t - this.lastSeedT < this.minGap) return null;
      let s = extractSeed(this.notes.filter(n => t - n.t < this.window), { now: t });
      if (s && s.score < this.minScore) s = null;
      if (!s && t - this.lastNoteT > this.noiseAfter && t - this.lastSeedT > this.noiseAfter * 2) {
        let tot = 0; for (let m = 0; m < 128; m++) tot += this.hist[m];
        if (tot > 1e-5) s = seedFromNoise(this.hist, this.histTW, this.onsets, t, this.rng);
      }
      if (!s) return null;
      if (this.seed && s.label === this.seed.label && s.source !== 'pitch' && t - this.lastSeedT < 30) return null;
      return this._accept(s, t);
    }
    // 立即需要一組靈感音（例如開場或下一首來不及等）
    force(t) {
      const tn = this.tracker.flush(); if (tn) this.notes.push(tn);
      let s = extractSeed(this.notes.filter(n => t - n.t < this.window * 1.5), { now: t });
      if (!s) s = seedFromNoise(this.hist, this.histTW, this.onsets, t, this.rng);
      return this._accept(s, t);
    }
  }

  // ================= v3：調性擬合 =================
  const DEG_W = [3.0, 1.0, 2.4, 1.2, 2.6, 1.6, 0.7]; // 1 2 3 4 5 6 7 級的「穩定度」
  function keyFitScore(midis, tonic, mode, lens) {
    const sc = SCALES[mode], rels = midis.map(m => mod(m - tonic, 12)); let s = 0;
    rels.forEach((r, i) => { const w = lens ? 0.7 + 0.3 * Math.min(2, (lens[i] || 2) / 4) : 1; const ix = sc.indexOf(r); s += ix >= 0 ? DEG_W[ix] * w : -3.5 * w; });
    const triad = [0, sc[2], sc[4]], inT = rels.filter(r => triad.includes(r)).length;
    if (inT === rels.length) s += 2; else if (inT >= 2) s += 0.5;
    const last = rels[rels.length - 1], first = rels[0];
    if (last === 0) s += 0.8; else if (last === sc[4]) s += 0.3;
    if (first === 0 || first === sc[4]) s += 0.3;
    if (mode === 'major') s += 0.3;
    return s;
  }
  function fitKeys(midis, lens) {
    const out = [];
    for (let t = 0; t < 12; t++) for (const mode of ['major', 'minor']) {
      const sc = SCALES[mode], degs = midis.map(m => sc.indexOf(mod(m - t, 12)));
      out.push({ tonic: t, mode, score: keyFitScore(midis, t, mode, lens), degs, inScale: degs.every(d => d >= 0) });
    }
    return out.sort((a, b) => b.score - a.score);
  }
  // 五度圈距離（關係大小調視為同一位置）
  function keyDistance(a, b) {
    const rel = k => mod(k.mode === 'minor' ? k.tonic + 3 : k.tonic, 12), pa = mod(rel(a) * 7, 12), pb = mod(rel(b) * 7, 12), d = Math.abs(pa - pb);
    return Math.min(d, 12 - d);
  }
  function chooseKey(seed, o = {}) {
    const st = STYLES[o.style] || STYLES.folk, rank = fitKeys(seed.midis, seed.notes.map(n => n.len)), top = rank[0].score; let best = null;
    for (const c of rank.slice(0, 10)) {
      if (c.score < top - 2.5) continue;
      let s = c.score + (c.mode === 'minor' ? 1 : -1) * (st.minorBias - 1) * 2.5;
      if (o.prevKey) s -= 0.7 * keyDistance(o.prevKey, c);
      if (!best || s > best.s) best = { tonic: c.tonic, mode: c.mode, fit: c.score, s, degs: c.degs };
    }
    return best;
  }

  // ================= v3：作曲（三個音 → 一首歌）=================
  const FORMS = {
    XS: [['intro', 4], ['verse', 4], ['chorus', 4], ['bridge', 2], ['chorus', 4, 1], ['outro', 2]],
    S: [['intro', 4], ['verse', 4], ['pre', 2], ['chorus', 4], ['bridge', 2], ['chorus', 4, 1], ['outro', 4]],
    M: [['intro', 4], ['verse', 4], ['pre', 2], ['chorus', 8], ['bridge', 2], ['chorus', 8, 1], ['outro', 4]],
    L: [['intro', 4], ['verse', 8], ['pre', 4], ['chorus', 8], ['bridge', 4], ['chorus', 8, 1], ['outro', 4]],
    T: [['intro', 4], ['verse', 4], ['chorus', 4], ['chorus', 4, 1], ['outro', 4]]
  };
  const formBars = id => FORMS[id].reduce((a, s) => a + s[1], 0);
  function chooseForm(bpm, target = 75) {
    let best = 'M', bd = 1e9;
    for (const id of ['XS', 'S', 'M', 'L']) { const d = Math.abs(formBars(id) * 240 / bpm - target); if (d < bd) { bd = d; best = id; } }
    return best;
  }
  const sumLen = m => m.reduce((a, n) => a + n.len, 0);
  function fitLen(m, max = 16) { const L = sumLen(m); if (L <= max) return m; return m.map(n => Object.assign({}, n, { len: Math.max(1, Math.floor(n.len * max / L)) })); }
  // 動機變形
  const tSeq = (m, t) => m.map(n => ({ deg: n.deg + t, alt: 0, len: n.len }));
  const tInv = m => m.map(n => ({ deg: 2 * m[0].deg - n.deg, alt: 0, len: n.len }));
  const tRetro = m => m.slice().reverse().map((n, i) => ({ deg: n.deg, alt: 0, len: m[i].len }));
  const tAug = m => fitLen(m.map(n => Object.assign({}, n, { len: Math.min(8, n.len * 2) })));
  const tDim = m => { const h = m.map(n => Object.assign({}, n, { len: Math.max(1, Math.round(n.len / 2)) })); return sumLen(h) * 2 <= 16 ? h.concat(h.map(x => Object.assign({}, x))) : h; };
  // 靈感音 → Hook（只做八度移位，保留原本音高關係）
  function seedToHook(seed, key, center = 69) {
    const ms = seed.midis, mean = ms.reduce((a, b) => a + b, 0) / ms.length, mx = Math.max(...ms), mn = Math.min(...ms);
    let shift = 0, bd = Infinity; // 八度移位：靠近 center，且 Hook 落在 55–79 之內
    for (let k = -4; k <= 4; k++) { const d = Math.abs(mean + 12 * k - center) + (mx + 12 * k > 79 ? 20 : 0) + (mn + 12 * k < 55 ? 20 : 0); if (d < bd) { bd = d; shift = 12 * k; } }
    const notes = fitLen(seed.notes.map(n => ({ len: clamp(Math.round(n.len), 1, 8) }))).map((x, i) => {
      const mm = ms[i] + shift, q = quantizeToScale(mm, key.tonic, key.mode);
      return { deg: midiToDegree(q, key.tonic, key.mode, 66), alt: mm - q, len: x.len, midi: mm };
    });
    return { shift, notes, len: sumLen(notes) };
  }
  // 和弦進行對 Hook 的支撐度
  function scoreProgression(prog, notes, at = 0) {
    let s = 0, pos = at;
    notes.forEach((n, i) => {
      const bar = pos >> 4, st = pos & 15, ch = prog[bar % prog.length], rel = mod(n.deg - ch, 7), strong = st % 8 === 0 || n.len >= 4;
      const w = (strong ? 1.6 : 1) * (i === 0 ? 1.4 : 1) * (0.6 + n.len / 8);
      if (n.alt) s -= 0.3 * w; else if (rel === 0 || rel === 2 || rel === 4) s += 1.5 * w; else if (rel === 1) s -= 0.2 * w; else if (rel === 6) s -= 0.1 * w; else if (rel === 5) s -= 0.5 * w; else s -= 0.9 * w;
      pos += n.len;
    });
    if (prog[0] === 0) s += 0.4;
    return s;
  }
  const uniqProgs = list => { const seen = new Set(), out = []; for (const p of list) { const k = p.join(','); if (!seen.has(k)) { seen.add(k); out.push(p); } } return out; };
  function chooseProgression(rng, cands, notes, at, prefer, avoid) {
    const sc = cands.map(p => ({ p, s: scoreProgression(p, notes, at) + (prefer && prefer.includes(p) ? 0.5 : 0) - (p === avoid ? 1 : 0) })).sort((a, b) => b.s - a.s);
    const good = sc.filter(x => x.s >= sc[0].s - 0.8); const c = pick(rng, good); return { prog: c.p, score: c.s, ranking: sc };
  }
  // 以動機開頭的兩小節樂句
  function motifPhrase(rng, o) {
    const ev = []; let pos = o.at || 0;
    for (const n of o.motif) { ev.push([pos >> 4, pos & 15, n.len]); pos += n.len; }
    const tpl = RHYTHMS[o.tpl] || RHYTHMS.ballad8a;
    if (pos < 16) for (const [s, l] of tpl) if (s >= pos) ev.push([0, s, Math.min(l, 16 - s)]);
    for (const [s, l] of endingBar(tpl, rng)) if (16 + s >= pos) ev.push([1, s, l]);
    if (ev.length === o.motif.length) ev.push([1, 8, 8]);
    return buildPhrase(rng, { rhythm: ev, prefix: o.motif.map(n => n.deg), lock: o.lock ? o.motif.length : 0, alts: o.motif.map(n => n.alt || 0),
      chordAt: o.chordAt, center: Math.round((o.lo + o.hi) / 2), lo: o.lo, hi: o.hi, penta: o.penta, repeat: o.repeat, ending: o.ending, leap: o.leap });
  }
  // 重複一個既有樂句（Hook 再現），依新和弦重新對齊非鎖定的強拍音
  function repeatPhrase(rng, ph, o) {
    const lockN = ph.filter(n => n.hook).length;
    return buildPhrase(rng, { rhythm: ph.map(n => [n.bar, n.step, n.len]), prefix: ph.slice(0, -1).map(n => n.deg), lock: lockN, alts: ph.map(n => n.alt || 0),
      chordAt: o.chordAt, center: Math.round((o.lo + o.hi) / 2), lo: o.lo, hi: o.hi, penta: o.penta, repeat: o.repeat, ending: o.ending });
  }
  const shiftBars = (ph, off) => ph.map(n => Object.assign({}, n, { bar: n.bar + off }));
  function composeSectionMelody(rng, sec, X) {
    const nP = Math.max(1, sec.bars >> 1), out = [], H = X.hook, R = X.st.rhythm, phrases = [];
    const tones = b => chordToneDegs(sec.chords[Math.min(b, sec.bars - 1)]);
    const rg = X.range[sec.type] || X.range.chorus, tpl = pick(rng, R[sec.type] || (sec.type === 'intro' || sec.type === 'outro' ? R.chorus : R.verse));
    for (let p = 0; p < nP; p++) {
      const off = 2 * p, last = p === nP - 1, base = { chordAt: b => tones(b + off), lo: rg[0], hi: rg[1], penta: X.penta, repeat: X.st.repeat, tpl };
      let ph = null, spec = null;
      switch (sec.type) {
        case 'chorus':
          if (sec.final && X.chorusPhrases && X.chorusPhrases[p] && !last) { ph = X.chorusPhrases[p].map(n => Object.assign({}, n)); break; }
          if (sec.final && X.chorusPhrases && X.chorusPhrases[p]) { ph = repeatPhrase(rng, X.chorusPhrases[p], Object.assign(base, { ending: 'tonic' })); break; }
          if (p === 0) spec = { motif: H, lock: true, ending: last ? 'tonic' : 'open', leap: true };
          else if (p === 1) spec = { motif: tSeq(H, X.seqStep), ending: last ? 'tonic' : 'close' };
          else if (p === 2) { ph = repeatPhrase(rng, phrases[0], Object.assign(base, { ending: last ? 'tonic' : 'open' })); break; }
          else spec = X.answer === 'dim' ? { motif: tDim(H), lock: true, ending: 'tonic' } : { motif: tSeq(H, -X.seqStep), ending: 'tonic' };
          break;
        case 'verse':
          if (p === 0) spec = { motif: X.verseMotif, lock: true, at: X.verseAt, ending: last ? 'open' : 'open' };
          else if (p === 1) spec = { motif: rng() < 0.5 ? tSeq(X.verseMotif, -1) : tRetro(X.verseMotif), at: X.verseAt, ending: last ? 'open' : 'close' };
          else if (p === 2) { ph = repeatPhrase(rng, phrases[0], Object.assign(base, { ending: 'open' })); break; }
          else spec = { motif: tSeq(X.verseMotif, pick(rng, [1, -2])), at: X.verseAt, ending: 'open' };
          break;
        case 'pre': { const fr = H.slice(0, 2).map(n => ({ deg: n.deg, alt: 0, len: 2 })); spec = { motif: tSeq(fr, 1 + p).concat(tSeq(fr, 2 + p)), ending: 'open', leap: true }; break; }
        case 'bridge': spec = p === 0 ? { motif: tAug(tInv(H)), ending: 'open' } : { motif: tSeq(tInv(H), -1), ending: 'open' }; break;
        case 'intro': spec = p === 0 ? { motif: H, lock: true, ending: 'open' } : { motif: tSeq(H, X.seqStep), ending: 'close' }; break;
        case 'outro': spec = p === 0 ? { motif: tAug(H), lock: true, ending: 'tonic' } : { motif: H, lock: true, ending: 'tonic' }; break;
        default: spec = { motif: H, lock: true, ending: 'tonic' };
      }
      if (!ph) ph = motifPhrase(rng, Object.assign(base, spec));
      phrases.push(ph);
      for (const n of ph) out.push(Object.assign({}, n, { bar: n.bar + off }));
    }
    return { mel: out, phrases };
  }
  const TITLE_WORDS = {
    rnb: { zh: ['晚風', '舊街', '煙雨', '琥珀', '霧城', '紙飛機', '青石巷', '月台'], en: ['Evening Breeze', 'Old Street', 'Misty Town', 'Amber', 'Paper Plane', 'Platform 9'] },
    folk: { zh: ['小城', '遠方', '炊煙', '落日', '行李', '歸途', '山海', '老照片'], en: ['Small Town', 'Far Away', 'Sunset Road', 'Way Home', 'Old Photo'] },
    power: { zh: ['光年', '逆風', '星火', '心跳', '破曉', '回聲', '不落'], en: ['Light Years', 'Against the Wind', 'Spark', 'Heartbeat', 'Daybreak'] },
    lyric: { zh: ['留白', '雨後', '微光', '信箋', '靜夜', '花期', '餘溫'], en: ['White Space', 'After Rain', 'Faint Light', 'Letters', 'Quiet Night'] },
    us: { zh: ['公路', '日光', '霓虹', '奔跑', '夏夜', '天際線'], en: ['Highway', 'Sunlight', 'Neon Hearts', 'Runaway', 'Summer Night', 'Skyline'] },
    kpop: { zh: ['閃光', '節拍', '糖果', '電波', '流星', '心動訊號'], en: ['Flash', 'On Beat', 'Candy Pop', 'Signal', 'Shooting Star'] }
  };
  function songTitle(seed, style, rng) {
    const w = TITLE_WORDS[style] || TITLE_WORDS.folk, names = seed.names.join('–');
    return { zh: '《' + pick(rng, w.zh) + '・' + names + '》', en: pick(rng, w.en) + ' (' + names + ')' };
  }
  // 產生器：每次 next() 完成一小步（方便在 idle 時間分段計算）
  function* composeSongGen(seed, o = {}) {
    const rng = rng32(o.seed || 1), style = STYLES[o.style] ? o.style : 'folk', st = STYLES[style], HS = HARM_STYLE[style];
    const key = o.key ? Object.assign({ fit: keyFitScore(seed.midis, o.key.tonic, o.key.mode) }, o.key) : chooseKey(seed, { style, prevKey: o.prevKey });
    const mode = key.mode;
    let bpm = o.bpm || lerp(st.bpm[0], st.bpm[1], clamp(o.intensity == null ? 0.5 : o.intensity, 0, 1));
    if (!o.bpm && o.tempoHint) bpm = lerp(bpm, clamp(o.tempoHint, st.bpm[0], st.bpm[1]), 0.5);
    if (!o.bpm && o.prevBpm) bpm = lerp(bpm, clamp(o.prevBpm, st.bpm[0], st.bpm[1]), 0.5);
    bpm = Math.round(clamp(bpm, st.bpm[0] - 4, st.bpm[1] + 4));
    const formId = o.form && FORMS[o.form] ? o.form : chooseForm(bpm, o.targetSec || 75);
    yield 'key';
    const hk = seedToHook(seed, key, 65 + 0.6 * st.reg[1]), H = hk.notes;
    const D = m => midiToDegree(m, key.tonic, mode, 66);
    let hLo = Infinity, hHi = -Infinity; for (const n of H) { hLo = Math.min(hLo, n.deg); hHi = Math.max(hHi, n.deg); }
    const LO = D(55), HI = D(86);
    const range = {
      chorus: [Math.max(LO, hLo - 3), Math.min(HI, Math.max(hHi + 4, hLo + 8))],
      verse: [Math.max(LO, hLo - 5), Math.min(HI, hHi + 2)],
      pre: [Math.max(LO, hLo - 2), Math.min(HI, hHi + 5)],
      bridge: [Math.max(LO, hLo - 4), Math.min(HI, hHi + 3)]
    };
    range.intro = range.chorus; range.outro = range.verse;
    const L = hk.len, verseMotif = L <= 8 ? tAug(H) : H, verseAt = L <= 8 ? 0 : (L <= 14 ? 2 : 0);
    yield 'hook';
    const stProg = st.prog[mode].concat(HS.prog[mode]), cands = uniqProgs(stProg.concat(PROGRESSIONS[mode]));
    const ch = chooseProgression(rng, cands, H, 0, stProg);
    const vs = chooseProgression(rng, cands.filter(p => p !== ch.prog && p[0] + ',' + p[1] !== ch.prog[0] + ',' + ch.prog[1]), verseMotif, verseAt, stProg, ch.prog); // v4：主歌與副歌用不同進行
    const brC = BRIDGE_PROG[mode].filter(p => p.join() !== ch.prog.join() && p.join() !== vs.prog.join());
    const progs = { chorus: ch.prog, verse: vs.prog, pre: pick(rng, PRE_PROG[mode]), bridge: pick(rng, brC.length ? brC : BRIDGE_PROG[mode]) };
    progs.intro = progs.chorus; progs.outro = progs.chorus;
    yield 'harmony';
    const sections = []; let b0 = 0;
    for (const [type, bars, fin] of FORMS[formId]) {
      const pg = progs[type], chords = [];
      for (let b = 0; b < bars; b++) chords.push(pg[b % pg.length]);
      if (fin && bars >= 2) { chords[bars - 2] = 4; chords[bars - 1] = 0; }
      if (type === 'outro') chords[bars - 1] = 0;
      if (type === 'pre' && bars >= 2) chords[bars - 1] = 4;                                                  // v4：導歌停在 V（張力）
      if (type === 'chorus' && !fin && bars >= 4 && rng() < HS.deceptive) { chords[bars - 2] = 4; chords[bars - 1] = 5; } // v4：假終止 V → vi
      const hint = BASS_HINTS[mode + ':' + pg.join(',')];
      sections.push({ type, bars, start: b0, final: !!fin, chords, mel: [], bassHint: hint && !fin ? chords.map((d, b) => d === pg[b % pg.length] ? hint[b % hint.length] : null) : null }); b0 += bars;
    }
    const X = { hook: H, st, range, penta: rng() < st.penta ? PENTA[mode] : null, verseMotif, verseAt, seqStep: pick(rng, [1, -1, 2]), answer: rng() < 0.5 ? 'dim' : 'seq', chorusPhrases: null };
    for (const sec of sections.filter(s => !s.final).concat(sections.filter(s => s.final))) { // 先寫一般副歌，最後副歌沿用
      const r = composeSectionMelody(rng, sec, X); sec.mel = r.mel;
      if (sec.type === 'chorus' && !sec.final && !X.chorusPhrases) X.chorusPhrases = r.phrases;
      yield sec.type;
    }
    const st7 = rng() < st.seventh, add9 = rng() < st.add9;
    // v4：最後副歌升 Key（半音／全音），之後的尾奏也在新調
    let lift = 0; const fi = sections.findIndex(s => s.final);
    if (fi > 0 && (o.lift != null ? o.lift > 0 : rng() < HS.lift)) {
      const L = o.lift > 0 ? o.lift : (rng() < 0.55 ? 1 : 2); let mx = -1e9;
      for (const s of sections.slice(fi)) for (const n of s.mel) mx = Math.max(mx, leadMidi({ key }, n));
      if (mx + L <= 86) lift = L;
    }
    if (lift) for (const s of sections.slice(fi)) { s.lift = lift; for (const n of s.mel) n.lift = lift; }
    yield 'lift';
    const song = { id: o.id || 0, title: songTitle(seed, style, rng), seed, style, styleLabel: st.label, key: { tonic: key.tonic, mode }, keyLabel: keyName(key.tonic, mode), keyFit: key.fit,
      bpm, form: formId, totalBars: b0, sections, hook: H, hookShift: hk.shift, progs, progScore: ch.score, seventh: st7, add9, intensity: o.intensity == null ? 0.5 : o.intensity,
      introBars: sections[0].type === 'intro' ? sections[0].bars : 0, outroBars: sections[sections.length - 1].type === 'outro' ? sections[sections.length - 1].bars : 0,
      finalStart: (sections.find(s => s.final) || sections[sections.length - 1]).start, duration: b0 * 240 / bpm,
      lift, endKey: { tonic: mod(key.tonic + lift, 12), mode }, rseed: (o.seed || 1) >>> 0 };
    harmonizeSong(song, rng32(((o.seed || 1) * 7 + 3) >>> 0)); // v4：和聲色彩、修正、聲部進行、副旋律
    yield 'voicing';
    return song;
  }
  function composeSong(seed, o) { const g = composeSongGen(seed, o); let r; do { r = g.next(); } while (!r.done); return r.value; }
  function sectionAt(song, bar) {
    for (const sec of song.sections) if (bar >= sec.start && bar < sec.start + sec.bars) return { sec, secBar: bar - sec.start };
    const s = song.sections[song.sections.length - 1]; return { sec: s, secBar: s.bars - 1 };
  }
  const leadMidi = (song, n) => degreeToMidi(n.deg, song.key.tonic, song.key.mode, 66) + (n.alt || 0) + (n.lift || 0);

  // ================= v3：DJ 轉場規劃 =================
  const DJ_TECH = {
    eqswap: { label: '等化器交換＋低頻互換', off: 0 },
    filter: { label: '濾波器掃頻', off: 0 },
    riser: { label: '鼓過門＋升頻噪音＋鈸', off: 2, cutOutro: true },
    echo: { label: '回聲甩尾', off: 2 },
    reverse: { label: '反向鈸聲漸強', off: 2 },
    break: { label: '鼓組橋接', off: 0 },
    cut: { label: '瞬間切換 Drop', off: 4, cutOutro: true }
  };
  const DJ_IDS = Object.keys(DJ_TECH);
  // A: { startBar, offset, totalBars, outroBars, bpm, key }；B: { introBars, bpm, key }；所有小節皆為全域（絕對）小節
  function planTransition(A, B, o = {}) {
    const rng = o.rng || Math.random;
    const type = o.type && DJ_TECH[o.type] ? o.type : pick(rng, DJ_IDS.filter(id => id !== o.avoid));
    const T = DJ_TECH[type], introB = B.introBars || 4;
    let aEnd = A.startBar - (A.offset || 0) + A.totalBars;
    if (T.cutOutro && A.outroBars && aEnd - A.outroBars > (o.minBar == null ? -Infinity : o.minBar + 2)) aEnd -= A.outroBars;
    const off = Math.min(T.off, introB), overlap = introB - off, bStart = aEnd - overlap;
    const minBar = o.minBar == null ? -Infinity : o.minBar;
    const dB = Math.abs(B.bpm - A.bpm), rampBars = dB < 3 ? 2 : dB < 10 ? 4 : 8;
    const rampEnd = Math.max(bStart, minBar + 1), rampStart = Math.max(minBar + 1, rampEnd - rampBars);
    const keyDist = keyDistance(A.key, B.key);
    const pivot = keyDist >= 2 && bStart - 1 > minBar ? { bar: bStart - 1, pcs: diatonicChord(B.key.tonic, 'major', 4, 3), name: chordName(B.key.tonic, 'major', 4) } : null;
    const fx = [], F = (target, from, to, v0, v1, curve) => { from = Math.max(from, minBar + 1); to = Math.max(to, from); fx.push({ target, from, to, v0, v1, curve: curve || 'lin' }); };
    switch (type) {
      case 'eqswap':
        F('B.gain', bStart, aEnd - 2, 0.8, 1); F('B.bass', bStart, bStart, 0, 0); F('B.lp', bStart, aEnd - 2, 400, 18000, 'exp'); F('A.hp', bStart, aEnd, 30, 380, 'exp');
        F('A.bass', aEnd - 2, aEnd - 2 + 0.06, 1, 0); F('B.bass', aEnd - 2, aEnd - 2 + 0.06, 0, 1); F('A.gain', aEnd - 2, aEnd, 1, 0); break;
      case 'filter':
        F('A.lp', aEnd - 6, aEnd, 18000, 220, 'exp'); F('A.gain', aEnd - 1, aEnd, 1, 0); F('B.hp', bStart, aEnd, 900, 25, 'exp'); F('B.gain', bStart, aEnd, 0.7, 1); break;
      case 'riser':
        F('riser', aEnd - 4, aEnd, 0, 1); F('A.hp', aEnd - 2, aEnd, 30, 500, 'exp'); F('A.gain', aEnd, aEnd + 0.03, 1, 0);
        F('B.lp', bStart, aEnd, 500, 18000, 'exp'); F('B.gain', bStart, aEnd, 0.5, 1); F('crash', aEnd, aEnd, 1, 1); break;
      case 'echo':
        F('A.throw', aEnd - 1, aEnd - 0.5, 0, 0.9); F('fb', aEnd - 1, aEnd + 2, 0.62, 0.35); F('A.dry', aEnd - 0.5, aEnd - 0.25, 1, 0); F('A.throw', aEnd + 1, aEnd + 1.5, 0.9, 0);
        F('B.lp', bStart, aEnd, 1200, 18000, 'exp'); F('B.gain', bStart, aEnd, 0.35, 1); break;
      case 'reverse':
        F('revcym', aEnd - 1, aEnd, 0, 1); F('A.lp', aEnd - 2, aEnd, 18000, 1200, 'exp'); F('A.gain', aEnd - 0.5, aEnd, 1, 0); F('B.gain', bStart, aEnd, 0.45, 1); F('crash', aEnd, aEnd, 1, 1); break;
      case 'break':
        F('A.melodic', bStart, bStart + 0.25, 1, 0); F('B.gain', bStart, aEnd, 0.6, 1); F('B.hp', bStart, aEnd, 300, 25, 'exp'); F('A.gain', aEnd, aEnd + 0.03, 1, 0); F('crash', aEnd, aEnd, 1, 1); break;
      case 'cut':
        F('A.gain', aEnd, aEnd + 0.01, 1, 0); F('B.gain', aEnd, aEnd, 1, 1); F('crash', aEnd, aEnd, 1, 1); break;
    }
    return { type, label: T.label, aEnd, bStart, bOffset: off, overlap, bDrumIn: aEnd, aFillBar: (type === 'riser' || type === 'cut' || type === 'break') ? aEnd - 1 : null,
      rampStart, rampEnd, fromBpm: A.bpm, toBpm: B.bpm, keyDist, pivot, fx, aForceDrums: type === 'break' ? [bStart, aEnd] : null, outroCut: aEnd !== A.startBar - (A.offset || 0) + A.totalBars };
  }
  // 速度曲線：rampStart → rampEnd 線性過渡（小節可為小數）
  function bpmAt(plan, barF) {
    if (barF <= plan.rampStart) return plan.fromBpm; if (barF >= plan.rampEnd) return plan.toBpm;
    return lerp(plan.fromBpm, plan.toBpm, (barF - plan.rampStart) / (plan.rampEnd - plan.rampStart));
  }
  // 從 b0 到 b1（小節，可為小數）所需秒數；以十六分音符積分
  function barsDuration(plan, b0, b1, bpm) {
    if (b1 <= b0) return 0; let t = 0;
    const s0 = Math.floor(b0 * 16), s1 = Math.ceil(b1 * 16);
    for (let s = s0; s < s1; s++) { const a = Math.max(b0, s / 16), b = Math.min(b1, (s + 1) / 16); if (b <= a) continue; const bp = plan ? bpmAt(plan, s / 16) : bpm; t += (b - a) * 16 * 15 / bp; }
    return t;
  }
  const drumOwner = (plan, bar) => bar < plan.bDrumIn ? 'A' : 'B';


  // ================= v4：和聲語彙・聲部進行・編曲（純函式，可測試） =================
  const HARM_MINOR = [0, 2, 3, 5, 7, 8, 11];
  const dist12 = (a, b) => { const d = mod(b - a, 12); return Math.min(d, 12 - d); };
  const QUAL = { '': [0, 4, 7], m: [0, 3, 7], dim: [0, 3, 6], maj7: [0, 4, 7, 11], m7: [0, 3, 7, 10], '7': [0, 4, 7, 10], m7b5: [0, 3, 6, 10], dim7: [0, 3, 6, 9],
    add9: [0, 4, 7, 14], madd9: [0, 3, 7, 14], sus2: [0, 2, 7], sus4: [0, 5, 7], '7sus4': [0, 5, 7, 10], '6': [0, 4, 7, 9], m6: [0, 3, 7, 9],
    maj9: [0, 4, 7, 11, 14], m9: [0, 3, 7, 10, 14], '9': [0, 4, 7, 10, 14], m7b5b9: [0, 3, 6, 10, 13] };
  const QUAL_KEY = {}; for (const q in QUAL) QUAL_KEY[QUAL[q].join(',')] = q;
  const QUAL_SFX = { '': '', m: 'm', dim: '°', maj7: 'maj7', m7: 'm7', '7': '7', m7b5: 'm7♭5', dim7: '°7', add9: 'add9', madd9: 'm(add9)', sus2: 'sus2', sus4: 'sus4', '7sus4': '7sus4', '6': '6', m6: 'm6', maj9: 'maj9', m9: 'm9', '9': '9', m7b5b9: 'm7♭5♭9' };
  function mkChord(root, iv, kind, o) {
    const q = QUAL_KEY[iv.join(',')]; if (q == null) return null; const r = mod(root, 12), pcs = [];
    for (const x of iv) { const p = mod(r + x, 12); if (!pcs.includes(p)) pcs.push(p); }
    return Object.assign({ root: r, iv: iv.slice(), q, pcs, bass: r, ped: null, kind }, o || {});
  }
  // 調內和弦（含延伸音）；ext: tri 7 9 add9 6 sus2 sus4 7sus4。不合法（例如 ♭9）回傳 null
  function scaleChord(tonic, mode, deg, ext = 'tri') {
    const sc = SCALES[mode], pc = d => mod(tonic + sc[mod(d, 7)], 12), r = pc(deg), rel = d => mod(pc(deg + d) - r, 12);
    const t3 = rel(2), t5 = rel(4), t7 = rel(6), t9 = rel(1), t6 = rel(5), t4 = rel(3); let iv;
    switch (ext) {
      case 'tri': iv = [0, t3, t5]; break;
      case '7': iv = [0, t3, t5, t7]; break;
      case '9': if (t9 !== 2 || t5 !== 7) return null; iv = [0, t3, t5, t7, 14]; break;
      case 'add9': if (t9 !== 2 || t5 !== 7) return null; iv = [0, t3, t5, 14]; break;
      case '6': if (t6 !== 9 || t5 !== 7) return null; iv = [0, t3, t5, 9]; break;
      case 'sus2': if (t9 !== 2 || t5 !== 7) return null; iv = [0, 2, 7]; break;
      case 'sus4': if (t4 !== 5 || t5 !== 7) return null; iv = [0, 5, 7]; break;
      case '7sus4': if (t4 !== 5 || t5 !== 7 || t7 !== 10) return null; iv = [0, 5, 7, 10]; break;
      default: return null;
    }
    return mkChord(r, iv, 'dia', { deg: mod(deg, 7), ext });
  }
  const hmDom = (tonic, seventh) => mkChord(tonic + 7, seventh ? [0, 4, 7, 10] : [0, 4, 7], 'hm', { deg: 4 });           // 小調和聲小音階 V
  const secDom = (target, seventh) => mkChord(target + 7, seventh ? [0, 4, 7, 10] : [0, 4, 7], 'sec', { target: mod(target, 12) }); // 副屬和弦 V/x
  const triSub = target => mkChord(target + 1, [0, 4, 7, 10], 'tri', { target: mod(target, 12) });                      // 三全音代理 ♭II7
  const passDim = target => mkChord(target - 1, [0, 3, 6, 9], 'pass', { target: mod(target, 12) });                    // 半音經過減七
  function borChord(tonic, mode, deg, ext) { const c = scaleChord(tonic, mode === 'major' ? 'minor' : 'major', deg, ext); if (c) c.kind = 'bor'; return c; } // 同主音大小調借用
  const liftDom = newTonic => mkChord(newTonic + 7, [0, 4, 7, 10], 'lift', { target: mod(newTonic, 12) });              // 升 Key 前的新調屬七
  // 和弦是否「在調內，或為刻意的借用／副屬／代理／經過和弦」
  function chordInKey(c, key, o = {}) {
    const T = key.tonic, inSc = sc => c.pcs.every(p => sc.includes(mod(p - T, 12))), isDom7 = c.iv.join() === '0,4,7,10', isMaj = c.iv.join() === '0,4,7';
    const diaTarget = t => { const i = SCALES[key.mode].indexOf(mod(t - T, 12)); return i >= 0 && scaleChord(T, key.mode, i, 'tri').q !== 'dim'; };
    if (c.ped != null && !SCALES[key.mode].includes(mod(c.ped - T, 12))) return false;
    switch (c.kind) {
      case 'dia': return inSc(SCALES[key.mode]);
      case 'hm': return key.mode === 'minor' && inSc(HARM_MINOR);
      case 'bor': return inSc(SCALES[key.mode === 'major' ? 'minor' : 'major']);
      case 'sec': return (isDom7 || isMaj) && c.root === mod(c.target + 7, 12) && diaTarget(c.target);
      case 'tri': return isDom7 && c.root === mod(c.target + 1, 12) && SCALES[key.mode].includes(mod(c.target - T, 12));
      case 'pass': return c.q === 'dim7' && c.root === mod(c.target - 1, 12) && SCALES[key.mode].includes(mod(c.target - T, 12));
      case 'lift': return isDom7 && c.root === mod(c.target + 7, 12) && o.liftTarget != null && c.target === mod(o.liftTarget, 12);
      case 'pivot': return true;
    }
    return false;
  }
  function chordLabel(c, key) {
    const rn = spellPc(c.root, key), tbl = /♭/.test(rn) || c.kind === 'bor' ? NAMES_FLAT : /♯/.test(rn) || ['sec', 'hm', 'lift', 'pass'].includes(c.kind) ? NAMES_SHARP : null;
    const sp = p => tbl ? tbl[mod(p, 12)] : spellPc(p, key); let s = (tbl ? tbl[c.root] : rn) + QUAL_SFX[c.q];
    const b = c.ped != null ? c.ped : c.bass; if (b !== c.root) s += '/' + sp(b); return s;
  }
  // 各風格的和聲色彩（機率）
  const HARM_STYLE = {
    rnb: { fam: 'jazz', p7: 0.85, sec: 0.5, tri: 0.4, pass: 0.3, bor: 0.25, split: 0.55, inv: 0.55, pedal: 0.35, lift: 0, deceptive: 0.5, sus: 0.45 , prog: { major: [[1, 4, 0, 5], [0, 4, 5, 0, 3, 0, 1, 4]], minor: [[0, 4, 5, 2], [0, 6, 5, 4]] } },
    folk: { fam: 'pop', p7: 0.5, sec: 0.3, tri: 0, pass: 0.08, bor: 0.15, split: 0.3, inv: 0.75, pedal: 0.4, lift: 0.1, deceptive: 0.35, sus: 0.5 , prog: { major: [[0, 1, 0, 3], [0, 4, 5, 0, 3, 0, 1, 4]], minor: [[0, 4, 5, 2]] } },
    power: { fam: 'pop', p7: 0.55, sec: 0.35, tri: 0, pass: 0.1, bor: 0.45, split: 0.4, inv: 0.6, pedal: 0.45, lift: 0.85, deceptive: 0.5, sus: 0.6 , prog: { major: [[0, 4, 5, 2, 3, 0, 3, 4]], minor: [[0, 6, 5, 4]] } },
    lyric: { fam: 'jazz', p7: 0.75, sec: 0.4, tri: 0.05, pass: 0.2, bor: 0.35, split: 0.35, inv: 0.65, pedal: 0.4, lift: 0.3, deceptive: 0.5, sus: 0.5 , prog: { major: [[0, 4, 5, 0, 3, 0, 1, 4]], minor: [[0, 4, 5, 2]] } },
    us: { fam: 'pop', p7: 0.4, sec: 0.2, tri: 0, pass: 0, bor: 0.4, split: 0.25, inv: 0.4, pedal: 0.3, lift: 0.35, deceptive: 0.3, sus: 0.55 , prog: { major: [[0, 4, 5, 2, 3, 0, 3, 4]], minor: [[0, 6, 5, 4]] } },
    kpop: { fam: 'jazz', p7: 0.7, sec: 0.35, tri: 0.1, pass: 0.1, bor: 0.25, split: 0.45, inv: 0.35, pedal: 0.45, lift: 0.8, deceptive: 0.4, sus: 0.5 , prog: { major: [[0, 4, 5, 2, 3, 0, 1, 4]], minor: [[0, 4, 5, 2]] } }
  };
  const EXT = { // 依級數（0 = I）可用的延伸
    jazz: { major: [['7', '9', 'add9', '6'], ['7', '9'], ['7'], ['7', 'add9', '6', '9'], ['7', '9', '7sus4'], ['7', '9'], ['7']],
      minor: [['7', '9', 'add9'], ['7'], ['7', 'add9'], ['7', '9'], ['7'], ['7', 'add9'], ['7', 'add9']] },
    pop: { major: [['add9', 'sus2', '6', '7'], ['7'], ['7'], ['add9', '7', 'sus2'], ['7', 'sus4'], ['7'], ['7']],
      minor: [['add9', '7'], ['7'], ['add9', '7'], ['7'], ['7'], ['add9', '7'], ['add9']] }
  };
  function shuffle(rng, a) { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); const t = a[i]; a[i] = a[j]; a[j] = t; } return a; }
  // 旋律（絕對十六分音符位置）對和弦的檢查
  const melInfo = (song, sec) => sec.mel.map(n => ({ n, pos: n.bar * 16 + n.step, len: n.len, pc: mod(leadMidi(song, n), 12), hook: !!n.hook || !!n.alt }));
  function harmViol(c, mel, p0, p1) { let v = 0; for (const x of mel) { if (x.pos + x.len <= p0 || x.pos >= p1) continue; const strong = x.pos < p0 || x.pos % 8 === 0 || x.len >= 4; if (strong && !c.pcs.includes(x.pc)) v++; } return v; }
  function harmClash(c, basePcs, mel, p0, p1) {
    const nt = c.pcs.filter(p => !basePcs.includes(p)); if (!nt.length) return false;
    for (const x of mel) { if (x.pos + x.len <= p0 || x.pos >= p1 || c.pcs.includes(x.pc)) continue; if ((x.len >= 2 || x.pos % 4 === 0) && nt.some(p => dist12(p, x.pc) === 1)) return true; }
    return false;
  }
  const harmFits = (c, base, mel, p0, p1) => !!c && harmViol(c, mel, p0, p1) <= harmViol(base, mel, p0, p1) && !harmClash(c, base.pcs, mel, p0, p1);
  const sameChord = (a, b) => !!a && !!b && a.root === b.root && a.q === b.q;
  function colorPick(T, mode, deg, HS, R, mel, p0, p1) {
    const base = scaleChord(T, mode, deg, 'tri');
    if (R() < HS.p7) for (const e of shuffle(R, EXT[HS.fam][mode][mod(deg, 7)])) { const c = scaleChord(T, mode, deg, e); if (c && harmFits(c, base, mel, p0, p1)) return c; }
    return base;
  }
  const chordAtStep = (sec, bar, step) => { const hs = sec.harm[clamp(bar, 0, sec.bars - 1)]; let c = hs[0]; for (const h of hs) if (step >= h.s) c = h; return c; };
  // 一個段落：級數 → 實際和弦（延伸、借用、副屬、代理、經過、掛留解決、和聲節奏、持續低音、指定低音線）
  function colorSection(song, si, HS, R) {
    const sec = song.sections[si], T = mod(song.key.tonic + (sec.lift || 0), 12), mode = song.key.mode, bars = sec.bars, type = sec.type, mel = melInfo(song, sec);
    const nextSec = song.sections[si + 1], nextDeg = nextSec && !nextSec.lift === !sec.lift ? nextSec.chords[0] : null, harm = [];
    for (let b = 0; b < bars; b++) {
      const deg = sec.chords[b], p0 = b * 16, next = b + 1 < bars ? sec.chords[b + 1] : nextDeg, base = scaleChord(T, mode, deg, 'tri');
      let c = colorPick(T, mode, deg, HS, R, mel, p0, p0 + 16);
      const cad = next === 0 || b === bars - 1, hookBar = (type === 'chorus' || type === 'verse') && b === 0; let sub = null;
      if (mode === 'minor' && deg === 4 && R() < (cad ? 0.9 : 0.45)) sub = hmDom(T, R() < HS.p7 + 0.2);
      else if (!hookBar && type !== 'intro') {
        if (mode === 'major' && deg === 3 && type !== 'verse' && R() < HS.bor * (type === 'bridge' ? 1.3 : 0.7)) sub = borChord(T, mode, 3, R() < HS.p7 ? '7' : 'tri');      // iv
        else if (mode === 'major' && deg === 5 && (type === 'bridge' || sec.final || type === 'pre') && R() < HS.bor * 0.6) sub = borChord(T, mode, 5, R() < HS.p7 ? '7' : 'tri'); // ♭VI
        else if (mode === 'major' && deg === 4 && !cad && type !== 'verse' && R() < HS.bor * 0.4) sub = borChord(T, mode, 6, 'tri');                                   // ♭VII
        else if (mode === 'minor' && deg === 3 && R() < HS.bor * 0.4) sub = borChord(T, mode, 3, 'tri');                                                               // 多利安 IV
      }
      if (sub && harmFits(sub, base, mel, p0, p0 + 16)) c = sub;
      // 和聲節奏：副歌常一小節兩個和弦；樂句尾（每 4 小節）加 turnaround
      const turn = bars >= 2 && (b % 4 === 3 || b === bars - 1) && type !== 'intro' && type !== 'outro';
      let pS = { chorus: HS.split, pre: HS.split * 0.8, verse: 0.1, bridge: 0.15, inter: 0.1 }[type] || 0;
      if (turn) pS = Math.max(pS, 0.55);
      if (sec.final && b >= bars - 2) pS = deg === 4 ? HS.sus : 0;
      if (type === 'intro' || type === 'outro') pS = 0;
      let first = c, second = null;
      if (R() < pS) {
        if (deg === 4 && R() < HS.sus + 0.25) { const s4 = scaleChord(T, mode, 4, R() < 0.5 ? '7sus4' : 'sus4'); if (s4 && harmFits(s4, base, mel, p0, p0 + 8)) { first = s4; second = c; } } // 掛留 → 解決
        if (!second) {
          const nb = next == null ? null : scaleChord(T, mode, next, 'tri'), nT = nb ? nb.root : null, cs = [];
          if (nb && nT !== c.root) {
            if (next === 0 && deg === 3 && mode === 'major' && R() < HS.bor + 0.2) cs.push(borChord(T, mode, 3, 'tri'));          // IV – iv – I
            if (next !== 0 && nb.q !== 'dim' && R() < HS.sec) cs.push(secDom(nT, R() < 0.75));                                     // V/x
            if (HS.tri && R() < HS.tri) cs.push(triSub(nT));                                                                       // ♭II7/x
            if (HS.pass && mod(nT - c.root, 12) === 2 && R() < HS.pass) cs.push(passDim(nT));                                       // ♯I°7
            if (next === 0 && deg !== 4) cs.push(mode === 'minor' ? hmDom(T, true) : scaleChord(T, mode, 4, R() < HS.p7 ? '7' : 'tri')); // … V → I
            if (next === 4 && deg !== 1 && deg !== 3) cs.push(scaleChord(T, mode, 1, mode === 'major' ? '7' : 'tri'), scaleChord(T, mode, 3, 'tri')); // ii7 / IV → V
            cs.push(colorPick(T, mode, mod(deg + 5, 7), HS, R, mel, p0 + 8, p0 + 16));                                             // 下三度（兩個共同音）
          }
          for (const x of cs) if (x && !sameChord(x, c) && !sameChord(x, nb) && harmFits(x, base, mel, p0 + 8, p0 + 16)) { second = x; break; }
        }
      }
      harm.push(second ? [Object.assign(first, { s: 0, l: 8 }), Object.assign(second, { s: 8, l: 8 })] : [Object.assign(first, { s: 0, l: 16 })]);
    }
    const ped = (pc, from, to) => { for (let b = from; b < to; b++) for (const c of harm[b]) if (!c.pcs.some(p => dist12(p, pc) === 1)) c.ped = mod(pc, 12); };
    if (type === 'intro' && R() < HS.pedal) ped(T, 0, bars);                                  // 主音持續
    if (type === 'pre' && R() < HS.pedal + 0.2) ped(T + 7, Math.max(0, bars - 2), bars);       // 導歌屬音持續（IV/V 的張力）
    if (type === 'bridge' && bars >= 4 && R() < HS.pedal * 0.5) ped(T + 7, bars - 1, bars);
    if (type === 'outro' && R() < HS.pedal) ped(T, 0, bars);
    if (sec.bassHint) for (let b = 0; b < bars; b++) { const h = sec.bassHint[b]; if (h == null) continue; const pc = mod(T + SCALES[mode][mod(h, 7)], 12), c = harm[b][0]; if (c.ped == null && c.pcs.includes(pc)) { c.bass = pc; c.hinted = true; } }
    sec.harm = harm;
  }
  // 修正：強拍旋律音若不是和弦音 → 非鎖定音移到最近的和弦音；鎖定的靈感音 → 改用包含它的延伸和弦
  function repairSection(song, sec) {
    const T = mod(song.key.tonic + (sec.lift || 0), 12), mode = song.key.mode, mel = melInfo(song, sec); let fixed = 0, extended = 0;
    const ends = new Set(); { const g = {}; mel.forEach((x, i) => { g[x.n.bar >> 1] = i; }); for (const k in g) ends.add(g[k]); }
    mel.forEach((x, i) => {
      if (!(x.pos % 8 === 0 || x.len >= 4)) return;
      const c = chordAtStep(sec, x.n.bar, x.n.step); if (c.pcs.includes(x.pc)) return;
      if (x.hook || ends.has(i)) {
        const p0 = x.n.bar * 16 + c.s, p1 = p0 + c.l, base = c.kind === 'dia' ? scaleChord(T, mode, c.deg, 'tri') : null;
        const tries = base ? ['tri', '7', '9', 'add9', '6', 'sus2', 'sus4', '7sus4'].map(e => scaleChord(T, mode, c.deg, e)) : [];
        for (const c2 of tries) if (c2 && c2.pcs.includes(x.pc) && harmViol(c2, mel, p0, p1) < harmViol(c, mel, p0, p1) && !harmClash(c2, base.pcs, mel, p0, p1)) {
          const keep = { s: c.s, l: c.l, ped: c.ped, bass: c2.pcs.includes(c.bass) ? c.bass : c2.root, hinted: c.hinted }; for (const k in c) delete c[k]; Object.assign(c, c2, keep); extended++; break; }
        return;
      }
      const pv = mel[i - 1], nx = mel[i + 1]; let best = null;
      for (const d of [1, -1, 2, -2]) {
        const deg = x.n.deg + d, m = leadMidi(song, Object.assign({}, x.n, { deg })); if (!c.pcs.includes(mod(m, 12)) || m < 53 || m > 87) continue;
        const cost = Math.abs(d) + 0.5 * ((pv ? Math.abs(deg - pv.n.deg) : 0) + (nx ? Math.abs(nx.n.deg - deg) : 0)); if (!best || cost < best.cost) best = { deg, cost };
      }
      if (best) { x.n.deg = best.deg; x.pc = mod(leadMidi(song, x.n), 12); fixed++; }
    });
    return { fixed, extended };
  }
  // 強拍和弦音比例（含延伸音）；resolved = 非和弦音但下一個音級進到和弦音（倚音／經過音）
  function melodyConsonance(song, secs) {
    let strong = 0, ct = 0, res = 0;
    for (const sec of secs || song.sections) { if (!sec.harm) continue; const mel = melInfo(song, sec);
      mel.forEach((x, i) => { if (!(x.pos % 8 === 0 || x.len >= 4)) return; strong++; const c = chordAtStep(sec, x.n.bar, x.n.step);
        if (c.pcs.includes(x.pc)) { ct++; return; } const nx = mel[i + 1]; if (nx && Math.abs(leadMidi(song, nx.n) - leadMidi(song, x.n)) <= 2 && chordAtStep(sec, nx.n.bar, nx.n.step).pcs.includes(nx.pc)) res++; }); }
    return { strong, chordTone: ct, resolved: res, rate: strong ? ct / strong : 1, rateResolved: strong ? (ct + res) / strong : 1 };
  }
  // ---------- 配置（voicing）：最小移動的聲部進行 ----------
  function closedVoicings(pcs, lo, hi) {
    const uq = pcs.filter((p, i) => pcs.indexOf(p) === i);
    if (uq.length < pcs.length) { const out = []; for (const v of closedVoicings(uq, lo, hi)) { if (v[0] + 12 <= hi) out.push(v.concat([v[0] + 12])); if (v[v.length - 1] - 12 >= lo) out.push([v[v.length - 1] - 12].concat(v)); } return out; } // 重複音：八度重疊（四聲部的三和弦）
    pcs = pcs.slice().sort((a, b) => mod(a - pcs[0], 12) - mod(b - pcs[0], 12)); // 音級依音高排序 → 真正的密集配置
    const out = [], n = pcs.length;
    for (let r = 0; r < n; r++) { const ord = pcs.slice(r).concat(pcs.slice(0, r));
      for (let base = lo; base <= hi; base++) { if (mod(base, 12) !== ord[0]) continue; const v = [base];
        for (let k = 1; k < n; k++) { let m = v[k - 1] + 1; while (mod(m, 12) !== ord[k]) m++; v.push(m); }
        if (v[n - 1] <= hi) out.push(v); } }
    return out;
  }
  function voiceMove(a, b) {
    if (!a || !a.length) return b.map(() => 0);
    if (a.length === b.length) { const x = a.slice().sort((p, q) => p - q), y = b.slice().sort((p, q) => p - q); return y.map((m, i) => Math.abs(m - x[i])); }
    return b.map(m => Math.min(...a.map(p => Math.abs(p - m))));
  }
  function bestVoicing(pcs, prev, lo, hi, center) {
    let best = null, bc = Infinity;
    for (const v of closedVoicings(pcs, lo, hi)) {
      const mv = voiceMove(prev, v), c0 = v.reduce((s, m) => s + m, 0) / v.length;
      let cost = prev ? mv.reduce((s, x) => s + x, 0) + 0.6 * Math.max(...mv) + 0.3 * Math.max(0, Math.abs(c0 - center) - 4) : Math.abs(c0 - center);
      for (let i = 1; i < v.length; i++) if (v[i] - v[i - 1] === 1) cost += 2.5;
      if (v[0] < 55 && v[1] - v[0] < 4) cost += 2;
      if (cost < bc) { bc = cost; best = v; }
    }
    return best || pcs.map(p => lo + mod(p - lo, 12)).sort((a, b) => a - b);
  }
  const nearestIn = (pc, ref, lo, hi) => { let best = null; for (let m = lo; m <= hi; m++) if (mod(m, 12) === mod(pc, 12) && (best == null || Math.abs(m - ref) < Math.abs(best - ref))) best = m; return best; };
  const bassNear = (pc, ref) => { let best = null, bc = 1e9; for (let m = 28; m <= 50; m++) if (mod(m, 12) === mod(pc, 12)) { const c = Math.abs(m - ref) + 0.6 * Math.max(0, Math.abs(m - 38) - 3); if (c < bc) { bc = c; best = m; } } return best; }; // 貝斯：靠近前一音，並拉回中音域
  const rhTones = c => (c.iv.length >= 4 && c.q !== 'dim7' ? c.iv.slice(1) : c.iv).map(x => mod(c.root + x, 12));
  const strTones = c => (c.iv.length === 3 ? [0, c.iv[1], c.iv[2], 0] : c.iv.length === 4 ? c.iv : c.iv.slice(1)).map(x => mod(c.root + x, 12));
  // 為單一和弦配置：鋼琴右手 3–4 音（53–74）、左手低音＋五度／八度（36–50，低音區不放三度）、弦樂 4 聲部、大提琴、貝斯
  function voiceOne(c, pv) {
    pv = pv || {}; const bpc = c.ped != null ? c.ped : c.bass;
    const rh = bestVoicing(rhTones(c), pv.rh, 53, 74, 63), str = bestVoicing(strTones(c), pv.str, 55, 81, 67);
    const lb = nearestIn(bpc, pv.lh ? pv.lh[0] : 41, 36, 47), lh = [lb];
    const second = bpc === c.root && c.ped == null && c.iv.includes(7) ? lb + 7 : lb + 12; if (second < rh[0] - 1) lh.push(second);
    return { rh, lh, str, cello: nearestIn(bpc, pv.cello || 48, 43, 55), bass: bassNear(bpc, pv.bass || 38) };
  }
  // 全曲：轉位（級進低音線）→ 配置
  function voiceSong(song, R, HS) {
    const flat = []; song.sections.forEach((sec, si) => sec.harm.forEach((hs, b) => hs.forEach(c => flat.push({ c, sec, b, si }))));
    let prevB = null;
    flat.forEach((x, i) => {
      const c = x.c, nx = flat[i + 1], sec = x.sec;
      if (c.ped != null) { prevB = c.ped; return; }
      if (c.hinted) { prevB = c.bass; return; }
      const can = R() < HS.inv && !(sec.final && x.b >= sec.bars - 2) && !(x.b === 0 && c.s === 0) && !/sus/.test(c.q) && c.kind !== 'pass' && x.sec.type !== 'outro';
      if (can && prevB != null) {
        const opts = [c.root]; if (c.iv[1] === 3 || c.iv[1] === 4) opts.push(mod(c.root + c.iv[1], 12)); if (c.iv.includes(10)) opts.push(mod(c.root + 10, 12));
        let best = c.root, bc = Infinity;
        for (const o of opts) { const cost = dist12(prevB, o) + (nx ? dist12(o, nx.c.ped != null ? nx.c.ped : nx.c.root) : 0) - (o === c.root ? 1.2 : 0) + (o === mod(c.root + 10, 12) ? 0.6 : 0); if (cost < bc) { bc = cost; best = o; } }
        c.bass = best;
      }
      prevB = c.bass;
    });
    let pv = null; for (const x of flat) { x.c.v = voiceOne(x.c, pv); pv = x.c.v; }
  }
  // 副旋律（obbligato）：填在主旋律的長音與休止裡，走和弦音、反向進行、避開與主旋律的小二度
  function counterLine(song, sec) {
    const mel = melInfo(song, sec).sort((a, b) => a.pos - b.pos), out = [], total = sec.bars * 16, fast = song.style === 'us' || song.style === 'kpop'; let last = null, dir = -1;
    for (let i = 0; i < mel.length; i++) {
      const x = mel[i], nP = mel[i + 1] ? mel[i + 1].pos : total, g0 = x.len >= 6 ? x.pos + 4 : x.pos + x.len, g1 = Math.min(nP, total); if (g1 - g0 < 4) continue;
      const L = leadMidi(song, x.n), step = fast || g1 - g0 < 8 ? 2 : 4, n = Math.min(4, Math.floor((g1 - g0) / step));
      const lo = L <= 72 ? Math.max(62, L + 3) : Math.max(55, L - 12), hi = L <= 72 ? Math.min(86, L + 12) : L - 3;
      const pd = mel[i - 1] ? Math.sign(L - leadMidi(song, mel[i - 1].n)) : 1; dir = pd ? -pd : -dir;
      for (let k = 0; k < n; k++) {
        const pos = g0 + k * step, c = chordAtStep(sec, pos >> 4, pos & 15), sounding = x.pos + x.len > pos, ref = last == null ? (lo + hi) / 2 : last + dir * 2.5; let best = null;
        for (let m = lo; m <= hi; m++) { if (!c.pcs.includes(mod(m, 12)) || mod(m, 12) === x.pc || (sounding && dist12(m, L) <= 2)) continue; if (best == null || Math.abs(m - ref) < Math.abs(best - ref)) best = m; }
        if (best == null) continue;
        out.push({ bar: pos >> 4, step: pos & 15, len: k === n - 1 ? Math.min(g1 - pos, 8) : step, midi: best, vel: k === n - 1 ? 0.8 : 0.65 + 0.1 * (k % 2) }); last = best;
      }
    }
    return out.filter(e => e.step + e.len <= 16 || true);
  }
  // 由作曲結果完成和聲與配置（composeSongGen 會呼叫）
  function harmonizeSong(song, R) {
    const HS = HARM_STYLE[song.style] || HARM_STYLE.folk;
    song.sections.forEach((s, si) => colorSection(song, si, HS, R));
    const fi = song.sections.findIndex(s => s.final);
    if (song.lift && fi > 0) { // 升 Key 前一小節的後半：新調的屬七（旋律允許時）；否則直接轉調（鼓過門＋鈸）
      const pv = song.sections[fi - 1], hs = pv.harm[pv.bars - 1], T0 = song.key.tonic, d = liftDom(T0 + song.lift), base = scaleChord(T0, song.key.mode, pv.chords[pv.bars - 1], 'tri'), p0 = (pv.bars - 1) * 16;
      if (harmFits(d, base, melInfo(song, pv), p0 + 8, p0 + 16)) { if (hs.length === 2) hs[1] = Object.assign(d, { s: 8, l: 8 }); else { hs[0].l = 8; hs.push(Object.assign(d, { s: 8, l: 8 })); } song.liftPivot = true; }
    }
    let fixed = 0, extended = 0; for (const s of song.sections) { const r = repairSection(song, s); fixed += r.fixed; extended += r.extended; }
    voiceSong(song, R, HS);
    for (const s of song.sections) s.counter = s.type === 'chorus' || s.type === 'bridge' ? counterLine(song, s) : [];
    song.harmStats = Object.assign(melodyConsonance(song), { fixed, extended });
  }

  // ---------- 編曲：各風格、各段落的層次（逐小節，輪替 2–4 種變化） ----------
  function arrangeBar(style, type, dyn, o = {}) {
    const secBar = o.secBar || 0, bars = o.bars || 8, si = o.si || 0, fin = !!o.final, half = secBar >= Math.floor(bars / 2), k4 = Math.floor(secBar / 4) + si;
    const R = l => l[k4 % l.length], mid = dyn > 0.45, hi = dyn > 0.68, isCh = type === 'chorus';
    const A = { piano: null, gtr: null, cgtr: null, egtr: null, bass: null, strings: null, strLvl: 0, drums: null, lead: ['piano'], leadDouble: null, counter: null, arp: null, strHigh: false, build: type === 'pre', duck: false, half: false };
    switch (style) {
      case 'rnb':
        if (type === 'intro') A.piano = half ? 'alberti' : 'broken';
        else if (type === 'verse' || type === 'inter') { A.piano = R(['rnb', 'broken', 'rnbB']); A.gtr = half && mid ? 'pick' : null; A.bass = half ? R(['rnb', 'sync16']) : null; A.drums = half ? R(['rnbLight', 'rnbLight2']) : 'xstick'; }
        else if (type === 'pre') { A.piano = 'offblock'; A.strings = 'swell'; A.strLvl = 0.5; A.cgtr = 'mute8'; A.bass = 'rnb'; A.drums = 'rnb'; }
        else if (isCh) { A.piano = R(['rnb', 'ballad8']); A.gtr = R(['strumA', 'strumC']); A.egtr = hi ? 'powerHold' : null; A.strings = 'pad'; A.strLvl = 0.7; A.bass = R(['sync16', 'rnb']); A.drums = R(['rnb', 'rnb2']); A.counter = 'strings'; A.lead = ['piano', 'strings']; }
        else if (type === 'bridge') { A.piano = R(['block', 'broken']); A.strings = 'pad'; A.strLvl = 0.55; A.bass = 'whole'; A.drums = mid ? 'half' : null; A.half = true; A.counter = 'strings'; }
        else if (type === 'outro') A.piano = half ? 'block' : 'broken';
        break;
      case 'folk':
        if (type === 'intro') { A.gtr = 'travis'; A.lead = ['aguitar']; }
        else if (type === 'verse' || type === 'inter') { A.gtr = R(['travis', 'pick']); A.bass = half ? 'root5' : null; A.drums = half && mid ? 'brush' : null; }
        else if (type === 'pre') { A.gtr = 'mute8'; A.piano = 'broken'; A.strings = 'swell'; A.strLvl = 0.45; A.bass = 'root5'; A.drums = 'brush'; }
        else if (isCh) { A.gtr = R(['strumA', 'strumB']); A.piano = R(['ballad8', 'block']); A.strings = 'pad'; A.strLvl = 0.6; A.bass = R(['root5', 'walk']); A.drums = R(['ballad', 'ballad2']); A.counter = 'strings'; }
        else if (type === 'bridge') { A.piano = 'block'; A.gtr = 'pick'; A.strings = 'pad'; A.strLvl = 0.5; A.bass = 'whole'; A.drums = mid ? 'half' : null; A.half = true; A.counter = 'strings'; }
        else if (type === 'outro') A.piano = half ? 'block' : 'broken';
        break;
      case 'power':
        if (type === 'intro') A.piano = half ? 'alberti' : 'broken';
        else if (type === 'verse' || type === 'inter') { A.piano = R(['ballad8', 'broken']); A.bass = half ? 'ballad' : null; A.drums = half ? 'xstick' : null; }
        else if (type === 'pre') { A.piano = 'pulse8'; A.strings = 'swell'; A.strLvl = 0.6; A.egtr = mid ? 'mute8E' : null; A.bass = 'eighth'; A.drums = 'ballad'; }
        else if (isCh) { A.piano = R(['pulse8', 'ballad8']); A.egtr = R(['power8', 'powerHold']); A.gtr = 'strumA'; A.strings = 'pad'; A.strLvl = 0.85; A.bass = R(['oct8', 'eighth']); A.drums = R(['power', 'power2']); A.counter = 'strings'; A.duck = true; A.lead = ['piano', 'strings']; }
        else if (type === 'bridge') { A.piano = 'block'; A.strings = 'pad'; A.strLvl = 0.6; A.bass = 'whole'; A.drums = 'half'; A.egtr = hi ? 'powerHold' : null; A.half = true; A.counter = 'strings'; }
        else if (type === 'outro') A.piano = half ? 'block' : 'broken';
        break;
      case 'lyric':
        if (type === 'intro') A.piano = half ? 'alberti' : 'broken';
        else if (type === 'verse' || type === 'inter') { A.piano = R(['alberti', 'broken']); A.strings = half ? 'pad' : null; A.strLvl = 0.25; A.bass = half ? 'whole' : null; A.drums = half && mid ? 'brush' : null; }
        else if (type === 'pre') { A.piano = 'ballad8'; A.strings = 'swell'; A.strLvl = 0.55; A.bass = 'root5'; A.drums = 'brush'; }
        else if (isCh) { A.piano = R(['ballad8', 'pulse8']); A.strings = 'pad'; A.strLvl = 0.8; A.gtr = mid ? 'strumC' : null; A.egtr = dyn > 0.8 ? 'powerHold' : null; A.bass = R(['root5', 'walk']); A.drums = R(['ballad', 'ballad2']); A.counter = 'strings'; A.lead = ['piano', 'strings']; }
        else if (type === 'bridge') { A.piano = 'block'; A.strings = 'pad'; A.strLvl = 0.55; A.bass = 'whole'; A.drums = mid ? 'half' : null; A.half = true; A.counter = 'strings'; }
        else if (type === 'outro') A.piano = half ? 'block' : 'broken';
        break;
      case 'us':
        if (type === 'intro') A.gtr = 'strumA';
        else if (type === 'verse' || type === 'inter') { A.gtr = R(['strumB', 'mute8']); A.bass = half ? 'eighth' : null; A.drums = R(['pop4l', 'xstick']); }
        else if (type === 'pre') { A.gtr = 'mute8'; A.piano = 'pulse8'; A.strings = 'swell'; A.strLvl = 0.35; A.bass = 'eighth'; A.drums = 'pop4'; }
        else if (isCh) { A.egtr = R(['power8', 'oct8']); A.gtr = 'strumA'; A.piano = 'stab'; A.bass = R(['oct8', 'eighth']); A.drums = R(['rock', 'rock2']); A.strings = 'pad'; A.strLvl = 0.4; A.counter = 'cguitar'; A.duck = true; A.lead = ['piano', 'cguitar']; }
        else if (type === 'bridge') { A.piano = 'block'; A.strings = 'pad'; A.strLvl = 0.4; A.egtr = 'powerHold'; A.bass = 'whole'; A.drums = 'half'; A.half = true; A.counter = 'cguitar'; }
        else if (type === 'outro') A.piano = half ? 'block' : 'broken';
        break;
      case 'kpop':
        if (type === 'intro') A.piano = half ? 'alberti' : 'broken';
        else if (type === 'verse' || type === 'inter') { A.cgtr = 'mute16'; A.piano = 'offblock'; A.bass = half ? 'kpop' : null; A.drums = R(['kpopL', 'xstick']); }
        else if (type === 'pre') { A.strings = 'pizz'; A.strLvl = 0.5; A.piano = 'pulse8'; A.bass = 'eighth'; A.drums = 'pop4'; A.cgtr = 'mute16'; }
        else if (isCh) { A.piano = 'stab'; A.cgtr = R(['mute16', 'arpE']); A.egtr = mid ? 'powerHold' : null; A.strings = R(['pizz', 'pad']); A.strLvl = 0.5; A.bass = R(['kpop', 'sync16']); A.drums = R(['kpop', 'kpop2']); A.counter = 'strings'; A.duck = true; A.lead = ['piano', 'cguitar']; }
        else if (type === 'bridge') { A.piano = 'broken'; A.strings = 'pad'; A.strLvl = 0.5; A.bass = 'ballad'; A.drums = 'half'; A.half = true; A.counter = 'strings'; }
        else if (type === 'outro') A.piano = half ? 'block' : 'broken';
        break;
    }
    if (isCh && fin) { // 最後副歌：全部 + 八度重疊主旋律 + 高八度弦樂 + 琶音
      A.leadDouble = style === 'power' ? 'oguitar' : 'strings'; A.strHigh = true; A.arp = style === 'folk' ? null : 'arp16'; if (!A.strings) { A.strings = 'pad'; A.strLvl = 0.5; }
      if (style === 'power') A.egtr = 'power8'; else if (!A.egtr) A.egtr = 'powerHold'; if (!A.gtr && (style === 'lyric' || style === 'rnb')) A.gtr = 'strumC';
    }
    if (type === 'inter') { A.lead = []; A.counter = null; }
    if (type === 'intro' || type === 'outro') { A.drums = null; A.egtr = null; A.cgtr = null; A.bass = null; A.strings = null; A.counter = null; }
    return A;
  }
  const arrange = (style, type, dyn, final) => arrangeBar(style, type, dyn, { final, secBar: 0, bars: 8, si: 0 });
  const LAYERS = ['piano', 'gtr', 'cgtr', 'egtr', 'bass', 'strings', 'drums', 'counter', 'arp', 'leadDouble'];
  const layerCount = A => LAYERS.filter(k => A[k]).length + (A.lead && A.lead.length ? 1 : 0);
  const sectionDyn = (song, sec, mic = 0.5) => clamp(0.5 * SECTION_LEVEL[sec.type] + 0.5 * (0.6 * mic + 0.4 * song.intensity) + (sec.final ? 0.08 : 0) + (sec.type === 'chorus' ? 0.05 : 0), 0, 1);
  // 鼓組節奏型（「9..5」= 力度 0–9）
  const DRUM_SRC = {
    xstick: { kick: '8.......5.......', stick: '....6.......6...', hatp: '..3...3...3...3.' },
    brush: { kick: '6.......4.......', stick: '....4.......4...', hatp: '4.2.4.2.4.2.4.2.' },
    ballad: { kick: '9......48.5.....', snare: '....9.......9...', hat: '5.3.5.3.5.3.5.3.' },
    ballad2: { kick: '9.......8..5....', snare: '....9.......9...', hat: '5.3.5.3.5.3.5.3.', hatO: '..............4.' },
    rnbLight: { kick: '8......6..6.....', stick: '....7.......7...', hat: '4.3.4.3.4.3.4.3.' },
    rnbLight2: { kick: '8..5......6.....', stick: '....7.......7..2', hat: '4343434343434343' },
    rnb: { kick: '9......7..8.....', snare: '....9..2....9..3', hat: '6464646464646464' },
    rnb2: { kick: '9..6......8..6..', snare: '....9.2.....9.2.', hat: '6464646464646.6.', hatO: '..............5.' },
    pop4l: { kick: '8.......8.......', stick: '....6.......6...', hat: '4.4.4.4.4.4.4.4.' },
    pop4: { kick: '9...9...9...9...', snare: '....9.......9...', clap: '....6.......6...', hat: '4.6.4.6.4.6.4.6.', hatO: '..............5.' },
    rock: { kick: '9.....7.9.7.....', snare: '....9.......9...', hat: '7.5.7.5.7.5.7.5.' },
    rock2: { kick: '9.7...7.9.....7.', snare: '....9.......9..4', hat: '7.5.7.5.7.5.7.5.', hatO: '......5.........' },
    kpopL: { kick: '9.......9..5....', stick: '....7.......7...', hat: '5.4.5.4.5.4.5.4.' },
    kpop: { kick: '9.....8.9..6....', snare: '....9.......9...', clap: '....8.......8...', hat: '6464646464646464', hatO: '..............6.' },
    kpop2: { kick: '9..7..8...9.....', snare: '....9.......9...', clap: '....8.......8..5', hat: '646464.464646464', hatO: '......6.......6.' },
    power: { kick: '9.......9.7.....', snare: '....9.......9...', ride: '6.4.6.4.6.4.6.4.' },
    power2: { kick: '9.7.....9.7...5.', snare: '....9.......9...', ride: '6.4.6.4.6.4.6.4.', hatO: '..............5.' },
    half: { kick: '9.........7.....', snare: '........9.......', hat: '5.4.5.4.5.4.5.4.' },
    half2: { kick: '9.....5...7.....', snare: '........9.....3.', hat: '5.4.5.4.5.4.5.4.', hatO: '......4.........' }
  };
  const DRUM_PAT = {}; for (const k in DRUM_SRC) { DRUM_PAT[k] = {}; for (const d in DRUM_SRC[k]) DRUM_PAT[k][d] = Array.from(DRUM_SRC[k][d]).map(ch => ch === '.' ? 0 : (+ch) / 9); }
  const STRUM = {
    strumA: [[0, 'D', 1], [4, 'D', 0.7], [6, 'U', 0.55], [10, 'U', 0.55], [12, 'D', 0.75], [14, 'U', 0.5]],
    strumB: [[0, 'D', 1], [2, 'U', 0.4], [4, 'X', 0.55], [6, 'U', 0.5], [8, 'D', 0.85], [10, 'U', 0.45], [12, 'X', 0.6], [14, 'U', 0.5]],
    strumC: [[0, 'D', 1], [3, 'U', 0.45], [6, 'D', 0.6], [8, 'D', 0.8], [11, 'U', 0.45], [14, 'U', 0.55]],
    mute8: [[0, 'X', 0.8], [2, 'X', 0.5], [4, 'X', 0.65], [6, 'X', 0.5], [8, 'X', 0.75], [10, 'X', 0.5], [12, 'X', 0.65], [14, 'X', 0.55]]
  };
  function gtrVoicing(c) { // 吉他六弦式的開放配置（最低音 = 低音／斜線和弦的低音）
    const b = c.ped != null ? c.ped : c.bass, r = 40 + mod(b - 40, 12), out = [r];
    for (let m = r + 5; m <= r + 24 && out.length < 6; m++) if (c.pcs.includes(mod(m, 12)) && m - out[out.length - 1] >= 3) out.push(m);
    return out;
  }
  // 一小節的所有音符事件（瀏覽器排程與 Node 測試共用）
  // o: { dyn, intensity, pivot:[pcs], noDrums, forceDrums, djFill }
  function barEvents(song, lb, o = {}) {
    const { sec, secBar } = sectionAt(song, lb), si = song.sections.indexOf(sec), type = sec.type, bars = sec.bars;
    const dyn = o.dyn != null ? o.dyn : sectionDyn(song, sec, o.intensity == null ? 0.5 : o.intensity);
    const A = arrangeBar(song.style, type, dyn, { final: sec.final, secBar, bars, si });
    if (o.forceDrums) A.drums = arrangeBar(song.style, 'chorus', 0.8, {}).drums || 'pop4';
    if (o.noDrums) A.drums = null;
    const R = rng32(((song.rseed || 1) * 31 + lb * 7919 + 17) >>> 0), hv = () => 0.92 + 0.16 * R(), E = [], add = e => { E.push(e); return e; };
    const key = { tonic: mod(song.key.tonic + (sec.lift || 0), 12), mode: song.key.mode };
    let chords = sec.harm[secBar];
    if (o.pivot) { const pc = mkChord(o.pivot[0], [0, 4, 7], 'pivot'); pc.v = voiceOne(pc, chords[0].v); chords = [Object.assign(pc, { s: 0, l: 16 })]; }
    const at = s => { let c = chords[0]; for (const h of chords) if (s >= h.s) c = h; return c; };
    const nextSec = song.sections[si + 1], lastBar = secBar === bars - 1, nextType = nextSec ? nextSec.type : null;
    const nextChord = secBar + 1 < bars ? sec.harm[secBar + 1][0] : nextSec ? nextSec.harm[0][0] : null;
    let V = 0.55 + 0.45 * dyn; if (type === 'outro') V *= 1 - 0.45 * secBar / bars;
    const leadOn = A.lead.length > 0 && sec.mel.some(n => n.bar === secBar);
    // —— 鋼琴 ——
    const P = (m, s, d, v, x) => add(Object.assign({ i: 'piano', m, s, d, v: v * V * hv(), bus: 'keys', voice: 'pad', rel: 0.45, pan: m < 55 ? -0.15 : 0.15, layer: 'piano' }, x));
    const chordP = (rh, s, d, v, roll, x) => rh.forEach((m, k) => P(m, s, d * (0.94 + 0.1 * R()), v * (k === rh.length - 1 ? 1.06 : 0.9) * (leadOn ? 0.88 : 1), Object.assign({ o: roll ? k * 0.014 : k * 0.003 }, x)));
    const piano = (name, c, s0, L, alt) => {
      const { lh, rh } = c.v, b = lh[0], b2 = lh[1] != null ? lh[1] : b + 12, top = rh[rh.length - 1], end = s0 + L;
      switch (name) {
        case 'broken': { const seq = alt ? [b, b2, rh[0], top, rh[1], rh[Math.max(0, rh.length - 2)], rh[0], b2] : [b, b2, rh[0], rh[1], rh[2] || top, top, rh[1], rh[0]];
          for (let k = 0; k < L / 2; k++) { const s = s0 + 2 * k; P(seq[k % 8], s, Math.min(end - s + 1, 12), k === 0 ? 0.6 : k === 4 ? 0.46 : 0.36); } break; } // 延音踏板：撐到和弦結束
        case 'alberti': { P(b, s0, L + 0.5, 0.55); if (L >= 16) P(b2, s0 + 8, 8.5, 0.4); const al = [rh[0], top, rh[1], top]; for (let k = 0; k < L / 2; k++) P(al[k % 4], s0 + 2 * k, 2.4, k % 2 ? 0.3 : 0.38); break; }
        case 'ballad8': P(b, s0, L + 0.5, 0.6); if (L > 4) P(b2, s0 + 4, L - 4, 0.34); chordP(rh, s0, 4, 0.5);
          for (let s = 2; s < L; s += 2) if (s !== 4 || R() < 0.5) chordP(rh.slice(-2), s0 + s, 2, s % 8 === 0 ? 0.42 : 0.28); break;
        case 'rnb': chordP(rh, s0, 3, 0.55); for (const [st, d, v, g] of [[3, 1, 0.2, 1], [6, 2, 0.45], [10, 2, 0.42], [13, 1, 0.18, 1], [14, 2, 0.4]]) if (st < L) chordP(g ? rh.slice(-2) : rh, s0 + st, d, v);
          P(b, s0, Math.min(6, L), 0.55); if (L > 6) P(b + 12 < rh[0] ? b + 12 : b, s0 + 6, 2, 0.3); if (L > 10) P(b, s0 + 10, 4, 0.45); break;
        case 'rnbB': for (const [st, d, v, g] of [[0, 2, 0.5], [2, 1, 0.2, 1], [4, 3, 0.45], [7, 1, 0.2, 1], [8, 2, 0.5], [11, 3, 0.42], [14, 2, 0.35]]) if (st < L) chordP(g ? rh.slice(-2) : rh, s0 + st, d, v);
          P(b, s0, 4, 0.55); if (L > 7) P(b2, s0 + 7, 3, 0.35); if (L > 11) P(b, s0 + 11, 5, 0.4); break;
        case 'offblock': P(b, s0, Math.min(8, L), 0.55); if (L > 8) P(b2, s0 + 8, 8, 0.4); for (const st of [2, 6, 10, 14]) if (st < L) chordP(rh, s0 + st, 1.6, 0.42); break;
        case 'block': P(b, s0, L + 0.5, 0.55); if (lh[1] != null) P(lh[1], s0, L + 0.5, 0.38); chordP(rh, s0, Math.min(8, L) + 0.5, 0.5, true); if (L > 8) chordP(rh, s0 + 8, 8.5, 0.36); break;
        case 'pulse8': P(b, s0, Math.min(8, L), 0.6); P(b - 12 >= 33 ? b - 12 : b2, s0, Math.min(8, L), 0.38); if (L > 8) P(b, s0 + 8, 8, 0.5); for (let s = 0; s < L; s += 2) chordP(rh, s0 + s, 2, s % 8 === 0 ? 0.48 : 0.32); break;
        case 'stab': for (const [st, v] of [[0, 0.6], [3, 0.42], [6, 0.48], [8, 0.55], [11, 0.42], [14, 0.4]]) if (st < L) chordP(rh, s0 + st, 1.5, v); P(b, s0, 4, 0.5); if (L > 8) P(b, s0 + 8, 4, 0.45); break;
        case 'sustain': P(b, s0, L + 8, 0.5); if (lh[1] != null) P(lh[1], s0, L + 8, 0.38); chordP(rh, s0, L + 10, 0.45, true); break;
      }
    };
    if (A.piano) {
      const nm = type === 'outro' && lastBar ? 'sustain' : A.piano;
      for (const c of chords) piano(nm, c, c.s, c.l, secBar % 2 === 1);
    }
    if (A.arp === 'arp16') { const c0 = chords[0]; for (let s = 0; s < 16; s++) { const c = at(s), hiN = c.v.rh.map(m => m + 12), seq = hiN.concat(hiN.slice(1, -1).reverse()); P(seq[s % seq.length], s, 1.6, s % 4 === 0 ? 0.28 : 0.2, { bus: 'arp', voice: 'arp', layer: 'arp', pan: s % 2 ? 0.35 : -0.05 }); } void c0; }
    // —— 吉他 ——
    const G = (id, m, s, d, v, x) => add(Object.assign({ i: id, m, s, d, v: v * V * hv(), bus: 'gtr', voice: 'arp', pan: id === 'aguitar' ? -0.35 : id === 'cguitar' ? 0.38 : 0, rel: 0.14, layer: id === 'aguitar' ? 'gtr' : id === 'cguitar' ? 'cgtr' : 'egtr' }, x));
    const strumPat = (pat, id) => pat.forEach(([s, dir, v], k) => { const c = at(s), gv = gtrVoicing(c), nxt = (pat[k + 1] || [16])[0];
      const strs = dir === 'D' ? gv : dir === 'U' ? gv.slice(-4).reverse() : gv.slice(0, 3);
      strs.forEach((m, j) => G(id, m, s, dir === 'X' ? 0.6 : nxt - s + 0.3, v * 0.62 * (dir === 'U' ? 0.8 : 1), { o: j * (dir === 'U' ? 0.008 : 0.011), rel: dir === 'X' ? 0.04 : 0.12 })); });
    if (A.gtr) {
      if (STRUM[A.gtr]) strumPat(STRUM[A.gtr], 'aguitar');
      else if (A.gtr === 'travis') for (const [s, idx, v] of [[0, 0, 0.7], [0, 5, 0.45], [2, 4, 0.38], [4, 2, 0.5], [6, 3, 0.38], [8, 1, 0.6], [10, 5, 0.4], [12, 2, 0.5], [14, 4, 0.36]]) { const gv = gtrVoicing(at(s)); G('aguitar', gv[Math.min(idx, gv.length - 1)], s, 5, v, { rel: 0.3 }); }
      else if (A.gtr === 'pick') { const seq = [0, 3, 1, 4, 2, 3, 1, 5]; for (let k = 0; k < 8; k++) { const gv = gtrVoicing(at(2 * k)); G('aguitar', gv[Math.min(seq[(k + (secBar % 2) * 2) % 8], gv.length - 1)], 2 * k, 6, k % 2 ? 0.5 : 0.64, { rel: 0.3 }); } }
    }
    if (A.cgtr === 'mute8') strumPat(STRUM.mute8, 'cguitar');
    else if (A.cgtr === 'mute16') for (const s of [0, 2, 3, 4, 6, 8, 10, 11, 12, 14]) { const c = at(s), b = c.v.bass + 24, f = c.iv.includes(7) ? b + 7 : b + 12, seq = [b, b, f, b + 12]; G('cguitar', seq[s % 4], s, 0.5, s % 4 === 0 ? 0.75 : 0.5, { rel: 0.04 }); }
    else if (A.cgtr === 'arpE') for (let s = 0; s < 16; s++) { const c = at(s), n = c.v.rh.map(m => m + 12); G('cguitar', n[(s + (s >> 2)) % n.length], s, 1.5, s % 4 === 0 ? 0.5 : 0.36, { bus: 'arp', rel: 0.1 }); }
    if (A.egtr) {
      const pw = c => { const r = 40 + mod((c.ped != null ? c.ped : c.bass) - 40, 12); return [r, r + 7, r + 12]; };
      if (A.egtr === 'power8') for (let s = 0; s < 16; s += 2) { const acc = s === 0 || s === 6 || s === 8 || (secBar % 2 && s === 14); pw(at(s)).forEach((m, k) => G('dguitar', m, s, acc ? 2 : 1.1, (acc ? 0.8 : 0.5), { o: k * 0.004, pan: k === 2 ? 0.5 : -0.5, rel: 0.05 })); }
      else if (A.egtr === 'powerHold') { for (const [s, d] of [[0, 10], [10, 6]]) pw(at(s)).forEach((m, k) => G('dguitar', m, s, d, 0.62, { o: k * 0.006, pan: k === 2 ? 0.5 : -0.5, rel: 0.2 })); }
      else if (A.egtr === 'mute8E') for (let s = 0; s < 16; s += 2) pw(at(s)).slice(0, 2).forEach((m, k) => G('dguitar', m, s, 0.6, s % 8 === 0 ? 0.55 : 0.38, { pan: k ? 0.45 : -0.45, rel: 0.04 }));
      else if (A.egtr === 'oct8') for (let s = 0; s < 16; s += 2) { const c = at(s), r = 52 + mod(c.root - 52, 12), f = c.iv.includes(7) ? r + 7 : r + c.iv[1], seq = [r, f, r + 12, f]; const m = seq[(s >> 1) % 4]; G('oguitar', m, s, 1.8, s % 4 === 0 ? 0.55 : 0.42, { pan: 0.42, rel: 0.08 }); G('oguitar', m + 12, s, 1.8, 0.3, { pan: -0.42, rel: 0.08 }); }
    }
    // —— 貝斯 ——
    const Bn = (m, s, d, v) => add({ i: 'bass', m, s, d: d * 0.95, v: v * V * hv(), bus: 'bass', voice: 'bass', rel: 0.08, pan: 0, layer: 'bass' });
    if (A.bass) chords.forEach((c, ci) => {
      const b = c.v.bass, s0 = c.s, L = c.l, nc = ci + 1 < chords.length ? chords[ci + 1] : nextChord, nb = nc && nc.v ? nc.v.bass : null;
      const f = c.iv.includes(7) ? (b + 7 <= 50 ? b + 7 : b - 5) : b + 12, o = b + 12 <= 55 ? b + 12 : b;
      const ap = nb != null && nb !== b ? (Math.abs(nb - b) <= 2 ? b : nb > b ? nb - 1 : nb + 1) : f; // 經過音：半音接近下一個和弦的低音
      let name = A.bass; if (c.ped != null && (name === 'walk' || name === 'sync16' || name === 'rnb')) name = 'eighth';
      const list = [];
      switch (name) {
        case 'whole': list.push([0, L, b, 0.7]); break;
        case 'ballad': list.push([0, Math.min(8, L), b, 0.8]); if (L > 8) list.push([8, 8, R() < 0.5 ? f : b, 0.62]); break;
        case 'root5': list.push([0, 6, b, 0.85], [6, 2, b, 0.48]); if (L > 8) list.push([8, 4, f, 0.68], [12, 4, nb != null && R() < 0.6 ? ap : b, 0.58]); break;
        case 'walk': { const q = L > 8 ? [b, b + (c.iv[1] === 3 ? 3 : 4), f, ap] : [b, ap]; q.forEach((m, k) => list.push([4 * k, 3.6, m, k === 0 ? 0.85 : 0.62])); break; }
        case 'eighth': for (let s = 0; s < L; s += 2) list.push([s, 1.8, s === L - 2 && nb != null && R() < 0.5 ? ap : b, s % 8 === 0 ? 0.88 : 0.62]); break;
        case 'oct8': { const seq = [b, b, o, b, b, o, b, ap]; for (let s = 0; s < L; s += 2) list.push([s, 1.7, seq[s >> 1], s % 4 === 0 ? 0.9 : 0.6]); break; }
        case 'sync16': for (const x of [[0, 3, b, 0.9], [3, 1, b, 0.5], [6, 2, o, 0.55], [8, 2, b, 0.8], [10, 1, f, 0.5], [11, 2, b, 0.62], [14, 2, ap, 0.58]]) list.push(x); break;
        case 'rnb': for (const x of [[0, 3, b, 0.95], [6, 2, o, 0.55], [10, 3, b, 0.8], [14, 2, ap, 0.6]]) list.push(x); break;
        case 'kpop': for (const x of [[0, 2, b, 1], [3, 1, o, 0.6], [6, 2, b, 0.8], [8, 2, b, 0.9], [11, 1, o, 0.6], [14, 2, f, 0.7]]) list.push(x); break;
      }
      for (const [s, d, m, v] of list) if (s < L) Bn(clamp(m, 28, 58), s0 + s, Math.min(d, L - s), v);
    });
    // —— 弦樂 ——
    const Sx = (m, s, d, v, x) => add(Object.assign({ i: 'strings', m, s, d, v: v * V * hv(), bus: 'pad', voice: 'pad', att: 0.3, rel: 0.6, layer: 'strings' }, x));
    if (A.strings && A.strLvl > 0) {
      const lv = A.strLvl, PAN = [-0.42, -0.14, 0.14, 0.42];
      if (A.strings === 'pizz') { const st = secBar % 2 ? [0, 2, 4, 6, 8, 10, 12, 14] : [0, 3, 6, 8, 11, 14]; st.forEach((s, k) => { const sv = at(s).v.str; Sx(sv[(k * 2) % sv.length], s, 0.8, lv * 0.62, { att: 0.004, rel: 0.05, pan: PAN[(k * 2) % 4] }); Sx(sv[(k * 2 + 1) % sv.length], s, 0.8, lv * 0.5, { att: 0.004, rel: 0.05, pan: PAN[(k * 2 + 1) % 4] }); }); }
      else for (const c of chords) {
        const swell = A.strings === 'swell', v = swell ? lv * (0.32 + 0.5 * (secBar + 1) / bars) : lv * 0.5;
        c.v.str.forEach((m, k) => Sx(m, c.s, c.l + 0.5, v, swell ? { attS: c.l * 0.7, rel: 0.35, pan: PAN[k] } : { att: c.s ? 0.15 : 0.35, pan: PAN[k] }));
        if (type === 'chorus' || type === 'pre' || type === 'bridge') Sx(c.v.cello, c.s, c.l + 0.5, v * 0.85, { pan: -0.08, att: 0.25 });
        if (A.strHigh) Sx(c.v.str[c.v.str.length - 1] + 12, c.s, c.l + 0.5, lv * 0.32, { pan: 0.25, att: 0.3 });
      }
    }
    // —— 主旋律（Hook = 靈感音）與八度重疊 ——
    if (A.lead.length) {
      const lv0 = type === 'intro' || type === 'outro' ? 0.72 : 1;
      for (const n of sec.mel) if (n.bar === secBar) {
        let m = leadMidi(song, n); if (type === 'intro' && m < 64) m += 12; if (o.pivot) { let bm = m, bd = 99; for (let d = -6; d <= 6; d++) if (o.pivot.includes(mod(m + d, 12)) && Math.abs(d) < bd) { bd = Math.abs(d); bm = m + d; } m = bm; }
        const v = lv0 * n.vel * (0.78 + 0.3 * dyn) * (n.hook ? 1.06 : 1);
        A.lead.forEach((id, k) => add({ i: id, m, s: n.step, d: n.len * 0.96, v: v * (k ? 0.45 : 0.95), bus: 'lead', voice: k ? 'pad' : 'lead', mark: !k && n.hook ? 'hook' : null, att: id === 'strings' ? 0.05 : 0.003, rel: id === 'piano' ? 0.5 : 0.25, g: id === 'oguitar' ? 1.2 : 1, pan: k ? 0.18 : 0, layer: 'lead' }));
        if (A.leadDouble) add({ i: A.leadDouble, m: m + (m < 70 ? 12 : -12), s: n.step, d: n.len * 0.96, v: v * 0.42, bus: 'lead', voice: 'pad', att: 0.04, rel: 0.3, pan: -0.2, layer: 'leadDouble' });
      }
    }
    if (A.counter && sec.counter) for (const n of sec.counter) if (n.bar === secBar) add({ i: A.counter, m: n.midi, s: n.step, d: n.len, v: n.vel * (A.counter === 'strings' ? 0.42 : 0.5) * V, bus: 'arp', voice: 'arp', att: A.counter === 'strings' ? 0.08 : 0.003, rel: 0.3, pan: 0.3, layer: 'counter' });
    // —— 鼓組 ——
    const Dr = (k, s, v, x) => { if (v > 0) add(Object.assign({ i: 'drum', m: k, s, d: 1, v: clamp(v * V * (0.94 + 0.12 * R()), 0, 1.2), bus: 'drums', layer: 'drums', duck: A.duck && /kick/.test(k) }, x)); };
    const dp = A.drums && DRUM_PAT[A.drums];
    if (dp) {
      const bigFill = (lastBar && type !== 'outro' && nextType !== 'outro') || o.djFill, smallFill = !bigFill && secBar % 4 === 3 && bars > 4;
      const toChorus = nextType === 'chorus' || o.djFill, build = bigFill && toChorus && (A.build || ['power', 'kpop', 'us'].includes(song.style) || R() < 0.4);
      const cut = bigFill ? 8 : smallFill ? 12 : 16, odd = secBar % 2 === 1, preRamp = A.build ? 0.55 + 0.45 * (secBar + 1) / bars : 1;
      for (const k in dp) for (let s = 0; s < cut; s++) { let v = dp[k][s]; if (!v) continue; if (/hat/.test(k)) v *= preRamp; if (odd && k === 'hat' && s === 14 && !dp.hatO) { Dr('hatO', s, v * 0.9); continue; } Dr(k, s, v); }
      if (odd && dp.snare && !dp.snare[7]) Dr('snare', 7, 0.16); // 鬼音
      if (odd && dp.snare && !dp.snare[15] && !bigFill && !smallFill) Dr('snare', 15, 0.14);
      if (build) { Dr('kick', 8, 0.85); for (let s = 8; s < 16; s += s < 12 ? 2 : 1) Dr('snare', s, 0.3 + 0.06 * (s - 8)); Dr('hatO', 15, 0.3); }
      else if (bigFill) { Dr('kick', 8, 0.8); for (const [s, k, v] of shuffle(R, [[[8, 'snare', 0.8], [10, 'tomH', 0.8], [11, 'tomH', 0.6], [12, 'tomM', 0.8], [13, 'tomM', 0.6], [14, 'tomL', 0.85], [15, 'tomL', 0.7]], [[8, 'snare', 0.7], [9, 'snare', 0.3], [10, 'snare', 0.6], [12, 'tomH', 0.75], [13, 'tomM', 0.7], [14, 'tomL', 0.85], [15, 'kick', 0.7]]])[0]) Dr(k, s, v); }
      else if (smallFill) { if (dp.kick[12]) Dr('kick', 12, dp.kick[12]); const F = A.drums === 'xstick' || A.drums === 'brush' || A.drums === 'rnbLight' || A.drums === 'rnbLight2' ? [[14, 'stick', 0.5], [15, 'stick', 0.35]] : R() < 0.5 ? [[12, 'snare', 0.55], [13, 'snare', 0.3], [14, 'tomH', 0.6], [15, 'tomM', 0.55]] : [[12, 'snare', 0.4], [13, 'snare', 0.45], [14, 'snare', 0.55], [15, 'snare', 0.65]]; for (const [s, k, v] of F) Dr(k, s, v); }
      if (secBar === 0 && (type === 'chorus' || type === 'bridge' || (type === 'verse' && si > 1)) || (type === 'chorus' && sec.final && secBar === 4)) { Dr('crash', 0, 0.9); Dr('kick', 0, 0.6); }
    } else if (o.djFill && !o.noDrums) { for (let s = 0; s < 16; s += s < 8 ? 2 : 1) Dr('snare', s, 0.3 + 0.04 * s); }
    else if (type === 'chorus' && secBar === 0 && !o.noDrums && dyn > 0.4) Dr('crash', 0, 0.5);
    return { events: E, arr: A, chords, label: chords.map(c => chordLabel(c, key)).join(' → '), dyn, sec, secBar };
  }
  // Node 端的「離線渲染」：每段落每種樂器的音符密度（每小節事件數）
  function songEventDump(song, o = {}) {
    const rows = {}, cnt = {};
    for (let lb = 0; lb < song.totalBars; lb++) { const r = barEvents(song, lb, o), t = r.sec.final ? 'final' : r.sec.type; rows[t] = rows[t] || {}; cnt[t] = (cnt[t] || 0) + 1;
      for (const e of r.events) rows[t][e.layer] = (rows[t][e.layer] || 0) + 1; }
    for (const t in rows) for (const k in rows[t]) rows[t][k] /= cnt[t];
    return { perBar: rows, bars: cnt };
  }

  const api = { clamp, lerp, smoothstep, mod, NOTE_NAMES, noteName, freqToMidi, midiToFreq, rms, spectralCentroid, logCompress, spectralFlux,
    OnsetDetector, estimateTempo, yin, spectrumChroma, KS_MAJOR, KS_MINOR, pearson, detectKey, keyName, SCALES, inScale, quantizeToScale,
    degreeToMidi, midiToDegree, diatonicChord, voiceChord, PROGRESSIONS, motifToIntervals,
    rng32, pick, PENTA, chordToneDegs, snapDeg, RHYTHMS, endingBar, STYLES, STYLE_IDS, styleWeights, SONG_FORM, SECTION_LABEL, SECTION_LEVEL, PRE_PROG, BRIDGE_PROG, buildPhrase, buildSectionMelody, chordName,
    median, spellPc, spectralPeaks, NoteTracker, rhythmFromIOIs, makeSeed, extractSeed, seedFromNoise, SeedCapture, DEG_W, keyFitScore, fitKeys, keyDistance, chooseKey,
    FORMS, formBars, chooseForm, tSeq, tInv, tRetro, tAug, tDim, seedToHook, scoreProgression, chooseProgression, motifPhrase, composeSectionMelody, songTitle, composeSongGen, composeSong, sectionAt, leadMidi,
    arrange, DJ_TECH, DJ_IDS, planTransition, bpmAt, barsDuration, drumOwner,
    HARM_MINOR, QUAL, mkChord, scaleChord, hmDom, secDom, triSub, passDim, borChord, liftDom, chordInKey, chordLabel, HARM_STYLE, EXT, BASS_HINTS, harmViol, harmFits, colorSection, repairSection,
    melodyConsonance, melInfo, chordAtStep, closedVoicings, voiceMove, bestVoicing, voiceOne, voiceSong, counterLine, harmonizeSong, arrangeBar, LAYERS, layerCount, sectionDyn, DRUM_PAT, STRUM, gtrVoicing, barEvents, songEventDump, dist12 };
  root.MusicCore = api;
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
})(typeof self !== 'undefined' ? self : this);
