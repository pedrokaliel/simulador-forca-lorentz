"use strict";

/* =========================================================
 0. BÁSICO: UTILITÁRIOS, PERSISTÊNCIA SEGURA E TEMA
 ========================================================= */
const $ = (id) => document.getElementById(id);
const clamp = (x, a, b) => Math.min(b, Math.max(a, x));
const store = {
 get(k) {
  try {
   return localStorage.getItem(k);
  } catch (_) {
   return null;
  }
 },
 set(k, v) {
  try {
   localStorage.setItem(k, v);
  } catch (_) {}
 },
};
const reduceMotion = !!(window.matchMedia && matchMedia("(prefers-reduced-motion: reduce)").matches);
const isFirstVisit = !store.get("lorentz_seen");
const LOADING_MIN_MS = 2000;
const loadStart = performance.now();

let theme =
 store.get("lorentz_theme") ||
 (window.matchMedia && matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light");
document.documentElement.dataset.theme = theme;
const THEME_BG = { light: 0xffffff, dark: 0x0b1220 };

/* =========================================================
 1. CONSTANTES FÍSICAS E MATEMÁTICAS
 ========================================================= */
const E = 1.602176634e-19,
 ME = 9.1093837015e-31,
 MP = 1.67262192369e-27,
 C = 299792458;
const PART = {
 e: { q: -1, m: ME, n: "Elétron", hex: 0x3b82f6, sign: "−" },
 p: { q: 1, m: MP, n: "Próton", hex: 0xef4444, sign: "+" },
};

const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const sc = (a, k) => [a[0] * k, a[1] * k, a[2] * k];
const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const nrm = (a) => Math.hypot(a[0], a[1], a[2]);
const cr = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];

const PFX = [
 [-15, "f"],
 [-12, "p"],
 [-9, "n"],
 [-6, "µ"],
 [-3, "m"],
 [0, ""],
 [3, "k"],
 [6, "M"],
 [9, "G"],
];
function fmt(v, u) {
 if (v == null || !isFinite(v)) return "—";
 if (v === 0) return "0 " + u;
 const a = Math.abs(v);
 if (a < 1e-15 || a >= 1e12) return v.toExponential(2) + " " + u;
 let ch = PFX[5];
 for (const p of PFX) if (a >= Math.pow(10, p[0]) * 0.999) ch = p;
 const s = v / Math.pow(10, ch[0]);
 return s.toFixed(Math.abs(s) >= 100 ? 1 : Math.abs(s) >= 10 ? 2 : 3) + " " + ch[1] + u;
}
function fmtCompact(v, u) {
 if (v == null || !isFinite(v)) return "—";
 if (v === 0) return "0 " + u;
 const a = Math.abs(v);
 if (a < 1e-15 || a >= 1e12) return v.toExponential(1) + " " + u;
 let ch = PFX[5];
 for (const p of PFX) if (a >= Math.pow(10, p[0]) * 0.999) ch = p;
 return parseFloat((v / Math.pow(10, ch[0])).toPrecision(3)) + " " + ch[1] + u;
}
function niceNum(x) {
 if (!(x > 0)) return 1;
 const e = Math.floor(Math.log10(x)),
  f = x / Math.pow(10, e);
 return (f < 1.5 ? 1 : f < 3.5 ? 2 : f < 7.5 ? 5 : 10) * Math.pow(10, e);
}
function fmtErr(e) {
 if (e == null || !isFinite(e)) return "—";
 if (Math.abs(e) < 1e-10) return "≈ 0 %";
 return (e >= 0 ? "+" : "") + (e * 100).toPrecision(2) + " %";
}

const HELP = {
 r: "Raio da trajetória circular: r = γ·m·v⊥ / (|q|·B). Só a componente de v perpendicular a B faz a partícula curvar.",
 T: "Tempo de uma volta completa: T = 2π·γ·m / (|q|·B). No regime não relativístico não depende da velocidade.",
 f: "Frequência de cíclotron, f = 1/T. É a base do cíclotron e da ressonância magnética.",
 v: "Módulo da velocidade. A força magnética não realiza trabalho, então |v| permanece constante.",
 vpar: "Componente de v paralela a B. Não sofre força e permanece constante: é o avanço da hélice.",
 vperp: "Componente de v perpendicular a B. É ela que gira em círculo.",
 pitch: "Passo da hélice: distância percorrida ao longo de B em uma volta completa (v∥·T).",
 gamma: "Fator de Lorentz, γ = 1/√(1 − v²/c²). Perto de c a massa efetiva γm cresce e o raio aumenta.",
 KE: "Energia cinética relativística, (γ − 1)·m·c². Constante, pois a força é perpendicular a v.",
 p: "Momento linear relativístico, p = γ·m·v.",
 F: "Módulo da força de Lorentz, |F| = |q|·v⊥·B. É sempre perpendicular a v e a B.",
 a: "Aceleração a = |F| / (γ·m). Aponta para o centro da circunferência (centrípeta).",
 cmp: "Compara as fórmulas analíticas com o que a simulação mede (ω obtido pela rotação de v⊥). O erro vem do integrador numérico de Boris; para Ec, mostra o desvio em relação ao valor inicial.",
 chart: "Gráficos em função do tempo simulado. Em “Conservação”, |v| e Ec normalizados devem ficar em 1.",
};

/* =========================================================
 2. INTEGRADOR FÍSICO (Algoritmo de Boris)
 ========================================================= */
function boris(v, q, m, B, dt) {
 const k = (q * dt) / (2 * m),
  t = sc(B, k),
  t2 = dot(t, t);
 const vp = add(v, cr(v, t));
 return add(v, cr(vp, sc(t, 2 / (1 + t2))));
}

function derive(v, P) {
 const sp = nrm(v);
 const b = Math.min(0.9999, sp / C);
 const g = 1 / Math.sqrt(Math.max(1e-12, 1 - b * b));
 const Bm = nrm(P.B);
 const KE = ((g * g * b * b) / (g + 1)) * P.m * C * C;
 const p = g * P.m * sp;

 if (Bm < 1e-12)
  return {
   g, sp, Bm: 0, Bh: [0, 1, 0], vpar: sp, vperp: 0,
   T: Infinity, w: 0, r: 0, pitch: Infinity, f: 0, F: 0, acc: 0, KE, p,
  };

 const Bh = sc(P.B, 1 / Bm);
 const vpar = dot(v, Bh);
 const vperp = Math.sqrt(Math.max(0, sp * sp - vpar * vpar));
 const w = (Math.abs(P.q) * Bm) / (g * P.m);
 const T = (2 * Math.PI) / w;
 const r = (g * P.m * vperp) / (Math.abs(P.q) * Bm);
 const F = Math.abs(P.q) * vperp * Bm;
 return { g, sp, Bm, Bh, vpar, vperp, T, w, r, pitch: vpar * T, f: w / (2 * Math.PI), F, acc: F / (g * P.m), KE, p };
}

function kineticOf(vv) {
 const sp = nrm(vv);
 const b = Math.min(0.9999, sp / C);
 const g = 1 / Math.sqrt(Math.max(1e-12, 1 - b * b));
 return ((g * g * b * b) / (g + 1)) * P.m * C * C;
}

/* =========================================================
 3. ESTADO GLOBAL E PERSISTÊNCIA
 ========================================================= */
const MODB_MAX = 5;
const val = { Bx: 0.5, By: 0, Bz: 1, vx: 1e7, vy: 0, vz: 6e6 };
let kind = "e",
 ctl = {};
let speedLog = 0,
 speedMul = 1;
const disp = { trailLen: 3000, trailW: 3, trailMode: "fade", fieldOp: 0.35, fieldN: 5 };
const DISPLAY_IDS = ["cFollow", "cVec", "cLabels", "cTrail", "cField", "cRadius", "cGrid", "cScale"];
const chk = {};
DISPLAY_IDS.forEach((id) => (chk[id] = $(id)));

let P, x, v, gm, d, rate, tSim;
let sp0 = 0, ke0 = 0;
let playing = false,
 lastT = null,
 fc = 0;

function numList(str, n) {
 if (!str) return null;
 const a = str.split(",").map(Number);
 return a.length === n && a.every(Number.isFinite) ? a : null;
}
function parseHash() {
 const h = location.hash.replace(/^#/, "");
 if (!h) return null;
 const q = new URLSearchParams(h);
 const o = { k: q.get("k"), B: numList(q.get("B"), 3), v: numList(q.get("v"), 3), s: parseFloat(q.get("s")) };
 return o.k || o.B || o.v ? o : null;
}
function applyPhys(o) {
 if (!o) return;
 if (o.k && PART[o.k]) kind = o.k;
 if (o.B) ["Bx", "By", "Bz"].forEach((id, i) => (val[id] = clamp(o.B[i], -MODB_MAX, MODB_MAX)));
 if (o.v) ["vx", "vy", "vz"].forEach((id, i) => (val[id] = clamp(o.v[i], -C, C)));
 if (Number.isFinite(o.s)) speedLog = clamp(o.s, -1, 0.7);
}
let savedChips = null;
(function loadPersisted() {
 let saved = {};
 try {
  saved = JSON.parse(store.get("lorentz_state") || "{}") || {};
 } catch (_) {
  saved = {};
 }
 applyPhys(parseHash() || saved.phys);
 if (saved.disp) {
  if (Number.isFinite(saved.disp.trailLen)) disp.trailLen = clamp(saved.disp.trailLen, 200, 10000);
  if (Number.isFinite(saved.disp.trailW)) disp.trailW = clamp(saved.disp.trailW, 1, 8);
  if (saved.disp.trailMode === "solid" || saved.disp.trailMode === "fade") disp.trailMode = saved.disp.trailMode;
  if (Number.isFinite(saved.disp.fieldOp)) disp.fieldOp = clamp(saved.disp.fieldOp, 0.1, 1);
  if (Number.isFinite(saved.disp.fieldN)) disp.fieldN = clamp(Math.round(saved.disp.fieldN), 3, 9);
 }
 savedChips = saved.chips || null;
 speedMul = Math.pow(10, speedLog);
})();

function physState() {
 return { k: kind, B: [val.Bx, val.By, val.Bz], v: [val.vx, val.vy, val.vz], s: speedLog };
}
let persistTimer = null;
function persist() {
 clearTimeout(persistTimer);
 persistTimer = setTimeout(() => {
  const chips = {};
  DISPLAY_IDS.forEach((id) => (chips[id] = chk[id].checked));
  store.set("lorentz_state", JSON.stringify({ phys: physState(), disp: { ...disp }, chips }));
 }, 300);
}
function buildLink() {
 const p = physState();
 const qs = new URLSearchParams({ k: p.k, B: p.B.join(","), v: p.v.join(","), s: p.s.toFixed(2) });
 return location.href.split("#")[0] + "#" + qs.toString();
}

const MAX_TRAIL = 10000;
const MAX_TRAIL_SEGMENTS = 64;
const TRAIL_EPS = 1e-12;
const DEBUG_TRAIL = false;
let trailLimit = disp.trailLen;
let trajectorySegments = [];
let trailPointCount = 0;
let trailRegime = null;
let trailDirty = true;
let planeYInit = false;

function finitePoint(pos) {
 return Array.isArray(pos) && pos.length === 3 && pos.every(Number.isFinite);
}
function regimeFor(derived) {
 return derived && derived.Bm > TRAIL_EPS ? "magnetic" : "free";
}
function debugTrail(label) {
 if (!DEBUG_TRAIL) return;
 console.debug("[trail]", label, { segments: trajectorySegments.length, points: trailPointCount, B: d && d.Bm });
}
function enforceTrailLimit() {
 while (
  trajectorySegments.length &&
  (trailPointCount > trailLimit || trajectorySegments.length > MAX_TRAIL_SEGMENTS)
 ) {
  const first = trajectorySegments[0];
  if (first.points.length <= 1 || trajectorySegments.length > MAX_TRAIL_SEGMENTS) {
   trailPointCount -= first.points.length;
   trajectorySegments.shift();
  } else {
   first.points.shift();
   trailPointCount--;
  }
 }
 trailDirty = true;
}
function startTrailSegment(pos, reason) {
 if (!finitePoint(pos)) throw new Error(`Ponto inicial inválido (${reason})`);
 trajectorySegments.push({ points: [pos.slice()], reason, regime: trailRegime });
 trailPointCount++;
 enforceTrailLimit();
 debugTrail(`novo segmento: ${reason}`);
}
function pushTrail(pos) {
 if (!finitePoint(pos)) throw new Error("Tentativa de inserir ponto não finito no trail");
 if (!trajectorySegments.length) startTrailSegment(pos, "initial");
 trajectorySegments[trajectorySegments.length - 1].points.push(pos.slice());
 trailPointCount++;
 enforceTrailLimit();
}
function transitionTrailIfNeeded(reason) {
 const next = regimeFor(d);
 if (trailRegime === null) trailRegime = next;
 else if (next !== trailRegime) {
  trailRegime = next;
  startTrailSegment(x, reason);
 }
}
function clearTrail(pos) {
 planeYInit = false;
 trajectorySegments = [];
 trailPointCount = 0;
}

function validateZeroFieldPhysics(beforeX, beforeV, afterX, afterV, dt) {
 if (!d || d.Bm > TRAIL_EPS) return true;
 const velocityError = nrm(sub(afterV, beforeV));
 const positionError = nrm(sub(afterX, add(beforeX, sc(beforeV, dt))));
 const tolerance = 1e-8 * Math.max(1, nrm(beforeX), nrm(afterX));
 if (velocityError > 1e-12 || positionError > tolerance) {
  console.error("[physics] B=0 não preservou movimento uniforme", { velocityError, positionError, dt });
  return false;
 }
 return true;
}
function validateTrail() {
 let seen = 0;
 for (const s of trajectorySegments)
  for (const p of s.points) {
   if (!finitePoint(p)) {
    console.error("[trail] ponto inválido", p);
    return false;
   }
   seen++;
  }
 if (seen !== trailPointCount || seen > MAX_TRAIL) {
  console.error("[trail] contagem inconsistente", { seen, trailPointCount });
  return false;
 }
 return true;
}

const HIST_MAX = 20000;
const hist = [];
function recordSample() {
 hist.push([tSim, x[0], x[1], x[2], v[0], v[1], v[2], P.B[0], P.B[1], P.B[2]]);
 if (hist.length > HIST_MAX + 1000) hist.splice(0, 1000);
}
const meas = { phi: 0, t: 0 };

function params() {
 const k = PART[kind];
 let v0 = [val.vx, val.vy, val.vz];
 const s = nrm(v0);
 if (s >= C) v0 = sc(v0, (C * 0.999) / s);
 return { q: k.q * E, m: k.m, sign: Math.sign(k.q), name: k.n, B: [val.Bx, val.By, val.Bz], v0 };
}
function guide() {
 return d.Bm ? add(x, sc(cr(v, P.B), gm / (P.q * d.Bm * d.Bm))) : x.slice();
}
const baseRate = () => (d.Bm ? d.T / 2 : 1 / 3);

/* =========================================================
 4. INTERFACE: CAMPOS E MÓDULO
 ========================================================= */
let lastDir = [0.5, 0, 1];
{
 const m0 = Math.hypot(val.Bx, val.By, val.Bz);
 if (m0 > TRAIL_EPS) lastDir = [val.Bx / m0, val.By / m0, val.Bz / m0];
}
let modNum = null,
 modRng = null;

const CFG = [
 ["gB", "Bx", "Bx", -MODB_MAX, MODB_MAX, 0.1, "T"],
 ["gB", "By", "By", -MODB_MAX, MODB_MAX, 0.1, "T"],
 ["gB", "Bz", "Bz", -MODB_MAX, MODB_MAX, 0.1, "T"],
 ["gV", "vx", "vx", -C, C, 1e6, "m/s"],
 ["gV", "vy", "vy", -C, C, 1e6, "m/s"],
 ["gV", "vz", "vz", -C, C, 1e6, "m/s"],
];

CFG.forEach(([g, id, lb, mn, mx, st, u]) => {
 const w = document.createElement("div");
 w.className = "fld";
 w.innerHTML = `<div class="fh"><label for="n_${id}">${lb}</label><div><input id="n_${id}" type="number" step="any" value="${val[id]}"> ${u}</div></div><input type="range" min="${mn}" max="${mx}" step="${st}" value="${val[id]}" aria-label="${lb} (controle deslizante)">`;
 $(g).appendChild(w);
 const num = w.querySelector("input[type=number]"),
  rng = w.querySelector("input[type=range]");
 const set = (v_val, silent) => {
  v_val = Math.min(mx, Math.max(mn, v_val));
  val[id] = v_val;
  num.value = v_val;
  rng.value = v_val;
  if (!silent) {
   if (id.startsWith("B")) {
    syncModule();
    applyFieldChange();
   } else reset(false);
  }
 };
 rng.oninput = () => set(parseFloat(rng.value));
 num.onchange = () => set(parseFloat(num.value) || 0);
 ctl[id] = set;
});

function applyFieldChange() {
 const previousRegime = d ? regimeFor(d) : null;
 const nextRegime = regimeFor({ Bm: nrm([val.Bx, val.By, val.Bz]) });

 if (previousRegime === "free" && nextRegime === "magnetic") {
  reset(false);
  fit();
  return;
 }

 P.B = [val.Bx, val.By, val.Bz];
 d = derive(v, P);
 transitionTrailIfNeeded(`B regime: ${nextRegime}`);
 if (previousRegime !== nextRegime) fit();
 meas.phi = meas.t = 0;
 rate = baseRate() * speedMul;
 readouts();
 info();
 drawFieldGrid();
 persist();
}

function syncModule() {
 const m = nrm([val.Bx, val.By, val.Bz]);
 if (m > TRAIL_EPS) lastDir = [val.Bx / m, val.By / m, val.Bz / m];
 if (modNum) {
  const shown = parseFloat(m.toFixed(4));
  modNum.value = shown;
  modRng.value = shown;
 }
}
function setModule(m) {
 m = Math.min(MODB_MAX, Math.max(0, m));
 const dir = lastDir;
 ctl.Bx(dir[0] * m, true);
 ctl.By(dir[1] * m, true);
 ctl.Bz(dir[2] * m, true);
 modNum.value = m;
 modRng.value = m;
 applyFieldChange();
}
{
 const w = document.createElement("div");
 w.className = "fld";
 w.innerHTML = `<div class="fh"><label for="n_mod">|B| (módulo)</label><div><input id="n_mod" type="number" step="any" min="0" value="0"> T</div></div><input type="range" min="0" max="${MODB_MAX}" step="0.05" value="0" aria-label="|B| módulo (controle deslizante)">`;
 $("gM").appendChild(w);
 modNum = w.querySelector("input[type=number]");
 modRng = w.querySelector("input[type=range]");
 modRng.oninput = () => setModule(parseFloat(modRng.value));
 modNum.onchange = () => setModule(parseFloat(modNum.value) || 0);
 syncModule();
}

Object.keys(PART).forEach((k) => {
 const b = document.createElement("button");
 b.type = "button";
 b.textContent = PART[k].n;
 b.dataset.k = k;
 b.onclick = () => {
  setKind(k);
  reset(true);
 };
 $("kinds").appendChild(b);
});
function setKind(k) {
 kind = k;
 document.querySelectorAll("#kinds button").forEach((b) => (b.className = b.dataset.k === k ? "on" : ""));
}

const PRE = [
 ["Elétron circular", "e", 0, 0, 1, 1e7, 0, 0],
 ["Próton circular", "p", 0, 0, 1, 1e6, 0, 0],
 ["Hélice 3D (elétron)", "e", 0.5, 0, 1, 1e7, 0, 6e6],
 ["Hélice 3D (próton)", "p", 0, 0.6, 0.8, 2e6, 0, 1e6],
 ["v ∥ B (reta)", "e", 0, 0, 1, 0, 0, 1e7],
 ["Relativístico (0,33c)", "e", 0, 0, 1, 1e8, 0, 0],
];
PRE.forEach((p) => {
 const b = document.createElement("button");
 b.type = "button";
 b.textContent = p[0];
 b.onclick = () => {
  setKind(p[1]);
  ["Bx", "By", "Bz", "vx", "vy", "vz"].forEach((id, i) => ctl[id](p[2 + i], true));
  syncModule();
  reset(true);
 };
 $("pre").appendChild(b);
});

/* =========================================================
 5. MOTOR WEBGL (THREE.JS)
 ========================================================= */
let scene, camera, renderer, controls, stageEl;
let renderScale = 1;
let particleMesh, particleSprite, glowSprite, vecV, vecF, guideCircleMesh, guideCenterMesh;
let vLabel, fLabel, rLabel, rLine;
let fieldLinesInstanced, fieldHeadsInstanced, fieldAxisMarkers, fieldCrossMat, fieldDotMat, fieldBodyMat;
let gizmoScene, gizmoCamera, gizmoBArrow, gizmoBLabel;
let trailObj, trailGeo, trailMat, trailPos, trailCol;
let trailFat = false;
const currentTarget = new THREE.Vector3();
const bgCol = new THREE.Color(THEME_BG[theme]);
const trailBase = new THREE.Color(PART[kind].hex);

const _v3v = new THREE.Vector3();
const _v3f = new THREE.Vector3();
const _v3cam = new THREE.Vector3();
const _v3B = new THREE.Vector3();
const _q = new THREE.Quaternion();
const Y_AXIS = new THREE.Vector3(0, 1, 0);

const CAM_B_ALIGN_COS = 0.94;
const FIELD_NMAX = 9,
 FIELD_K = 5;

function createFieldAxisMaterial(mode) {
 const canvas = document.createElement("canvas");
 canvas.width = canvas.height = 128;
 const ctx = canvas.getContext("2d");
 ctx.strokeStyle = "#10B981";
 ctx.fillStyle = "#10B981";
 ctx.lineCap = "round";
 ctx.lineWidth = 9;
 ctx.beginPath();
 ctx.arc(64, 64, 48, 0, Math.PI * 2);
 ctx.stroke();
 if (mode === "cross") {
  ctx.lineWidth = 8;
  ctx.beginPath();
  ctx.moveTo(36, 36);
  ctx.lineTo(92, 92);
  ctx.moveTo(92, 36);
  ctx.lineTo(36, 92);
  ctx.stroke();
 } else {
  ctx.beginPath();
  ctx.arc(64, 64, 13, 0, Math.PI * 2);
  ctx.fill();
 }
 return new THREE.SpriteMaterial({
  map: new THREE.CanvasTexture(canvas),
  transparent: true,
  opacity: 0.9,
  depthWrite: false,
 });
}

function createSignSprite(signText) {
 const canvas = document.createElement("canvas");
 canvas.width = canvas.height = 256;
 const ctx = canvas.getContext("2d");
 ctx.fillStyle = "white";
 ctx.font = "bold 160px sans-serif";
 ctx.textAlign = "center";
 ctx.textBaseline = "middle";
 ctx.shadowColor = "rgba(0,0,0,0.5)";
 ctx.shadowBlur = 10;
 ctx.fillText(signText, 128, 140);
 const sprite = new THREE.Sprite(
  new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(canvas), depthTest: false, transparent: true }),
 );
 sprite.scale.set(1.6, 1.6, 1);
 sprite.renderOrder = 3;
 return sprite;
}

function makeLabel(text, color, size) {
 const canvas = document.createElement("canvas");
 canvas.width = canvas.height = 128;
 const ctx = canvas.getContext("2d");
 ctx.font = "italic 700 88px Georgia, 'Times New Roman', serif";
 ctx.textAlign = "center";
 ctx.textBaseline = "middle";
 ctx.shadowColor = "rgba(0,0,0,0.3)";
 ctx.shadowBlur = 6;
 ctx.fillStyle = color;
 ctx.fillText(text, 64, 68);
 const s = new THREE.Sprite(
  new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(canvas), transparent: true, depthTest: false, depthWrite: false }),
 );
 s.scale.set(size, size, 1);
 s.renderOrder = 4;
 return s;
}

function makeGlowSprite() {
 const c = document.createElement("canvas");
 c.width = c.height = 128;
 const g = c.getContext("2d");
 const gr = g.createRadialGradient(64, 64, 0, 64, 64, 64);
 gr.addColorStop(0, "rgba(255,255,255,0.9)");
 gr.addColorStop(0.35, "rgba(255,255,255,0.35)");
 gr.addColorStop(1, "rgba(255,255,255,0)");
 g.fillStyle = gr;
 g.fillRect(0, 0, 128, 128);
 const s = new THREE.Sprite(
  new THREE.SpriteMaterial({
   map: new THREE.CanvasTexture(c),
   color: PART[kind].hex,
   transparent: true,
   opacity: 0.6,
   depthWrite: false,
  }),
 );
 s.scale.set(4.4, 4.4, 1);
 s.renderOrder = 1;
 return s;
}

function createOrbitControls(prevControls) {
 const c = new THREE.OrbitControls(camera, renderer.domElement);
 c.enableDamping = true;
 c.dampingFactor = 0.05;
 c.minDistance = 2;
 c.maxDistance = 1000;
 if (prevControls) c.target.copy(prevControls.target);
 c.update();
 return c;
}
function resyncControlsUp() {
 const old = controls;
 controls = createOrbitControls(old);
 if (old) old.dispose();
}

function initThreeJS() {
 const canvas = $("scene");
 stageEl = $("stage");
 renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: false });
 renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
 renderer.setClearColor(bgCol, 1);
 const rect = stageEl.getBoundingClientRect();
 const w = Math.max(1, rect.width),
  h = Math.max(1, rect.height);
 renderer.setSize(w, h, false);

 scene = new THREE.Scene();
 scene.fog = new THREE.Fog(bgCol.getHex(), 40, 180);
 camera = new THREE.PerspectiveCamera(45, w / h, 0.1, 10000);
 camera.up.set(0, 1, 0);
 camera.position.set(-20, 20, 25);
 controls = createOrbitControls();

 scene.add(new THREE.HemisphereLight(0xffffff, 0x444444, 0.7));
 const dirLight = new THREE.DirectionalLight(0xffffff, 0.6);
 dirLight.position.set(15, 30, 20);
 scene.add(dirLight);

 particleMesh = new THREE.Mesh(
  new THREE.SphereGeometry(0.8, 32, 32),
  new THREE.MeshStandardMaterial({ roughness: 0.3, metalness: 0.5 }),
 );
 glowSprite = makeGlowSprite();
 particleMesh.add(glowSprite);
 particleSprite = createSignSprite("-");
 particleMesh.add(particleSprite);
 scene.add(particleMesh);

 initTrail(w, h);

 vecV = new THREE.ArrowHelper(new THREE.Vector3(1, 0, 0), new THREE.Vector3(), 1, 0xf59e0b, 1.2, 0.6);
 vecF = new THREE.ArrowHelper(new THREE.Vector3(1, 0, 0), new THREE.Vector3(), 1, 0x8b5cf6, 1.2, 0.6);
 scene.add(vecV);
 scene.add(vecF);
 vLabel = makeLabel("v", "#F59E0B", 1.7);
 fLabel = makeLabel("F", "#8B5CF6", 1.7);
 rLabel = makeLabel("r", "#6B7280", 1.5);
 scene.add(vLabel);
 scene.add(fLabel);
 scene.add(rLabel);

 guideCircleMesh = new THREE.Mesh(
  new THREE.RingGeometry(0.95, 1.0, 64),
  new THREE.MeshBasicMaterial({ color: 0x10b981, side: THREE.DoubleSide, transparent: true, opacity: 0.5 }),
 );
 guideCenterMesh = new THREE.Mesh(
  new THREE.SphereGeometry(0.25, 16, 16),
  new THREE.MeshBasicMaterial({ color: 0x6b7280 }),
 );
 rLine = new THREE.Line(
  new THREE.BufferGeometry().setAttribute("position", new THREE.BufferAttribute(new Float32Array(6), 3)),
  new THREE.LineBasicMaterial({ color: 0x6b7280, transparent: true, opacity: 0.8 }),
 );
 rLine.frustumCulled = false;
 scene.add(guideCircleMesh);
 scene.add(guideCenterMesh);
 scene.add(rLine);

 const cap = FIELD_NMAX * FIELD_NMAX * FIELD_K;
 const lineGeo = new THREE.CylinderGeometry(0.025, 0.025, 1, 8);
 lineGeo.translate(0, 0.5, 0);
 const headGeo = new THREE.ConeGeometry(0.12, 0.3, 8);
 headGeo.translate(0, 1.15, 0);
 fieldBodyMat = new THREE.MeshBasicMaterial({ color: 0x10b981, transparent: true, opacity: disp.fieldOp, depthWrite: false });
 fieldLinesInstanced = new THREE.InstancedMesh(lineGeo, fieldBodyMat, cap);
 fieldHeadsInstanced = new THREE.InstancedMesh(headGeo, fieldBodyMat, cap);
 fieldLinesInstanced.frustumCulled = fieldHeadsInstanced.frustumCulled = false;
 scene.add(fieldLinesInstanced);
 scene.add(fieldHeadsInstanced);

 fieldCrossMat = createFieldAxisMaterial("cross");
 fieldDotMat = createFieldAxisMaterial("dot");
 fieldAxisMarkers = new THREE.Group();
 fieldAxisMarkers.visible = false;
 for (let i = 0; i < FIELD_NMAX * FIELD_NMAX; i++) {
  const sprite = new THREE.Sprite(fieldCrossMat);
  sprite.scale.set(2.6, 2.6, 1);
  fieldAxisMarkers.add(sprite);
 }
 scene.add(fieldAxisMarkers);
 applyFieldOpacity();

 initPlane();
 initGizmo();

 renderer.domElement.addEventListener("dblclick", () => $("v3d").click());
 if (window.ResizeObserver) new ResizeObserver(onWindowResize).observe(stageEl);
 else window.addEventListener("resize", onWindowResize);
}

function initTrail(w, h) {
 trailPos = new Float32Array(MAX_TRAIL * 6);
 trailCol = new Float32Array(MAX_TRAIL * 6);
 if (THREE.LineSegments2 && THREE.LineSegmentsGeometry && THREE.LineMaterial) {
  trailFat = true;
  trailGeo = new THREE.LineSegmentsGeometry();
  trailGeo.setPositions(trailPos);
  trailGeo.setColors(trailCol);
  trailMat = new THREE.LineMaterial({ color: 0xffffff, linewidth: disp.trailW, vertexColors: true });
  trailMat.resolution.set(w, h);
  trailObj = new THREE.LineSegments2(trailGeo, trailMat);
  trailGeo.instanceCount = 0;
 } else {
  trailFat = false;
  trailGeo = new THREE.BufferGeometry();
  trailGeo.setAttribute("position", new THREE.BufferAttribute(trailPos, 3));
  trailGeo.setAttribute("color", new THREE.BufferAttribute(trailCol, 3));
  trailGeo.setDrawRange(0, 0);
  trailMat = new THREE.LineBasicMaterial({ vertexColors: true });
  trailObj = new THREE.LineSegments(trailGeo, trailMat);
 }
 trailObj.frustumCulled = false;
 scene.add(trailObj);
}

function updateTrail() {
 const segs = trajectorySegments,
  total = Math.max(1, trailPointCount - 1),
  fade = disp.trailMode === "fade";
 let pairs = 0,
  ord = 0,
  minY = Infinity,
  maxR = 0;
 for (const s of segs) {
  const pts = s.points;
  for (let i = 0; i < pts.length; i++) {
   const pt = pts[i];
   if (pt[1] * renderScale < minY) minY = pt[1] * renderScale;
   const rr = Math.hypot(pt[0], pt[2]) * renderScale;
   if (rr > maxR) maxR = rr;
   if (i > 0 && pairs < MAX_TRAIL) {
    const a = pts[i - 1],
     b = pts[i],
     o = pairs * 6;
    trailPos[o] = a[0] * renderScale;
    trailPos[o + 1] = a[1] * renderScale;
    trailPos[o + 2] = a[2] * renderScale;
    trailPos[o + 3] = b[0] * renderScale;
    trailPos[o + 4] = b[1] * renderScale;
    trailPos[o + 5] = b[2] * renderScale;
    shadowPos[o] = trailPos[o];
    shadowPos[o + 1] = 0;
    shadowPos[o + 2] = trailPos[o + 2];
    shadowPos[o + 3] = trailPos[o + 3];
    shadowPos[o + 4] = 0;
    shadowPos[o + 5] = trailPos[o + 5];
    const ta = fade ? 0.12 + (0.88 * (ord - 1)) / total : 1,
     tb = fade ? 0.12 + (0.88 * ord) / total : 1;
    trailCol[o] = bgCol.r + (trailBase.r - bgCol.r) * ta;
    trailCol[o + 1] = bgCol.g + (trailBase.g - bgCol.g) * ta;
    trailCol[o + 2] = bgCol.b + (trailBase.b - bgCol.b) * ta;
    trailCol[o + 3] = bgCol.r + (trailBase.r - bgCol.r) * tb;
    trailCol[o + 4] = bgCol.g + (trailBase.g - bgCol.g) * tb;
    trailCol[o + 5] = bgCol.b + (trailBase.b - bgCol.b) * tb;
    pairs++;
   }
   ord++;
  }
 }
 if (trailFat) {
  trailGeo.attributes.instanceStart.data.needsUpdate = true;
  trailGeo.attributes.instanceColorStart.data.needsUpdate = true;
  trailGeo.instanceCount = pairs;
 } else {
  trailGeo.attributes.position.needsUpdate = true;
  trailGeo.attributes.color.needsUpdate = true;
  trailGeo.setDrawRange(0, pairs * 2);
 }
 trailObj.userData.pairs = pairs;
 trailMinY = isFinite(minY) ? minY : 0;
 trailMaxR = maxR;
 shadowGeo.setDrawRange(0, pairs * 2);
 shadowGeo.attributes.position.needsUpdate = true;
 trailDirty = false;
}

function initGizmo() {
 gizmoScene = new THREE.Scene();
 gizmoCamera = new THREE.OrthographicCamera(-1.6, 1.6, 1.6, -1.6, 0.1, 10);
 const mk = (dir, color, label) => {
  gizmoScene.add(new THREE.ArrowHelper(dir.clone().normalize(), new THREE.Vector3(), 1.0, color, 0.3, 0.16));
  const s = makeLabel(label, "#9CA3AF", 0.5);
  s.position.copy(dir).multiplyScalar(1.3);
  gizmoScene.add(s);
 };
 mk(new THREE.Vector3(1, 0, 0), 0x9ca3af, "x");
 mk(new THREE.Vector3(0, 1, 0), 0x9ca3af, "y");
 mk(new THREE.Vector3(0, 0, 1), 0x9ca3af, "z");
 gizmoBArrow = new THREE.ArrowHelper(new THREE.Vector3(0, 0, 1), new THREE.Vector3(), 1.0, 0x10b981, 0.3, 0.16);
 gizmoBLabel = makeLabel("B", "#10B981", 0.55);
 gizmoScene.add(gizmoBArrow);
 gizmoScene.add(gizmoBLabel);
}
function renderGizmo() {
 const sizeV = new THREE.Vector2();
 renderer.getSize(sizeV);
 const px = 84,
  pad = 10;
 gizmoBArrow.visible = gizmoBLabel.visible = !!d.Bm;
 if (d.Bm) {
  _v3B.set(d.Bh[0], d.Bh[1], d.Bh[2]).normalize();
  gizmoBArrow.setDirection(_v3B);
  gizmoBLabel.position.copy(_v3B).multiplyScalar(1.3);
 }
 gizmoCamera.position.copy(camera.position).sub(controls.target).normalize().multiplyScalar(3);
 gizmoCamera.up.copy(camera.up);
 gizmoCamera.lookAt(0, 0, 0);

 renderer.setScissorTest(true);
 renderer.setViewport(sizeV.x - px - pad, sizeV.y - px - pad, px, px);
 renderer.setScissor(sizeV.x - px - pad, sizeV.y - px - pad, px, px);
 renderer.clearDepth();
 renderer.render(gizmoScene, gizmoCamera);
 renderer.setScissorTest(false);
 renderer.setViewport(0, 0, sizeV.x, sizeV.y);
}

function onWindowResize() {
 if (!renderer) return;
 const rect = stageEl.getBoundingClientRect();
 const w = Math.max(1, rect.width),
  h = Math.max(1, rect.height);
 camera.aspect = w / h;
 camera.updateProjectionMatrix();
 renderer.setSize(w, h, false);
 if (trailFat) trailMat.resolution.set(w, h);
}

const PLANE_GAP_FACTOR = 0.06;
let refPlane, planeMat, ticks, originDot, shadow, shadowGeo, shadowPos, projLine, projDot;
let planeKey = "",
 planeH = 0,
 planePhys = 1,
 planeY = 0,
 tickKey = "";
let trailMinY = 0,
 trailMaxR = 0;
const tickMatCache = new Map();
let tickCacheTheme = null;

function initPlane() {
 planeMat = new THREE.ShaderMaterial({
  uniforms: { col: { value: new THREE.Color() }, c: { value: 1 }, H: { value: 30 }, o: { value: 1 } },
  vertexShader:
   "uniform float H;varying vec2 p;void main(){p=position.xy*H;gl_Position=projectionMatrix*modelViewMatrix*vec4(p,0.,1.);}",
  fragmentShader: `uniform vec3 col;uniform float c,H,o;varying vec2 p;
   float ln(float v,float s){float q=v/s;return 1.-min(abs(fract(q-.5)-.5)/max(fwidth(q),1e-6),1.);}
   void main(){
    float e=1.-smoothstep(.7,1.,length(p)/H);
    float px=max(fwidth(p.x),fwidth(p.y));
    float mi=max(ln(p.x,c),ln(p.y,c))*(1.-smoothstep(.15,.4,px/c));
    float ma=max(ln(p.x,c*5.),ln(p.y,c*5.))*(1.-smoothstep(.15,.4,px/(c*5.)));
    float ax=max(1.-min(abs(p.x)/max(fwidth(p.x),1e-6),1.),1.-min(abs(p.y)/max(fwidth(p.y),1e-6),1.));
    float a=(.05+.16*mi+.3*ma+.55*ax)*e*o;
    if(a<.004) discard;
    gl_FragColor=vec4(col,a);
   }`,
  transparent: true,
  depthWrite: false,
  side: THREE.DoubleSide,
  extensions: { derivatives: true },
 });
 const planeMesh = new THREE.Mesh(new THREE.PlaneGeometry(2, 2), planeMat);
 planeMesh.frustumCulled = false;
 ticks = new THREE.Group();
 originDot = new THREE.Mesh(new THREE.SphereGeometry(0.3, 12, 12), new THREE.MeshBasicMaterial({ color: 0x6b7280 }));
 refPlane = new THREE.Group();
 refPlane.rotation.x = Math.PI / 2;
 refPlane.add(planeMesh, ticks, originDot);
 refPlane.visible = false;
 scene.add(refPlane);

 shadowPos = new Float32Array(MAX_TRAIL * 6);
 shadowGeo = new THREE.BufferGeometry();
 shadowGeo.setAttribute("position", new THREE.BufferAttribute(shadowPos, 3));
 shadowGeo.setDrawRange(0, 0);
 shadow = new THREE.LineSegments(
  shadowGeo,
  new THREE.LineBasicMaterial({ color: 0x6b7280, transparent: true, opacity: 0.45, depthWrite: false }),
 );
 shadow.frustumCulled = false;
 shadow.visible = false;
 scene.add(shadow);

 projLine = new THREE.Line(
  new THREE.BufferGeometry().setAttribute("position", new THREE.BufferAttribute(new Float32Array(6), 3)),
  new THREE.LineBasicMaterial({ color: 0x6b7280, transparent: true, opacity: 0.7 }),
 );
 projLine.frustumCulled = false;
 projDot = new THREE.Mesh(
  new THREE.SphereGeometry(0.25, 12, 12),
  new THREE.MeshBasicMaterial({ color: 0x6b7280, transparent: true }),
 );
 projLine.visible = projDot.visible = false;
 scene.add(projLine, projDot);
}

function tickMaterial(t) {
 if (tickCacheTheme !== theme) {
  tickMatCache.forEach((m) => {
   m.map.dispose();
   m.dispose();
  });
  tickMatCache.clear();
  tickCacheTheme = theme;
 }
 let m = tickMatCache.get(t);
 if (!m) {
  const cv = document.createElement("canvas");
  cv.width = 192;
  cv.height = 64;
  const g = cv.getContext("2d");
  g.font = "600 34px system-ui";
  g.textAlign = "center";
  g.textBaseline = "middle";
  g.fillStyle = theme === "dark" ? "#D1D5DB" : "#4B5563";
  g.fillText(t, 96, 34);
  const tex = new THREE.CanvasTexture(cv);
  tex.generateMipmaps = false;
  tex.minFilter = THREE.LinearFilter;
  m = new THREE.SpriteMaterial({ map: tex, transparent: true, depthTest: false, opacity: 0.9 });
  tickMatCache.set(t, m);
  if (tickMatCache.size > 200) {
   const first = tickMatCache.keys().next().value,
    old = tickMatCache.get(first);
   old.map.dispose();
   old.dispose();
   tickMatCache.delete(first);
  }
 }
 return m;
}
function buildTicks() {
 ticks.children.slice().forEach((o) => ticks.remove(o));
 const stepR = 5 * planePhys * renderScale;
 const put = (t, x, y) => {
  const sp = new THREE.Sprite(tickMaterial(t));
  sp.scale.set(6, 2, 1);
  sp.position.set(x, y, 0);
  ticks.add(sp);
 };
 for (let k = 1; k <= 8 && k * stepR < planeH * 0.85; k++)
  for (const sg of [1, -1]) {
   const t = fmtCompact(sg * k * 5 * planePhys, "m");
   put(t, sg * k * stepR, 2);
   put(t, 4.2, sg * k * stepR);
  }
 put("0", 2.2, 2);
 put("x", planeH * 0.93, -2.4);
 put("z", -3, planeH * 0.93);
}

function updatePlane(px, py, pz, gy) {
 const key = String(renderScale);
 if (key !== planeKey) {
  planeKey = key;
  planeH = 0;
  tickKey = "";
  planeYInit = false;
  planePhys = niceNum(4 / renderScale);
 }
 const c = planePhys * renderScale;

 const R = Math.max(trailMaxR, Math.hypot(px, pz));
 const need = Math.max(30, Math.ceil((R * 1.3 + 2 * c) / c) * c);
 if (need > planeH) {
  planeH = Math.max(need, planeH * 1.5);
  tickKey = "";
 }
 const tk = planeH + "|" + planePhys + "|" + renderScale + "|" + theme;
 if (tk !== tickKey) {
  tickKey = tk;
  buildTicks();
 }

 const orbitR = d.Bm ? d.r * renderScale : 15;
 const orbitLow = d.Bm ? gy - orbitR * Math.sqrt(Math.max(0, 1 - d.Bh[1] * d.Bh[1])) : py;
 const lowY = Math.min(trailMinY, orbitLow, py);
 const targetY = lowY - Math.max(0.6, PLANE_GAP_FACTOR * orbitR);
 if (!planeYInit) {
  planeY = targetY;
  planeYInit = true;
 } else if (targetY < planeY - 0.01 * orbitR) {
  planeY += (targetY - 0.1 * orbitR - planeY) * 0.2;
 }
 refPlane.position.set(0, planeY, 0);

 camera.getWorldDirection(_v3cam);
 const k0 = clamp((Math.abs(_v3cam.y) - 0.04) / 0.26, 0, 1),
  face = k0 * k0 * (3 - 2 * k0);
 const U = planeMat.uniforms;
 U.col.value.setHex(theme === "dark" ? 0x9ca3af : 0x4b6cb7);
 U.c.value = c;
 U.H.value = planeH;
 U.o.value = 0.12 + 0.88 * face;
 ticks.visible = face > 0.25;
 shadow.material.opacity = 0.45 * Math.max(face, 0.35);

 const dist = py - planeY;
 const t = clamp((Math.abs(dist) - 0.05 * c) / (0.35 * c), 0, 1),
  kk = t * t * (3 - 2 * t);
 projLine.material.opacity = 0.7 * kk;
 projDot.material.opacity = kk;
 projLine.visible = projDot.visible = kk > 0.01;
 const pa = projLine.geometry.attributes.position;
 pa.setXYZ(0, px, py, pz);
 pa.setXYZ(1, px, planeY, pz);
 pa.needsUpdate = true;
 projDot.position.set(px, planeY, pz);
}

function applyFieldOpacity() {
 fieldBodyMat.opacity = disp.fieldOp;
 const so = Math.min(1, disp.fieldOp * 2.3);
 fieldCrossMat.opacity = fieldDotMat.opacity = so;
}
function drawFieldGrid() {
 if (!d.Bm) {
  fieldLinesInstanced.count = fieldHeadsInstanced.count = 0;
  fieldAxisMarkers.visible = false;
  return;
 }
 const N = disp.fieldN,
  half = (N - 1) / 2;
 fieldLinesInstanced.count = fieldHeadsInstanced.count = N * N * FIELD_K;

 const dir = new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]).normalize();
 const axis = Math.abs(dir.x) < 0.9 ? new THREE.Vector3(1, 0, 0) : new THREE.Vector3(0, 1, 0);
 const e1 = new THREE.Vector3().crossVectors(dir, axis).normalize();
 const e2 = new THREE.Vector3().crossVectors(dir, e1).normalize();
 const dummy = new THREE.Object3D();
 const q = new THREE.Quaternion().setFromUnitVectors(Y_AXIS, dir);
 const L = 6;
 let idx = 0,
  mIdx = 0;

 for (let i = -half; i <= half; i++) {
  for (let j = -half; j <= half; j++) {
   const base = new THREE.Vector3().addScaledVector(e1, i * L * 1.6).addScaledVector(e2, j * L * 1.6);
   const marker = fieldAxisMarkers.children[mIdx++];
   marker.position.copy(base);
   marker.visible = true;
   for (let k = -2; k <= 2; k++) {
    const origin = base.clone().addScaledVector(dir, k * L * 0.9);
    dummy.position.copy(origin);
    dummy.quaternion.copy(q);
    dummy.scale.set(1, L * 0.5, 1);
    dummy.updateMatrix();
    fieldLinesInstanced.setMatrixAt(idx, dummy.matrix);
    dummy.position.copy(origin).addScaledVector(dir, L * 0.5);
    dummy.scale.set(1, 1, 1);
    dummy.updateMatrix();
    fieldHeadsInstanced.setMatrixAt(idx, dummy.matrix);
    idx++;
   }
  }
 }
 for (let m = N * N; m < fieldAxisMarkers.children.length; m++) fieldAxisMarkers.children[m].visible = false;
 fieldLinesInstanced.instanceMatrix.needsUpdate = true;
 fieldHeadsInstanced.instanceMatrix.needsUpdate = true;
}

function fit() {
 if (!d) return;
 let L = d.Bm ? Math.max(d.r, Math.abs(d.pitch) / 10) : d.sp * 3;
 if (!(L > 0)) L = 1;
 renderScale = 15 / L;
 trailDirty = true;
 drawFieldGrid();
}

function applyTheme(name) {
 theme = name;
 document.documentElement.dataset.theme = name;
 store.set("lorentz_theme", name);
 const ic = $("btnTheme") && $("btnTheme").querySelector("i");
 if (ic) ic.className = name === "dark" ? "bi bi-sun" : "bi bi-moon-stars";
 bgCol.setHex(THEME_BG[name]);
 if (renderer) {
  renderer.setClearColor(bgCol, 1);
  scene.fog.color.copy(bgCol);
  guideCenterMesh.material.color.setHex(name === "dark" ? 0x9ca3af : 0x6b7280);
  rLine.material.color.setHex(name === "dark" ? 0x9ca3af : 0x6b7280);
  tickKey = "";
  const gc = name === "dark" ? 0x9ca3af : 0x6b7280;
  [shadow, projLine, projDot, originDot].forEach((o) => o.material.color.setHex(gc));
  trailDirty = true;
 }
}

let camAnim = null;
const safeUp = (dir, up) => (Math.abs(dir.clone().normalize().dot(up.clone().normalize())) > 0.99 ? new THREE.Vector3(0, up.y > 0.5 ? 0 : 1, up.y > 0.5 ? 1 : 0) : up.clone());
function animateCameraTo(toDir, toUp, toDist) {
 toDir = toDir.clone().normalize();
 toUp = safeUp(toDir, toUp).normalize();
 const target = currentTarget.clone();
 const off = camera.position.clone().sub(target);
 const fromDist = off.length() || 45,
  fromDir = off.normalize();
 const dist = toDist != null ? toDist : fromDist;
 if (reduceMotion) {
  camera.up.copy(toUp);
  camera.position.copy(target).addScaledVector(toDir, dist);
  camera.lookAt(target);
  resyncControlsUp();
  return;
 }
 camAnim = {
  t0: performance.now(), dur: 520, fromDir, toDir, fromDist, toDist: dist,
  fromUp: camera.up.clone(), toUp, q: new THREE.Quaternion().setFromUnitVectors(fromDir, toDir),
 };
 controls.enabled = false;
}
function stepCameraAnim(target) {
 const a = camAnim;
 let u = (performance.now() - a.t0) / a.dur;
 const done = u >= 1;
 u = Math.min(1, u);
 const e = u < 0.5 ? 4 * u * u * u : 1 - Math.pow(-2 * u + 2, 3) / 2;
 const qt = new THREE.Quaternion().slerp(a.q, e);
 const dir = a.fromDir.clone().applyQuaternion(qt);
 const dist = a.fromDist + (a.toDist - a.fromDist) * e;
 camera.up.copy(a.fromUp).lerp(a.toUp, e).normalize();
 camera.position.copy(target).addScaledVector(dir, dist);
 camera.lookAt(target);
 if (done) {
  camAnim = null;
  camera.up.copy(a.toUp);
  camera.lookAt(target);
  resyncControlsUp();
 }
}

function placeCameraAlongB(target, distance) {
 if (!d.Bm) return false;
 const Bh = new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]);
 const up = safeUp(Bh, new THREE.Vector3(0, 1, 0));
 camera.up.copy(up);
 camera.position.copy(target).addScaledVector(Bh, -distance);
 camera.lookAt(target);
 return true;
}

function reset(fitView) {
 P = params();
 x = [0, 0, 0];
 v = P.v0.slice();
 d = derive(v, P);
 gm = d.g * P.m;
 tSim = 0;
 sp0 = d.sp;
 ke0 = d.KE;
 rate = baseRate() * speedMul;
 meas.phi = meas.t = 0;
 hist.length = 0;
 clearTrail(x);
 recordSample();

 particleMesh.material.color.setHex(PART[kind].hex);
 glowSprite.material.color.setHex(PART[kind].hex);
 trailBase.setHex(PART[kind].hex);
 trailDirty = true;
 particleMesh.remove(particleSprite);
 particleSprite = createSignSprite(PART[kind].sign);
 particleMesh.add(particleSprite);

 if (fitView) {
  fit();
  camAnim = null;
  controls.enabled = true;
  camera.up.set(0, 1, 0);
  currentTarget.set(0, 0, 0);
  controls.target.set(0, 0, 0);
  if (!placeCameraAlongB(currentTarget, 45)) {
   camera.position.set(-20, 20, 25);
   camera.lookAt(currentTarget);
  }
  resyncControlsUp();
 }
 readouts();
 info();
 persist();
}

/* =========================================================
 6. SIMULAÇÃO
 ========================================================= */
function setPlaying(f) {
 playing = f;
 $("play").innerHTML = f ? '<i class="bi bi-pause-fill"></i> Pausar' : '<i class="bi bi-play-fill"></i> Iniciar';
 $("tPlay").innerHTML = f ? '<i class="bi bi-pause-fill"></i>' : '<i class="bi bi-play-fill"></i>';
 $("stChip").className = f ? "badge run" : "badge";
 $("stTxt").textContent = f ? "Rodando" : "Pausado";
}

function advance(run) {
 if (!(run > 0)) return;
 const n = d.Bm ? Math.min(300, Math.max(1, Math.ceil(run / (d.T / 200)))) : 1,
  dt = run / n;
 const Bh = d.Bm ? d.Bh : null,
  measurable = Bh && d.vperp > 1e-9 * d.sp;
 for (let i = 0; i < n; i++) {
  const xa = DEBUG_TRAIL ? x.slice() : null,
   va = v;
  v = boris(v, P.q, gm, P.B, dt);
  x = add(x, sc(add(va, v), dt / 2));
  if (measurable) {
   const pa = sub(va, sc(Bh, dot(va, Bh))),
    pb = sub(v, sc(Bh, dot(v, Bh)));
   meas.phi += Math.atan2(nrm(cr(pa, pb)), dot(pa, pb));
   meas.t += dt;
  }
  if (DEBUG_TRAIL) validateZeroFieldPhysics(xa, va, x, v, dt);
 }
 tSim += run;
 pushTrail(x);
 recordSample();
 if (DEBUG_TRAIL) validateTrail();
}
function step(el) {
 if (playing) advance(Math.min(el, 0.05) * rate);
}
function stepOnce() {
 if (playing) setPlaying(false);
 advance(rate / 30);
}

function setSpeed(log) {
 speedLog = clamp(log, -1, 0.7);
 speedMul = Math.pow(10, speedLog);
 if (d) rate = baseRate() * speedMul;
 $("spd").value = speedLog;
 $("spdOut").textContent = speedMul.toFixed(2) + "×";
 if (d) info();
 persist();
}

/* =========================================================
 7. RENDERIZAÇÃO POR QUADRO
 ========================================================= */
const _tp = new THREE.Vector3(),
 _delta = new THREE.Vector3();
let pendingShot = false;

function renderScene() {
 const g = guide();
 const gx = g[0] * renderScale,
  gy = g[1] * renderScale,
  gz = g[2] * renderScale;

 const follow = chk.cFollow.checked;
 _tp.set(follow ? gx : 0, follow ? gy : 0, follow ? gz : 0);
 if (follow) camera.position.add(_delta.copy(_tp).sub(currentTarget));
 currentTarget.copy(_tp);
 controls.target.copy(currentTarget);
 if (camAnim) stepCameraAnim(currentTarget);
 else controls.update();

 const rx = x[0] * renderScale,
  ry = x[1] * renderScale,
  rz = x[2] * renderScale;
 particleMesh.position.set(rx, ry, rz);

 if (trailDirty) updateTrail();
 trailObj.visible = chk.cTrail.checked && trailObj.userData.pairs > 0;
 if (DEBUG_TRAIL) validateTrail();

 const labelsOn = chk.cLabels.checked;
 let showV = false,
  showF = false;
 if (chk.cVec.checked && d.sp > 0) {
  const vLen = 6;
  showV = true;
  vecV.position.set(rx, ry, rz);
  _v3v.set(v[0], v[1], v[2]).normalize();
  vecV.setDirection(_v3v);
  vecV.setLength(vLen, 1.2, 0.6);
  vLabel.position.set(rx, ry, rz).addScaledVector(_v3v, vLen + 1.4);

  if (d.Bm && d.vperp > 1e-9 * d.sp) {
   const F = sc(cr(v, P.B), P.q);
   const fLen = 6;
   showF = true;
   vecF.position.set(rx, ry, rz);
   _v3f.set(F[0], F[1], F[2]).normalize();
   vecF.setDirection(_v3f);
   vecF.setLength(fLen, 1.2, 0.6);
   fLabel.position.set(rx, ry, rz).addScaledVector(_v3f, fLen + 1.4);
  }
 }
 vecV.visible = showV;
 vecF.visible = showF;
 vLabel.visible = showV && labelsOn;
 fLabel.visible = showF && labelsOn;

 const showField = chk.cField.checked;
 let axisAligned = false;
 if (showField && d.Bm) {
  camera.getWorldDirection(_v3cam);
  const align = _v3cam.dot(_v3B.set(d.Bh[0], d.Bh[1], d.Bh[2]));
  axisAligned = Math.abs(align) > CAM_B_ALIGN_COS;
  if (axisAligned) {
   fieldAxisMarkers.position.set(gx, gy, gz);
   const mat = align > 0 ? fieldCrossMat : fieldDotMat;
   for (const s of fieldAxisMarkers.children) s.material = mat;
  }
 }
 fieldAxisMarkers.visible = showField && !!d.Bm && axisAligned;
 fieldLinesInstanced.visible = fieldHeadsInstanced.visible = showField && !axisAligned;
 if (showField && !axisAligned) {
  fieldLinesInstanced.position.set(gx, gy, gz);
  fieldHeadsInstanced.position.set(gx, gy, gz);
 }

 const planeOn = chk.cGrid.checked;
 refPlane.visible = shadow.visible = planeOn;
 if (planeOn) updatePlane(rx, ry, rz, gy);
 else projLine.visible = projDot.visible = false;

 const showDisc = !!d.Bm && chk.cRadius.checked;
 guideCircleMesh.visible = guideCenterMesh.visible = showDisc;
 const showR = showDisc && d.r > 0 && d.vperp > 1e-9 * d.sp;
 rLine.visible = showR;
 rLabel.visible = showR && labelsOn;
 if (showDisc) {
  guideCenterMesh.position.set(gx, gy, gz);
  guideCircleMesh.position.set(gx, gy, gz);
  _q.setFromUnitVectors(new THREE.Vector3(0, 0, 1), _v3B.set(d.Bh[0], d.Bh[1], d.Bh[2]));
  guideCircleMesh.setRotationFromQuaternion(_q);
  const R = d.r * renderScale;
  guideCircleMesh.scale.set(R, R, 1);
  if (showR) {
   const pa = rLine.geometry.attributes.position;
   pa.setXYZ(0, gx, gy, gz);
   pa.setXYZ(1, rx, ry, rz);
   pa.needsUpdate = true;
   rLabel.position.set((gx + rx) / 2, (gy + ry) / 2, (gz + rz) / 2);
  }
 }

 renderer.render(scene, camera);
 renderGizmo();

 if (pendingShot) {
  pendingShot = false;
  try {
   download(renderer.domElement.toDataURL("image/png"), `lorentz_${stamp()}.png`);
   toast("Imagem salva");
  } catch (_) {
   toast("Não foi possível salvar a imagem");
  }
 }
}

function updateScaleBar() {
 const on = chk.cScale.checked;
 $("scalebar").hidden = !on;
 const gridOn = chk.cGrid.checked;
 $("legGrid").hidden = !gridOn;
 if (gridOn) $("legGridTxt").textContent = "plano: célula = " + fmtCompact(planePhys, "m");
 if (!on) return;
 const H = renderer.domElement.clientHeight || 1;
 const dist = camera.position.distanceTo(controls.target) || 1;
 const worldPerPx = (2 * dist * Math.tan(THREE.MathUtils.degToRad(camera.fov / 2))) / H;
 const mPerPx = worldPerPx / renderScale;
 const nice = niceNum(mPerPx * 90);
 $("sbLine").style.width = Math.max(8, Math.round(nice / mPerPx)) + "px";
 $("sbLabel").textContent = fmtCompact(nice, "m");
}

let loopErr = false;
function loop(t) {
 try {
  if (lastT == null) lastT = t;
  step((t - lastT) / 1000);
  lastT = t;
  renderScene();
  fc++;
  if (fc % 12 === 0) info();
  if (fc % 3 === 0) updateScaleBar();
  if (fc % 4 === 0) drawChart();
 } catch (err) {
  if (!loopErr) {
   loopErr = true;
   console.error("Lorentz loop error:", err);
  }
 }
 requestAnimationFrame(loop);
}

/* =========================================================
 8. GRANDEZAS, ANÁLISE E GRÁFICOS
 ========================================================= */
let srTimer = null;
function announce(text) {
 clearTimeout(srTimer);
 srTimer = setTimeout(() => ($("sr").textContent = text), 600);
}

function readouts() {
 const B = d.Bm > 0;
 const cards = [
  ["Raio r", B ? fmt(d.r, "m") : "—", "r"],
  ["Período T", B ? fmt(d.T, "s") : "—", "T"],
  ["Frequência f", B ? fmt(d.f, "Hz") : "—", "f"],
  ["|v|", fmt(d.sp, "m/s") + " (" + ((d.sp / C) * 100).toFixed(1) + "% c)", "v"],
  ["v∥ (ao B)", B ? fmt(d.vpar, "m/s") : "—", "vpar"],
  ["v⊥ (a B)", B ? fmt(d.vperp, "m/s") : "—", "vperp"],
  ["Passo (Pitch)", B ? fmt(d.pitch, "m") : "—", "pitch"],
  ["Fator γ", d.g.toFixed(4), "gamma"],
  ["Energia cin.", fmt(d.KE / E, "eV"), "KE"],
  ["Momento p", d.p.toExponential(3) + " kg·m/s", "p"],
  ["Força |F|", B ? fmt(d.F, "N") : "—", "F"],
  ["Aceleração", B ? fmt(d.acc, "m/s²") : "—", "a"],
 ];
 $("dash").innerHTML = cards
  .map(
   (c) =>
    `<div class="card"><b>${c[0]}<button class="help" type="button" data-help="${c[2]}" aria-label="O que é ${c[0]}?">?</button></b><span>${c[1]}</span></div>`,
  )
  .join("");
 $("cap").innerHTML =
  `<b>${P.name}</b><br>q = ${fmt(P.q, "C")} · m = ${fmt(P.m, "kg")}<br>Modelo relativístico: γm = ${fmt(gm, "kg")}`;

 const rel = d.g > 1.05;
 $("relChip").hidden = !rel;
 if (rel) $("relTxt").textContent = "Regime relativístico · γ = " + d.g.toFixed(3);
 announce(
  `${P.name}. ` +
   (B ? `Raio ${fmt(d.r, "m")}, período ${fmt(d.T, "s")}. ` : "Sem campo magnético. ") +
   `Velocidade ${(d.sp / C * 100).toFixed(1)} por cento da luz, energia cinética ${fmt(d.KE / E, "eV")}.`,
 );
}

function info() {
 const deg = (a) => ((a * 180) / Math.PI).toFixed(1) + "°";
 let s =
  `Tempo simulado: <b>${fmt(tSim, "s")}</b>` +
  (d.Bm ? ` (${(tSim / d.T).toFixed(2)} voltas)` : "") +
  `<br>Ritmo: 1 s real = <b>${fmt(rate, "s")}</b> simulados`;
 if (d.Bm) {
  const align = new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]).dot(camera.getWorldDirection(new THREE.Vector3()));
  s += `<br>Ângulo entre v e B: <b>${deg(Math.atan2(d.vperp, d.vpar))}</b>`;
  if (Math.abs(align) > CAM_B_ALIGN_COS)
   s += `<br>Câmera alinhada com B: <b>${align > 0 ? "⊗ campo entrando na tela" : "⊙ campo saindo da tela"}</b>`;
 } else s += "<br>Sem campo: movimento retilíneo uniforme.";
 $("info").innerHTML = s;
 updateAnalysis();
}

function updateAnalysis() {
 const set = (id, t) => ($(id).textContent = t);
 const magnetic = d.Bm > 0 && d.vperp > 1e-9 * d.sp;
 if (magnetic) {
  set("cmpRt", fmtCompact(d.r, "m"));
  set("cmpTt", fmtCompact(d.T, "s"));
  if (meas.t > 0 && meas.phi > 0.3) {
   const w = meas.phi / meas.t,
    rS = d.vperp / w,
    tS = (2 * Math.PI) / w;
   set("cmpRs", fmtCompact(rS, "m"));
   set("cmpTs", fmtCompact(tS, "s"));
   set("cmpRe", fmtErr((rS - d.r) / d.r));
   set("cmpTe", fmtErr((tS - d.T) / d.T));
  } else ["cmpRs", "cmpTs", "cmpRe", "cmpTe"].forEach((id) => set(id, "medindo…"));
 } else ["cmpRt", "cmpRs", "cmpRe", "cmpTt", "cmpTs", "cmpTe"].forEach((id) => set(id, "—"));

 if (ke0 > 0) {
  const cur = kineticOf(v);
  set("cmpEt", fmtCompact(ke0 / E, "eV"));
  set("cmpEs", fmtCompact(cur / E, "eV"));
  set("cmpEe", fmtErr((cur - ke0) / ke0));
 } else ["cmpEt", "cmpEs", "cmpEe"].forEach((id) => set(id, "—"));
}

let chartMode = "v";
const CHART_WIN = 600;
function drawChart() {
 const cv = $("chart");
 if (!cv || !cv.offsetParent) return;
 const dpr = Math.min(2, window.devicePixelRatio || 1),
  W = cv.clientWidth,
  H = cv.clientHeight;
 if (W < 40 || H < 40) return;
 const pw = Math.round(W * dpr),
  ph = Math.round(H * dpr);
 if (cv.width !== pw || cv.height !== ph) {
  cv.width = pw;
  cv.height = ph;
 }
 const g = cv.getContext("2d");
 g.setTransform(dpr, 0, 0, dpr, 0, 0);
 g.clearRect(0, 0, W, H);
 const cs = getComputedStyle(document.documentElement);
 const cMu = cs.getPropertyValue("--mu").trim() || "#6B7280",
  cBd = cs.getPropertyValue("--bd").trim() || "#E5E7EB",
  cTx = cs.getPropertyValue("--tx").trim() || "#1F2937";
 g.font = "10px system-ui, sans-serif";
 g.textBaseline = "middle";

 const n = Math.min(hist.length, CHART_WIN);
 if (n < 2) {
  g.fillStyle = cMu;
  g.textAlign = "center";
  g.fillText("Inicie a simulação para ver o gráfico", W / 2, H / 2);
  $("chartNote").textContent = "";
  return;
 }
 const rows = hist.slice(hist.length - n);
 let series, yFmt;
 if (chartMode === "v") {
  series = [
   { n: "vx", c: "#EF4444", f: (r) => r[4] },
   { n: "vy", c: "#10B981", f: (r) => r[5] },
   { n: "vz", c: "#3B82F6", f: (r) => r[6] },
   { n: "|v|", c: cTx, dash: [4, 3], f: (r) => Math.hypot(r[4], r[5], r[6]) },
  ];
  yFmt = (y) => fmtCompact(y, "m/s");
 } else {
  const spRef = sp0 || 1,
   keRef = ke0 || 1;
  series = [
   { n: "|v| / |v₀|", c: "#3B82F6", f: (r) => Math.hypot(r[4], r[5], r[6]) / spRef },
   { n: "Ec / Ec₀", c: "#F59E0B", dash: [4, 3], f: (r) => kineticOf([r[4], r[5], r[6]]) / keRef },
  ];
  yFmt = (y) => y.toFixed(3);
 }
 const vals = series.map((s) => rows.map(s.f));
 let yMin = Infinity,
  yMax = -Infinity;
 vals.forEach((a) =>
  a.forEach((y) => {
   if (y < yMin) yMin = y;
   if (y > yMax) yMax = y;
  }),
 );
 if (chartMode === "cons") {
  yMin = Math.min(0.98, yMin);
  yMax = Math.max(1.02, yMax);
  const dev = vals.map((a) => Math.max(...a.map((y) => Math.abs(y - 1))));
  $("chartNote").textContent =
   `Desvio máximo na janela: |v| ${dev[0].toExponential(1)} · Ec ${dev[1].toExponential(1)}. ` +
   "O integrador de Boris conserva a energia (a força magnética não realiza trabalho).";
 } else {
  if (yMax - yMin < 1e-12 * Math.max(1, Math.abs(yMax))) {
   const m = Math.abs(yMax) || 1;
   yMin -= m * 0.1;
   yMax += m * 0.1;
  } else {
   const pad = (yMax - yMin) * 0.08;
   yMin -= pad;
   yMax += pad;
  }
  $("chartNote").textContent =
   "Componentes de v e módulo |v| (tracejado) na janela recente. Em campo magnético puro, |v| é constante.";
 }
 const padL = 58,
  padR = 8,
  padT = 20,
  padB = 18;
 const pw2 = W - padL - padR,
  ph2 = H - padT - padB;
 const t0 = rows[0][0],
  t1 = rows[rows.length - 1][0] || t0 + 1;
 const X = (t) => padL + ((t - t0) / (t1 - t0 || 1)) * pw2;
 const Yp = (y) => padT + (1 - (y - yMin) / (yMax - yMin)) * ph2;

 g.strokeStyle = cBd;
 g.lineWidth = 1;
 g.fillStyle = cMu;
 g.textAlign = "right";
 for (let i = 0; i <= 4; i++) {
  const y = yMin + ((yMax - yMin) * i) / 4,
   py = Yp(y);
  g.beginPath();
  g.moveTo(padL, py);
  g.lineTo(W - padR, py);
  g.stroke();
  g.fillText(yFmt(y), padL - 4, py);
 }
 g.textAlign = "left";
 g.fillText(fmtCompact(t0, "s"), padL, H - 8);
 g.textAlign = "right";
 g.fillText(fmtCompact(t1, "s"), W - padR, H - 8);

 series.forEach((s, si) => {
  g.strokeStyle = s.c;
  g.lineWidth = 1.6;
  g.setLineDash(s.dash || []);
  g.beginPath();
  rows.forEach((r, i) => {
   const px = X(r[0]),
    py = Yp(vals[si][i]);
   i ? g.lineTo(px, py) : g.moveTo(px, py);
  });
  g.stroke();
 });
 g.setLineDash([]);
 let lx = padL;
 g.textAlign = "left";
 series.forEach((s) => {
  g.strokeStyle = s.c;
  g.lineWidth = 2;
  g.setLineDash(s.dash || []);
  g.beginPath();
  g.moveTo(lx, 9);
  g.lineTo(lx + 14, 9);
  g.stroke();
  g.setLineDash([]);
  g.fillStyle = cTx;
  g.fillText(s.n, lx + 18, 9);
  lx += 26 + g.measureText(s.n).width;
 });
}

/* =========================================================
 9. EXPORTAÇÃO E LINK
 ========================================================= */
const stamp = () => new Date().toISOString().replace(/[-:T]/g, "").slice(0, 14);
let toastTimer = null;
function toast(msg) {
 const t = $("toast");
 t.textContent = msg;
 t.classList.add("show");
 clearTimeout(toastTimer);
 toastTimer = setTimeout(() => t.classList.remove("show"), 2200);
}
function download(urlOrBlob, name) {
 const isBlob = urlOrBlob instanceof Blob;
 const url = isBlob ? URL.createObjectURL(urlOrBlob) : urlOrBlob;
 const a = document.createElement("a");
 a.href = url;
 a.download = name;
 document.body.appendChild(a);
 a.click();
 a.remove();
 if (isBlob) setTimeout(() => URL.revokeObjectURL(url), 4000);
}
async function copyText(t) {
 try {
  await navigator.clipboard.writeText(t);
  return true;
 } catch (_) {
  const ta = document.createElement("textarea");
  ta.value = t;
  ta.style.cssText = "position:fixed;opacity:0";
  document.body.appendChild(ta);
  ta.select();
  let ok = false;
  try {
   ok = document.execCommand("copy");
  } catch (__) {}
  ta.remove();
  return ok;
 }
}
async function copyLink() {
 const link = buildLink();
 toast((await copyText(link)) ? "Link do cenário copiado" : "Não foi possível copiar o link");
}
function takeScreenshot() {
 pendingShot = true;
}
function exportCsv() {
 if (hist.length < 2) return toast("Inicie a simulação para gerar dados");
 const m = P.m;
 const head = "t_s,x_m,y_m,z_m,vx_m_s,vy_m_s,vz_m_s,Bx_T,By_T,Bz_T,speed_m_s,gamma,Ec_J,Ec_eV";
 const rows = hist.map((r) => {
  const sp = Math.hypot(r[4], r[5], r[6]),
   b = Math.min(0.9999, sp / C),
   gm2 = 1 / Math.sqrt(1 - b * b),
   ke = ((gm2 * gm2 * b * b) / (gm2 + 1)) * m * C * C;
  return [...r, sp, gm2, ke, ke / E].map((n) => Number(n).toPrecision(10)).join(",");
 });
 const blob = new Blob(["\ufeff" + head + "\n" + rows.join("\n")], { type: "text/csv;charset=utf-8" });
 download(blob, `lorentz_${kind === "e" ? "eletron" : "proton"}_${stamp()}.csv`);
 toast(`CSV salvo (${hist.length} amostras)`);
}

let recorder = null,
 recChunks = [],
 recStart = 0,
 recTimer = null;
function updateRecUI(on) {
 const t = $("tRec"),
  b = $("btnRec");
 t.classList.toggle("rec", on);
 t.innerHTML = on ? '<i class="bi bi-stop-fill"></i>' : '<i class="bi bi-record-circle"></i>';
 t.setAttribute("aria-label", on ? "Parar gravação" : "Gravar vídeo");
 if (!on) {
  b.innerHTML = '<i class="bi bi-record-circle"></i> Gravar vídeo';
  return;
 }
 const s = Math.floor((performance.now() - recStart) / 1000);
 b.innerHTML = `<i class="bi bi-stop-circle"></i> Parar (${String(Math.floor(s / 60)).padStart(2, "0")}:${String(s % 60).padStart(2, "0")})`;
}
function toggleRecord() {
 if (recorder) {
  recorder.stop();
  return;
 }
 const cv = renderer.domElement;
 if (!cv.captureStream || !window.MediaRecorder) return toast("Gravação não suportada neste navegador");
 const mime = ["video/webm;codecs=vp9", "video/webm;codecs=vp8", "video/webm", "video/mp4"].find((t) =>
  MediaRecorder.isTypeSupported(t),
 );
 try {
  recorder = new MediaRecorder(cv.captureStream(30), mime ? { mimeType: mime, videoBitsPerSecond: 6e6 } : {});
 } catch (_) {
  recorder = null;
  return toast("Não foi possível iniciar a gravação");
 }
 recChunks = [];
 recorder.ondataavailable = (e) => e.data && e.data.size && recChunks.push(e.data);
 recorder.onstop = () => {
  const type = (recorder && recorder.mimeType) || "video/webm";
  clearInterval(recTimer);
  download(new Blob(recChunks, { type }), `lorentz_${stamp()}.${type.includes("mp4") ? "mp4" : "webm"}`);
  recorder = null;
  updateRecUI(false);
  toast("Vídeo salvo");
 };
 recorder.start(1000);
 recStart = performance.now();
 updateRecUI(true);
 recTimer = setInterval(() => updateRecUI(true), 500);
 toast("Gravando… clique novamente para parar");
}

/* =========================================================
 10. INTERFACE E CONTROLES
 ========================================================= */
function setView(dir, up) {
 animateCameraTo(dir, up, 45);
}
$("vTop").onclick = () => setView(new THREE.Vector3(0, 0, 1), new THREE.Vector3(0, 1, 0));
$("vSide").onclick = () => setView(new THREE.Vector3(0, 1, 0), new THREE.Vector3(0, 0, 1));
$("vYZ").onclick = () => setView(new THREE.Vector3(1, 0, 0), new THREE.Vector3(0, 1, 0));
$("v3d").onclick = () => setView(new THREE.Vector3(-20, 20, 25), new THREE.Vector3(0, 1, 0));
$("alignBtn").onclick = () => {
 if (!d.Bm) return toast("Sem campo magnético: não há direção para alinhar");
 animateCameraTo(new THREE.Vector3(-d.Bh[0], -d.Bh[1], -d.Bh[2]), camera.up.clone(), null);
};

$("play").onclick = () => setPlaying(!playing);
$("tPlay").onclick = () => setPlaying(!playing);
$("stepBtn").onclick = stepOnce;
$("reset").onclick = () => reset(true);
$("clr").onclick = () => clearTrail(x);

function initDisplayControls() {
 DISPLAY_IDS.forEach((id) => {
  if (savedChips && id in savedChips) chk[id].checked = !!savedChips[id];
  chk[id].addEventListener("change", persist);
 });
 const tl = $("trailLen"),
  tw = $("trailW"),
  tm = $("trailMode"),
  fo = $("fieldOp"),
  fn = $("fieldN");
 tl.value = disp.trailLen;
 tw.value = disp.trailW;
 tm.value = disp.trailMode;
 fo.value = disp.fieldOp;
 fn.value = disp.fieldN;
 const outs = () => {
  $("trailLenOut").textContent = disp.trailLen + " pts";
  $("trailWOut").textContent = disp.trailW + " px";
  $("fieldOpOut").textContent = disp.fieldOp.toFixed(2);
  $("fieldNOut").textContent = disp.fieldN + " × " + disp.fieldN;
 };
 outs();
 tl.oninput = () => {
  disp.trailLen = +tl.value;
  trailLimit = disp.trailLen;
  enforceTrailLimit();
  outs();
  persist();
 };
 tw.oninput = () => {
  disp.trailW = +tw.value;
  if (trailFat) trailMat.linewidth = disp.trailW;
  outs();
  persist();
 };
 tm.onchange = () => {
  disp.trailMode = tm.value;
  trailDirty = true;
  persist();
 };
 fo.oninput = () => {
  disp.fieldOp = +fo.value;
  applyFieldOpacity();
  outs();
  persist();
 };
 fn.oninput = () => {
  disp.fieldN = +fn.value;
  drawFieldGrid();
  outs();
  persist();
 };
 $("spd").oninput = () => setSpeed(parseFloat($("spd").value));
 document.querySelectorAll("#spdBtns button").forEach((b) => (b.onclick = () => setSpeed(Math.log10(+b.dataset.s))));
 document.querySelectorAll(".tab").forEach(
  (b) =>
   (b.onclick = () => {
    chartMode = b.dataset.mode;
    document.querySelectorAll(".tab").forEach((t) => t.setAttribute("aria-selected", String(t === b)));
    drawChart();
   }),
 );
}

$("btnLink").onclick = copyLink;
$("btnPng").onclick = $("tPng").onclick = takeScreenshot;
$("btnCsv").onclick = exportCsv;
$("btnRec").onclick = $("tRec").onclick = toggleRecord;
if (!window.MediaRecorder) {
 $("btnRec").hidden = true;
 $("tRec").hidden = true;
}

function toggleFullscreen() {
 const el = $("stage");
 if (document.fullscreenElement || document.webkitFullscreenElement) (document.exitFullscreen || document.webkitExitFullscreen).call(document);
 else (el.requestFullscreen || el.webkitRequestFullscreen || (() => {})).call(el);
}
$("tFull").onclick = toggleFullscreen;
if (!($("stage").requestFullscreen || $("stage").webkitRequestFullscreen)) $("tFull").hidden = true;
["fullscreenchange", "webkitfullscreenchange"].forEach((ev) =>
 document.addEventListener(ev, () => {
  const on = !!(document.fullscreenElement || document.webkitFullscreenElement);
  $("tFull").innerHTML = on ? '<i class="bi bi-fullscreen-exit"></i>' : '<i class="bi bi-fullscreen"></i>';
 }),
);

$("btnTheme").onclick = () => applyTheme(theme === "dark" ? "light" : "dark");

const tipEl = $("tip");
let tipFor = null;
function showTip(btn) {
 const txt = HELP[btn.dataset.help];
 if (!txt) return;
 tipEl.textContent = txt;
 tipEl.hidden = false;
 const r = btn.getBoundingClientRect(),
  tw = tipEl.offsetWidth,
  th = tipEl.offsetHeight;
 tipEl.style.left = clamp(r.left + r.width / 2 - tw / 2, 8, Math.max(8, innerWidth - tw - 8)) + "px";
 let top = r.bottom + 8;
 if (top + th > innerHeight - 8) top = r.top - th - 8;
 tipEl.style.top = Math.max(8, top) + "px";
 tipFor = btn;
 btn.setAttribute("aria-describedby", "tip");
}
function hideTip() {
 tipEl.hidden = true;
 if (tipFor) tipFor.removeAttribute("aria-describedby");
 tipFor = null;
}
const helpBtn = (e) => (e.target.closest ? e.target.closest(".help") : null);
document.addEventListener("mouseover", (e) => helpBtn(e) && showTip(helpBtn(e)));
document.addEventListener("mouseout", (e) => helpBtn(e) && hideTip());
document.addEventListener("focusin", (e) => helpBtn(e) && showTip(helpBtn(e)));
document.addEventListener("focusout", (e) => helpBtn(e) && hideTip());
window.addEventListener("scroll", hideTip, true);
document.addEventListener("click", (e) => {
 const b = helpBtn(e);
 if (b) showTip(b);
 else hideTip();
 if (e.detail > 0) {
  const btn = e.target.closest && e.target.closest("button");
  if (btn && !btn.closest("dialog") && !btn.classList.contains("help")) btn.blur();
 }
});

const openDialog = (dlg) => {
 hideTip();
 if (typeof dlg.showModal === "function") {
  if (!dlg.open) dlg.showModal();
 } else dlg.setAttribute("open", "");
};
const closeDialog = (dlg) => {
 if (typeof dlg.close === "function") dlg.close();
 else dlg.removeAttribute("open");
};
[$("about"), $("tour")].forEach((dlg) => dlg.addEventListener("click", (e) => e.target === dlg && closeDialog(dlg)));
$("btnHelp").onclick = () => openDialog($("about"));
$("aboutClose").onclick = () => closeDialog($("about"));

const TOUR = [
 { t: "Escolha um cenário", d: "Na lateral, comece por um dos cenários prontos (elétron circular, hélice 3D, relativístico…). Você também pode escolher a partícula e ajustar B e v." },
 { t: "Inicie a simulação", d: "Use o botão Iniciar ou a tecla Espaço. O botão Passo avança quadro a quadro, e o ritmo pode ser ajustado na seção Simulação." },
 { t: "Explore em 3D", d: "Arraste para girar, use scroll ou pinça para zoom e dê duplo clique para reiniciar a vista. As vistas XY, XZ, YZ e o botão “Alinhar câmera a B” ajudam a enxergar o campo." },
 { t: "Analise os resultados", d: "Os cartões no topo trazem raio, período, energia, força e mais — toque no “?” para entender cada grandeza. Em Análise há gráficos e a comparação teoria × simulação." },
 { t: "Guarde e compartilhe", d: "Copie um link do cenário, salve uma imagem PNG, o CSV da trajetória ou grave um vídeo. Aperte “?” a qualquer momento para ver os atalhos e rever este tutorial." },
];
let tourI = 0;
function renderTour() {
 const s = TOUR[tourI];
 $("tourStep").textContent = `Passo ${tourI + 1} de ${TOUR.length}`;
 $("tourTitle").textContent = s.t;
 $("tourText").textContent = s.d;
 $("tourDots").innerHTML = TOUR.map((_, i) => `<i class="${i === tourI ? "on" : ""}"></i>`).join("");
 $("tourPrev").hidden = tourI === 0;
 $("tourNext").textContent = tourI === TOUR.length - 1 ? "Concluir" : "Próximo";
}
function openTour() {
 tourI = 0;
 renderTour();
 openDialog($("tour"));
}
function closeTour() {
 store.set("lorentz_tour_done", "1");
 closeDialog($("tour"));
}
$("tourNext").onclick = () => (tourI >= TOUR.length - 1 ? closeTour() : (tourI++, renderTour()));
$("tourPrev").onclick = () => (tourI > 0 && (tourI--, renderTour()));
$("tourSkip").onclick = closeTour;
$("tour").addEventListener("close", () => store.set("lorentz_tour_done", "1"));
$("aboutTour").onclick = () => {
 closeDialog($("about"));
 openTour();
};

let loaderGone = false;
document.addEventListener("keydown", (e) => {
 if (!loaderGone || e.ctrlKey || e.metaKey || e.altKey) return;
 if (e.key === "Escape") hideTip();
 if (document.querySelector("dialog[open]")) return;
 if (e.target.closest && e.target.closest("input:not([type=range]), textarea, select, button, summary, a, [contenteditable]")) return;
 const k = e.key;
 if (k === " ") setPlaying(!playing);
 else if (k === "." || k === "n" || k === "N") stepOnce();
 else if (k === "r" || k === "R") reset(true);
 else if (k === "c" || k === "C") clearTrail(x);
 else if (k === "f" || k === "F") toggleFullscreen();
 else if (k === "p" || k === "P") takeScreenshot();
 else if (k === "t" || k === "T") $("btnTheme").click();
 else if (k === "?" || k === "h" || k === "H") openDialog($("about"));
 else return;
 e.preventDefault();
});

function hideLoader() {
 if (loaderGone) return;
 loaderGone = true;
 const l = $("loading-screen");
 if (l) {
  l.style.opacity = "0";
  setTimeout(() => l.remove(), reduceMotion ? 0 : 600);
 }
 store.set("lorentz_seen", "1");
 if (!store.get("lorentz_tour_done")) setTimeout(openTour, reduceMotion ? 0 : 650);
}
function setupLoader() {
 $("aboutAuthors").innerHTML = $("loadAuthors").innerHTML;
 const l = $("loading-screen");
 if (!isFirstVisit) {
  loaderGone = true;
  l.remove();
  if (!store.get("lorentz_tour_done")) openTour();
  return;
 }
 const remaining = Math.max(0, LOADING_MIN_MS - (performance.now() - loadStart));
 $("loadHint").hidden = false;
 l.addEventListener("click", hideLoader);
 document.addEventListener("keydown", hideLoader, { once: true });
 setTimeout(hideLoader, remaining);
}

/* =========================================================
 11. INICIALIZAÇÃO
 ========================================================= */
try {
 initDisplayControls();
 setKind(kind);
 initThreeJS();
 applyTheme(theme);
 reset(true);
 setSpeed(speedLog);
 setPlaying(false);
 updateScaleBar();
 requestAnimationFrame(loop);
 setupLoader();
} catch (err) {
 const box = document.getElementById("loading-box");
 if (box)
  box.innerHTML = `<h1 class="loading-title" style="color:#EF4444">Falha WebGL</h1><p style="color:var(--mu)">Seu navegador não suporta aceleração 3D ou houve um erro interno.</p>`;
 console.error("Lorentz WebGL Error:", err);
}