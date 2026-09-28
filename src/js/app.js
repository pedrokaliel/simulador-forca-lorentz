"use strict";

// Marca o início do carregamento para garantir um tempo mínimo de
// exibição da tela de loading (créditos da equipe), independente da
// velocidade de inicialização do motor 3D.
const LOADING_MIN_MS = 1800;
const loadStart = performance.now();

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

// Utilitários de Vetores (Física)
const add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const sc = (a, k) => [a[0] * k, a[1] * k, a[2] * k];
const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const nrm = (a) => Math.hypot(a[0], a[1], a[2]);
const cr = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const $ = (id) => document.getElementById(id);

// Formatação
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
  const b = Math.min(0.9999, sp / C); // Proteção contra velocidades não-físicas
  const g = 1 / Math.sqrt(Math.max(1e-12, 1 - b * b));
  const Bm = nrm(P.B);

  if (Bm < 1e-12)
    return { g, sp, Bm: 0, Bh: [0, 1, 0], vpar: sp, vperp: 0, T: Infinity, w: 0, r: 0, pitch: Infinity };

  const Bh = sc(P.B, 1 / Bm);
  const vpar = dot(v, Bh);
  const vperp = Math.sqrt(Math.max(0, sp * sp - vpar * vpar));
  const w = (Math.abs(P.q) * Bm) / (g * P.m);
  const T = (2 * Math.PI) / w;
  const r = (g * P.m * vperp) / (Math.abs(P.q) * Bm);
  return { g, sp, Bm, Bh, vpar, vperp, T, w, r, pitch: vpar * T };
}

/* =========================================================
 3. ESTADO GLOBAL E CONTROLES
 ========================================================= */
const val = { Bx: 0.5, By: 0, Bz: 1, vx: 1e7, vy: 0, vz: 6e6 };
let kind = "e",
  ctl = {};
let P, x, v, gm, d, rate, tSim;
let playing = false,
  lastT = null,
  fc = 0;

// Histórico segmentado: nunca conecta dois regimes físicos distintos.
// O limite é global para manter memória e custo de renderização constantes.
let MAX_TRAIL = 3000;
const MAX_TRAIL_SEGMENTS = 32;
const TRAIL_EPS = 1e-12;
const DEBUG_TRAIL = false;
let trajectorySegments = [];
let trailPointCount = 0;
let trailRegime = null;

function finitePoint(pos) {
  return Array.isArray(pos) && pos.length === 3 && pos.every(Number.isFinite);
}

function regimeFor(derived) {
  return derived && derived.Bm > TRAIL_EPS ? "magnetic" : "free";
}

function debugTrail(label) {
  if (!DEBUG_TRAIL) return;
  console.debug("[trail]", label, {
    segments: trajectorySegments.length,
    points: trailPointCount,
    B: d && d.Bm,
    position: x && x.slice(),
    velocity: v && v.slice(),
    renderScale,
  });
}

function startTrailSegment(pos, reason) {
  if (!finitePoint(pos)) throw new Error(`Ponto inicial inválido (${reason})`);
  const segment = { points: [pos.slice()], reason, regime: trailRegime };
  trajectorySegments.push(segment);
  trailPointCount++;
  while (trajectorySegments.length > MAX_TRAIL_SEGMENTS || trailPointCount > MAX_TRAIL) {
    const removed = trajectorySegments.shift();
    trailPointCount -= removed.points.length;
  }
  debugTrail(`novo segmento: ${reason}`);
}

function pushTrail(pos) {
  if (!finitePoint(pos)) throw new Error("Tentativa de inserir ponto não finito no trail");
  if (!trajectorySegments.length) startTrailSegment(pos, "initial");
  const segment = trajectorySegments[trajectorySegments.length - 1];
  segment.points.push(pos.slice());
  trailPointCount++;
  while (trailPointCount > MAX_TRAIL && trajectorySegments.length) {
    const first = trajectorySegments[0];
    if (first.points.length <= 1) {
      trajectorySegments.shift();
      trailPointCount--;
    } else {
      first.points.shift();
      trailPointCount--;
    }
  }
}

function transitionTrailIfNeeded(reason) {
  const next = regimeFor(d);
  if (trailRegime === null) trailRegime = next;
  else if (next !== trailRegime) {
    trailRegime = next;
    startTrailSegment(x, reason);
  } else trailRegime = next;
}

function clearTrail(pos) {
  trajectorySegments = [];
  trailPointCount = 0;
  trailRegime = d ? regimeFor(d) : null;
  startTrailSegment(pos, "reset");
  debugTrail("trail limpo");
}

function validateZeroFieldPhysics(beforeX, beforeV, afterX, afterV, dt) {
  if (!d || d.Bm > TRAIL_EPS) return true;
  const velocityError = nrm(sub(afterV, beforeV));
  const expectedX = add(beforeX, sc(beforeV, dt));
  const positionError = nrm(sub(afterX, expectedX));
  const tolerance = 1e-8 * Math.max(1, nrm(beforeX), nrm(afterX));
  if (velocityError > 1e-12 || positionError > tolerance) {
    console.error("[physics] B=0 não preservou movimento uniforme", {
      velocityError,
      positionError,
      beforeX,
      afterX,
      beforeV,
      afterV,
      dt,
    });
    return false;
  }
  return true;
}

function validateTrail() {
  let seen = 0;
  for (let si = 0; si < trajectorySegments.length; si++) {
    const points = trajectorySegments[si].points;
    for (let pi = 0; pi < points.length; pi++) {
      if (!finitePoint(points[pi])) {
        console.error("[trail] ponto inválido", {
          segment: si,
          index: pi,
          point: points[pi],
          B: P && P.B,
          previous: points[pi - 1],
          next: points[pi + 1],
        });
        return false;
      }
      seen++;
    }
  }
  if (seen !== trailPointCount || seen > MAX_TRAIL || trajectorySegments.length > MAX_TRAIL_SEGMENTS) {
    console.error("[trail] contagem inconsistente", {
      seen,
      trailPointCount,
      segments: trajectorySegments.length,
    });
    return false;
  }
  return true;
}

function params() {
  const k = PART[kind];
  let v0 = [val.vx, val.vy, val.vz];
  const s = nrm(v0);
  if (s >= C) v0 = sc(v0, (C * 0.999) / s); // Trava relativística
  return { q: k.q * E, m: k.m, sign: Math.sign(k.q), name: k.n, B: [val.Bx, val.By, val.Bz], v0 };
}

function guide() {
  return d.Bm ? add(x, sc(cr(v, P.B), gm / (P.q * d.Bm * d.Bm))) : x.slice();
}

/* =========================================================
 4. CONSTRUÇÃO DA INTERFACE & PRESETS
 ========================================================= */
const MODB_MAX = 5; // limite (T) do módulo e de cada componente de B
let lastDir = [0.5, 0, 1]; // última direção não nula de B (usada quando |B| = 0)
{
  const m0 = Math.hypot(val.Bx, val.By, val.Bz);
  lastDir = [val.Bx / m0, val.By / m0, val.Bz / m0];
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
  w.innerHTML = `<div class="fh"><label>${lb}</label><div><input type="number" step="any" value="${val[id]}"> ${u}</div></div><input type="range" min="${mn}" max="${mx}" step="${st}" value="${val[id]}">`;
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

// Aplica ao estado físico uma mudança em val.Bx/By/Bz (componentes ou módulo).
function applyFieldChange() {
  const previousRegime = d ? regimeFor(d) : null;
  const nextRegime = regimeFor({ Bm: nrm([val.Bx, val.By, val.Bz]) });

  // Campo voltou depois de ter sido zerado: a partícula reinicia
  // (posição, velocidade inicial, tempo e rastro) já com o novo B.
  if (previousRegime === "free" && nextRegime === "magnetic") {
    reset(false); // não mexe na câmera
    fit(); // recalibra a escala, que estava ajustada à reta
    return;
  }

  // Demais casos (magnético → magnético, magnético → zero)
  P.B = [val.Bx, val.By, val.Bz];
  d = derive(v, P);
  // B = 0 é um regime físico válido: preserva o histórico e abre
  // apenas uma nova faixa topológica, que continuará em linha reta.
  transitionTrailIfNeeded(`B regime: ${nextRegime}`);
  // Recalibrar somente na troca de regime estabiliza a tela.
  if (previousRegime !== nextRegime) fit();
  rate = d.Bm ? d.T / 2 : 1 / 3;
  readouts();
  info();
  drawFieldGrid();
}

// Atualiza a direção memorizada e o controle de módulo a partir dos componentes.
function syncModule() {
  const m = nrm([val.Bx, val.By, val.Bz]);
  if (m > TRAIL_EPS) lastDir = [val.Bx / m, val.By / m, val.Bz / m];
  if (modNum) {
    const shown = parseFloat(m.toFixed(4));
    modNum.value = shown;
    modRng.value = shown;
  }
}

// Define |B| mantendo a direção atual (ou a última direção, se B era nulo).
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
  w.innerHTML = `<div class="fh"><label>|B| (módulo)</label><div><input type="number" step="any" min="0" value="0"> T</div></div><input type="range" min="0" max="${MODB_MAX}" step="0.05" value="0">`;
  $("gM").appendChild(w);
  modNum = w.querySelector("input[type=number]");
  modRng = w.querySelector("input[type=range]");
  modRng.oninput = () => setModule(parseFloat(modRng.value));
  modNum.onchange = () => setModule(parseFloat(modNum.value) || 0);
  syncModule();
}

Object.keys(PART).forEach((k) => {
  const b = document.createElement("button");
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
let scene, camera, renderer, controls;
let renderScale = 1;
let particleMesh, particleSprite, trailLine, vecV, vecF, guideCircleMesh, guideCenterMesh;
let fieldLinesInstanced, fieldHeadsInstanced;
let fieldAxisMarkers, fieldCrossMat, fieldDotMat;
let fieldHalf = 2;
let gizmoScene, gizmoCamera, gizmoBArrow;
const currentTarget = new THREE.Vector3();

// Helpers reutilizáveis para evitar instanciamento e Garbage Collection
const _v3v = new THREE.Vector3();
const _v3f = new THREE.Vector3();
const _v3cam = new THREE.Vector3();

// Quando a câmera fica quase paralela a B, as setas 3D do campo (cilindro+cone)
// são vistas quase de ponta e degeneram visualmente em traços radiais curtos.
// A partir deste cosseno de alinhamento (~20°), substituímos as setas por
// símbolos padrão da física: ⊗ (campo entrando na tela) e ⊙ (campo saindo da
// tela) — sempre de frente para a câmera (sprites).
const CAM_B_ALIGN_COS = 0.94;

// Textura de sprite para os símbolos ⊗ / ⊙ de campo visto "de ponta".
function createFieldAxisMaterial(mode) {
  const canvas = document.createElement("canvas");
  canvas.width = canvas.height = 128;
  const ctx = canvas.getContext("2d");
  ctx.clearRect(0, 0, 128, 128);
  ctx.strokeStyle = "#10B981";
  ctx.fillStyle = "#10B981";
  ctx.lineCap = "round";
  ctx.lineWidth = 9;
  ctx.beginPath();
  ctx.arc(64, 64, 48, 0, Math.PI * 2);
  ctx.stroke();
  if (mode === "cross") {
    // ⊗ campo entrando na tela
    ctx.lineWidth = 8;
    ctx.beginPath();
    ctx.moveTo(64 - 28, 64 - 28);
    ctx.lineTo(64 + 28, 64 + 28);
    ctx.moveTo(64 + 28, 64 - 28);
    ctx.lineTo(64 - 28, 64 + 28);
    ctx.stroke();
  } else {
    // ⊙ campo saindo da tela
    ctx.beginPath();
    ctx.arc(64, 64, 13, 0, Math.PI * 2);
    ctx.fill();
  }
  const texture = new THREE.CanvasTexture(canvas);
  return new THREE.SpriteMaterial({
    map: texture,
    transparent: true,
    opacity: 0.9,
    depthWrite: false,
    sizeAttenuation: true,
  });
}

// Sprite de alta resolução com o sinal da carga
function createSignSprite(signText) {
  const canvas = document.createElement("canvas");
  canvas.width = 256;
  canvas.height = 256;
  const ctx = canvas.getContext("2d");
  ctx.fillStyle = "rgba(255,255,255,0)";
  ctx.fillRect(0, 0, 256, 256);
  ctx.fillStyle = "white";
  ctx.font = "bold 160px sans-serif";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.shadowColor = "rgba(0,0,0,0.5)";
  ctx.shadowBlur = 10;
  ctx.fillText(signText, 128, 140);

  const texture = new THREE.CanvasTexture(canvas);
  const spriteMaterial = new THREE.SpriteMaterial({ map: texture, depthTest: false });
  const sprite = new THREE.Sprite(spriteMaterial);
  sprite.scale.set(1.6, 1.6, 1);
  return sprite;
}

// OrbitControls (r128) calcula seu quaternion interno de orientação UMA ÚNICA
// VEZ, ao ser instanciado, a partir de camera.up naquele momento. Se camera.up
// for alterado depois (ao trocar de perspectiva), esse quaternion NÃO é
// recalculado e o arrasto do mouse gira o eixo errado. A forma robusta de
// corrigir é recriar a instância sempre que camera.up mudar, preservando as
// opções e o alvo (target) atuais.
function createOrbitControls(prevControls) {
  const c = new THREE.OrbitControls(camera, renderer.domElement);
  c.enableDamping = true;
  c.dampingFactor = 0.05;
  c.minDistance = 2;
  c.maxDistance = 1000;
  if (prevControls) {
    c.target.copy(prevControls.target);
  }
  c.update();
  return c;
}

// Troca a instância de OrbitControls, ressincronizando seu quaternion
// interno com o camera.up atual. Chamar sempre (e somente) depois de
// alterar camera.up.
function resyncControlsUp() {
  const old = controls;
  controls = createOrbitControls(old);
  if (old) old.dispose();
}

function initThreeJS() {
  const canvas = $("scene");
  renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: false });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2)); // Trava resolução excessiva
  renderer.setClearColor(0xffffff, 1);

  const rect = canvas.parentElement.getBoundingClientRect();
  renderer.setSize(rect.width, rect.height);

  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(45, rect.width / rect.height, 0.1, 10000);
  camera.up.set(0, 1, 0);
  camera.position.set(-20, 20, 25);

  controls = createOrbitControls();

  // Iluminação
  scene.add(new THREE.HemisphereLight(0xffffff, 0x444444, 0.7));
  const dirLight = new THREE.DirectionalLight(0xffffff, 0.6);
  dirLight.position.set(15, 30, 20);
  scene.add(dirLight);

  // Partícula
  particleMesh = new THREE.Mesh(
    new THREE.SphereGeometry(0.8, 32, 32),
    new THREE.MeshStandardMaterial({ roughness: 0.3, metalness: 0.5 }),
  );
  particleSprite = createSignSprite("-");
  particleMesh.add(particleSprite);
  scene.add(particleMesh);

  // Rastro segmentado. Cada Line possui um histórico independente;
  // THREE nunca recebe uma aresta implícita entre regimes incompatíveis.
  trailLine = new THREE.Group();
  trailLine.frustumCulled = false;
  scene.add(trailLine);

  // Vetores ArrowHelper
  vecV = new THREE.ArrowHelper(new THREE.Vector3(1, 0, 0), new THREE.Vector3(), 1, 0xf59e0b, 1.2, 0.6);
  vecF = new THREE.ArrowHelper(new THREE.Vector3(1, 0, 0), new THREE.Vector3(), 1, 0x8b5cf6, 1.2, 0.6);
  scene.add(vecV);
  scene.add(vecF);

  // Guias circulares
  guideCircleMesh = new THREE.Mesh(
    new THREE.RingGeometry(0.95, 1.0, 64),
    new THREE.MeshBasicMaterial({ color: 0x10b981, side: THREE.DoubleSide, transparent: true, opacity: 0.5 }),
  );
  guideCenterMesh = new THREE.Mesh(
    new THREE.SphereGeometry(0.25, 16, 16),
    new THREE.MeshBasicMaterial({ color: 0x6b7280 }),
  );
  scene.add(guideCircleMesh);
  scene.add(guideCenterMesh);

  // Campo magnético - InstancedMesh
  const count = 9 * 9 * 9; // capacidade máxima (densidade até 9 × 9)
  const lineGeo = new THREE.CylinderGeometry(0.025, 0.025, 1, 8);
  lineGeo.translate(0, 0.5, 0); // Pivô na base
  const headGeo = new THREE.ConeGeometry(0.12, 0.3, 8);
  headGeo.translate(0, 1.15, 0); // Pivô relativo
  const matB = new THREE.MeshBasicMaterial({
    color: 0x10b981,
    transparent: true,
    opacity: 0.35,
    depthWrite: false,
  });

  fieldLinesInstanced = new THREE.InstancedMesh(lineGeo, matB, count);
  fieldHeadsInstanced = new THREE.InstancedMesh(headGeo, matB, count);
  fieldLinesInstanced.frustumCulled = false;
  fieldHeadsInstanced.frustumCulled = false;
  scene.add(fieldLinesInstanced);
  scene.add(fieldHeadsInstanced);

  // Marcadores ⊗ / ⊙: uma coluna (5x5 = 25) de sprites sempre de frente
  // para a câmera, usados no lugar das setas 3D quando a visão está
  // quase paralela a B (ver CAM_B_ALIGN_COS).
  fieldCrossMat = createFieldAxisMaterial("cross");
  fieldDotMat = createFieldAxisMaterial("dot");
  fieldAxisMarkers = new THREE.Group();
  fieldAxisMarkers.visible = false;
  fieldAxisMarkers.frustumCulled = false;
  for (let i = 0; i < 81; i++) {
    const sprite = new THREE.Sprite(fieldCrossMat);
    sprite.scale.set(2.6, 2.6, 1);
    fieldAxisMarkers.add(sprite);
  }
  scene.add(fieldAxisMarkers);

  initGizmo();

  renderer.domElement.addEventListener("dblclick", () => $("v3d").click());
  window.addEventListener("resize", onWindowResize);
}

function initGizmo() {
  gizmoScene = new THREE.Scene();
  gizmoCamera = new THREE.OrthographicCamera(-1.6, 1.6, 1.6, -1.6, 0.1, 10);
  const mk = (dir, color) =>
    gizmoScene.add(new THREE.ArrowHelper(dir.normalize(), new THREE.Vector3(), 1.15, color, 0.35, 0.18));
  mk(new THREE.Vector3(1, 0, 0), 0x9ca3af);
  mk(new THREE.Vector3(0, 1, 0), 0x9ca3af);
  mk(new THREE.Vector3(0, 0, 1), 0x9ca3af);
  gizmoBArrow = new THREE.ArrowHelper(new THREE.Vector3(0, 0, 1), new THREE.Vector3(), 1.15, 0x10b981, 0.35, 0.18);
  gizmoScene.add(gizmoBArrow);
}

function renderGizmo() {
  const sizeV = new THREE.Vector2();
  renderer.getSize(sizeV);
  const px = 84,
    pad = 10;

  gizmoBArrow.visible = !!d.Bm;
  if (d.Bm) gizmoBArrow.setDirection(new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]).normalize());

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
  const rect = renderer.domElement.parentElement.getBoundingClientRect();
  camera.aspect = rect.width / rect.height;
  camera.updateProjectionMatrix();
  renderer.setSize(rect.width, rect.height);
}

// Calcula o InstancedMesh da grade de B
function drawFieldGrid() {
  if (!d.Bm) {
    fieldLinesInstanced.count = 0;
    fieldHeadsInstanced.count = 0;
    fieldAxisMarkers.visible = false;
    return;
  }
  fieldLinesInstanced.count = (2 * fieldHalf + 1) ** 3;
  fieldHeadsInstanced.count = (2 * fieldHalf + 1) ** 3;

  const dir = new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]).normalize();
  const axis = Math.abs(dir.x) < 0.9 ? new THREE.Vector3(1, 0, 0) : new THREE.Vector3(0, 1, 0);
  const e1 = new THREE.Vector3().crossVectors(dir, axis).normalize();
  const e2 = new THREE.Vector3().crossVectors(dir, e1).normalize();

  const dummy = new THREE.Object3D();
  const q = new THREE.Quaternion().setFromUnitVectors(new THREE.Vector3(0, 1, 0), dir);
  const L = 6; // Comprimento visual no WebGL
  let idx = 0,
    mIdx = 0;

  for (let i = -fieldHalf; i <= fieldHalf; i++) {
    for (let j = -fieldHalf; j <= fieldHalf; j++) {
      const base = new THREE.Vector3().addScaledVector(e1, i * L * 1.6).addScaledVector(e2, j * L * 1.6);

      // Marcador ⊗/⊙ desta coluna: uma única posição na mesma grade
      // e1/e2 das setas, sem repetição em profundidade (k).
      { const mk = fieldAxisMarkers.children[mIdx++]; if (mk) mk.position.copy(base); }

      for (let k = -fieldHalf; k <= fieldHalf; k++) {
        const origin = base.clone().addScaledVector(dir, k * L * 0.9);

        // Corpo (cilindro)
        dummy.position.copy(origin);
        dummy.quaternion.copy(q);
        dummy.scale.set(1, L * 0.5, 1);
        dummy.updateMatrix();
        fieldLinesInstanced.setMatrixAt(idx, dummy.matrix);

        // Cabeça (cone)
        dummy.position.copy(origin.clone().addScaledVector(dir, L * 0.5));
        dummy.scale.set(1, 1, 1);
        dummy.updateMatrix();
        fieldHeadsInstanced.setMatrixAt(idx, dummy.matrix);
        idx++;
      }
    }
  }
  fieldLinesInstanced.instanceMatrix.needsUpdate = true;
  fieldHeadsInstanced.instanceMatrix.needsUpdate = true;
}

function fit() {
  if (!d) return;
  let L = d.Bm ? Math.max(d.r, Math.abs(d.pitch) / 10) : d.sp * 3;
  if (!(L > 0)) L = 1;
  renderScale = 15 / L; // Normaliza o "aquário" visual
  drawFieldGrid();
}

function reset(fitView) {
  P = params();
  x = [0, 0, 0];
  v = P.v0.slice();
  d = derive(v, P);
  gm = d.g * P.m;
  tSim = 0;
  rate = d.Bm ? d.T / 2 : 1 / 3;
  clearTrail(x);

  particleMesh.material.color.setHex(PART[kind].hex);
  trailLine.children.forEach((line) => line.material.color.setHex(PART[kind].hex));

  particleMesh.remove(particleSprite);
  particleSprite = createSignSprite(PART[kind].sign);
  particleMesh.add(particleSprite);

  if (fitView) {
    fit();
    camera.up.set(0, 1, 0); // Restaura orientação padrão
    currentTarget.set(0, 0, 0);
    controls.target.set(0, 0, 0);
    // Posição inicial da câmera: a mesma que resultaria de apertar
    // "Alinhar câmera a B" (visada paralela ao campo). Sem campo
    // definido, cai de volta na visão livre padrão.
    if (!alignCameraToB(currentTarget, 45)) {
      camera.position.set(-20, 20, 25);
      camera.lookAt(currentTarget);
    }
    resyncControlsUp(); // Garante consistência dos eixos de controle
  }
  readouts();
  info();
}

function renderScene() {
  const g = guide();
  const gx = g[0] * renderScale,
    gy = g[1] * renderScale,
    gz = g[2] * renderScale;

  // Rastreamento fluido da câmera
  const targetPos = $("cFollow").checked ? new THREE.Vector3(gx, gy, gz) : new THREE.Vector3(0, 0, 0);
  const delta = targetPos.clone().sub(currentTarget);
  if ($("cFollow").checked) {
    camera.position.add(delta); // Desloca a câmera em sincronia
  }
  currentTarget.copy(targetPos);
  controls.target.copy(currentTarget);
  controls.update();

  // Partícula
  const rx = x[0] * renderScale,
    ry = x[1] * renderScale,
    rz = x[2] * renderScale;
  particleMesh.position.set(rx, ry, rz);

  // Atualiza cada segmento em world space; transformações visuais não
  // alteram as fotografias físicas armazenadas.
  while (trailLine.children.length < trajectorySegments.length) {
    const geo = new THREE.BufferGeometry();
    geo.setAttribute("position", new THREE.BufferAttribute(new Float32Array(MAX_TRAIL * 3), 3));
    const line = new THREE.Line(geo, new THREE.LineBasicMaterial({ color: PART[kind].hex, linewidth: 2 }));
    line.frustumCulled = false;
    trailLine.add(line);
  }
  trajectorySegments.forEach((segment, si) => {
    const line = trailLine.children[si];
    const array = line.geometry.attributes.position.array;
    segment.points.forEach((point, pi) => {
      const k = pi * 3;
      array[k] = point[0] * renderScale;
      array[k + 1] = point[1] * renderScale;
      array[k + 2] = point[2] * renderScale;
    });
    line.geometry.setDrawRange(0, segment.points.length);
    line.geometry.attributes.position.needsUpdate = true;
    line.visible = $("cTrail").checked;
  });
  for (let si = trajectorySegments.length; si < trailLine.children.length; si++) {
    trailLine.children[si].visible = false;
    trailLine.children[si].geometry.setDrawRange(0, 0);
  }
  if (DEBUG_TRAIL) validateTrail();

  // Vetores
  if ($("cVec").checked && d.sp > 0) {
    vecV.visible = true;
    vecV.position.set(rx, ry, rz);
    _v3v.set(v[0], v[1], v[2]).normalize();
    vecV.setDirection(_v3v);
    vecV.setLength(6, 1.2, 0.6); // Escala visual travada para legibilidade

    if (d.Bm && d.vperp > 1e-9 * d.sp) {
      const F = sc(cr(v, P.B), P.q);
      vecF.visible = true;
      vecF.position.set(rx, ry, rz);
      _v3f.set(F[0], F[1], F[2]).normalize();
      vecF.setDirection(_v3f);
      vecF.setLength(6, 1.2, 0.6);
    } else vecF.visible = false;
  } else {
    vecV.visible = vecF.visible = false;
  }

  // Campo magnético
  const showField = $("cField").checked;
  let axisAligned = false;
  if (showField && d.Bm) {
    camera.getWorldDirection(_v3cam);
    const align = _v3cam.dot(new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]));
    axisAligned = Math.abs(align) > CAM_B_ALIGN_COS;
    if (axisAligned) {
      // Câmera quase paralela a B: troca as setas pelos símbolos
      // ⊗ (entrando) / ⊙ (saindo), sempre de frente para a câmera.
      fieldAxisMarkers.visible = true;
      fieldAxisMarkers.position.set(gx, gy, gz);
      const mat = align > 0 ? fieldCrossMat : fieldDotMat;
      for (const s of fieldAxisMarkers.children) s.material = mat;
    } else {
      fieldAxisMarkers.visible = false;
    }
  } else {
    fieldAxisMarkers.visible = false;
  }
  fieldLinesInstanced.visible = showField && !axisAligned;
  fieldHeadsInstanced.visible = showField && !axisAligned;
  if (showField && !axisAligned) {
    // Ancora a grade visual no centro de guia
    fieldLinesInstanced.position.set(gx, gy, gz);
    fieldHeadsInstanced.position.set(gx, gy, gz);
  }

  // Disco guia
  if (d.Bm && $("cRadius").checked) {
    guideCircleMesh.visible = guideCenterMesh.visible = true;
    guideCenterMesh.position.set(gx, gy, gz);
    guideCircleMesh.position.set(gx, gy, gz);
    const q = new THREE.Quaternion().setFromUnitVectors(
      new THREE.Vector3(0, 0, 1),
      new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]),
    );
    guideCircleMesh.setRotationFromQuaternion(q);
    const R = d.r * renderScale;
    guideCircleMesh.scale.set(R, R, 1);
  } else {
    guideCircleMesh.visible = guideCenterMesh.visible = false;
  }

  renderer.render(scene, camera);
  renderGizmo();
}

/* =========================================================
 6. LOOP DE COMPUTAÇÃO & EVENTOS
 ========================================================= */
function step(el) {
  if (!playing) return;
  const run = Math.min(el, 0.05) * rate;
  const n = d.Bm ? Math.min(300, Math.max(1, Math.ceil(run / (d.T / 200)))) : 1,
    dt = run / n;
  for (let i = 0; i < n; i++) {
    const xa = x.slice(),
      va = v.slice();
    v = boris(v, P.q, gm, P.B, dt);
    x = add(x, sc(add(va, v), dt / 2));
    if (DEBUG_TRAIL) validateZeroFieldPhysics(xa, va, x, v, dt);
  }
  tSim += run;
  pushTrail(x);
  if (DEBUG_TRAIL) validateTrail();
}

function loop(t) {
  if (lastT == null) lastT = t;
  step((t - lastT) / 1000);
  lastT = t;
  renderScene();
  if (++fc % 12 === 0) info();
  requestAnimationFrame(loop);
}

function readouts() {
  const cards = [
    ["Raio r", d.Bm ? fmt(d.r, "m") : "—"],
    ["Período T", d.Bm ? fmt(d.T, "s") : "—"],
    ["|v|", fmt(d.sp, "m/s") + " (" + ((d.sp / C) * 100).toFixed(1) + "% c)"],
    ["v∥ (ao B)", d.Bm ? fmt(d.vpar, "m/s") : "—"],
    ["v⊥ (a B)", d.Bm ? fmt(d.vperp, "m/s") : "—"],
    ["Passo (Pitch)", d.Bm ? fmt(d.pitch, "m") : "—"],
    ["Fator γ", d.g.toFixed(4)],
  ];
  $("dash").innerHTML = cards.map((c) => `<div class="card"><b>${c[0]}</b><span>${c[1]}</span></div>`).join("");
  $("cap").innerHTML =
    `<b>${P.name}</b><br>q = ${fmt(P.q, "C")} · m = ${fmt(P.m, "kg")}<br>Modelo relativístico: γm = ${fmt(gm, "kg")}`;
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
}

// Controles de câmera (UI)
function setView(dir, up) {
  const target = controls.target.clone();
  camera.up.set(up[0], up[1], up[2]);
  camera.position.copy(target).addScaledVector(dir.clone().normalize(), 45);
  camera.lookAt(target);
  // camera.up mudou → OrbitControls precisa ser recriado para que o
  // arrasto do mouse gire em torno do eixo correto (ver resyncControlsUp).
  resyncControlsUp();
}
$("vTop").onclick = () => setView(new THREE.Vector3(0, 0, 1), [0, 1, 0]);
$("vSide").onclick = () => setView(new THREE.Vector3(0, 1, 0), [0, 0, 1]);
$("vYZ").onclick = () => setView(new THREE.Vector3(1, 0, 0), [0, 1, 0]);
$("v3d").onclick = () => setView(new THREE.Vector3(-20, 20, 25), [0, 1, 0]);

// Reposiciona a câmera na esfera de órbita (mesmo alvo, mesma distância,
// mesmo camera.up) na direção oposta a B, de modo que a visada da câmera
// fique paralela a B (campo "entrando na tela"). Retorna false quando não
// há campo definido. Usada pelo botão "Alinhar câmera a B" e pela posição
// inicial da câmera em reset().
function alignCameraToB(target, distance) {
  if (!d.Bm) return false;
  const Bh = new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]);
  camera.position.copy(target).addScaledVector(Bh, -distance);
  camera.lookAt(target);
  return true;
}

$("alignBtn").onclick = () => {
  // A câmera se move para olhar ao longo de B; o campo em si (P.B, val.Bx/By/Bz)
  // nunca é alterado — apenas a perspectiva de visualização.
  const target = controls.target.clone();
  const distance = camera.position.distanceTo(target) || 45;
  if (!alignCameraToB(target, distance)) return;
  controls.update();
  info();
};

$("play").onclick = (e) => {
  playing = !playing;
  e.currentTarget.innerHTML = playing
    ? '<i class="bi bi-pause-fill"></i> Pausar'
    : '<i class="bi bi-play-fill"></i> Iniciar';
  e.currentTarget.className = playing ? "pri" : "";
};

$("reset").onclick = () => {
  reset(true);
};
$("clr").onclick = () => {
  clearTrail(x);
};

/* =========================================================
 7. INICIALIZAÇÃO
 ========================================================= */
try {
  setKind("e");
  initThreeJS();
  reset(true);
  requestAnimationFrame(loop);

  // A tela de loading permanece visível por no mínimo LOADING_MIN_MS,
  // mesmo que o motor 3D inicialize antes, para que os créditos da equipe
  // sejam sempre legíveis.
  const elapsed = performance.now() - loadStart;
  const remaining = Math.max(0, LOADING_MIN_MS - elapsed);
  const loader = document.getElementById("loading-screen");
  if (loader) {
    setTimeout(() => {
      loader.style.opacity = "0";
      setTimeout(() => loader.remove(), 600);
    }, remaining);
  }
} catch (err) {
  const box = document.getElementById("loading-box");
  if (box)
    box.innerHTML = `<h1 class="loading-title" style="color:#EF4444">Falha WebGL</h1><p style="color:var(--mu)">Seu navegador não suporta aceleração 3D ou houve um erro interno.</p>`;
  console.error("Lorentz WebGL Error:", err);
}

/* =========================================================
 8. RECURSOS ADICIONAIS (ritmo, tema, exportação, ajuda…)
 ========================================================= */
const store = {
  get: (k) => { try { return localStorage.getItem(k); } catch (e) { return null; } },
  set: (k, s) => { try { localStorage.setItem(k, s); } catch (e) { /* ignora */ } },
};

// --- Ritmo da simulação (multiplicador logarítmico sobre o ritmo base) ---
let userSpeed = 1;
const baseStep = step;
step = function (el) {
  const r = rate;
  rate = r * userSpeed;
  try { baseStep(el); } finally { rate = r; }
};
function setSpeed(s) {
  userSpeed = s;
  $("spd").value = Math.log10(s);
  $("spdOut").textContent = s.toFixed(2) + "×";
}
$("spd").oninput = () => setSpeed(Math.pow(10, parseFloat($("spd").value)));
$("spdBtns").addEventListener("click", (e) => { if (e.target.dataset.s) setSpeed(parseFloat(e.target.dataset.s)); });
$("stepBtn").onclick = () => {
  const was = playing;
  playing = true;
  step(0.016);
  playing = was;
};

// --- Estado visível (rodando/pausado, regime relativístico) ---
function syncStatus() {
  $("stTxt").textContent = playing ? "Rodando" : "Pausado";
  $("stChip").classList.toggle("run", playing);
  $("tPlay").innerHTML = `<i class="bi bi-${playing ? "pause" : "play"}-fill"></i>`;
  const rel = d && d.g > 1.05;
  $("relChip").hidden = !rel;
  if (rel) $("relTxt").textContent = `Relativístico γ = ${d.g.toFixed(2)}`;
}
$("play").addEventListener("click", () => { syncStatus(); $("sr").textContent = playing ? "Simulação iniciada" : "Simulação pausada"; });
$("tPlay").onclick = () => $("play").click();
const baseInfo = info;
info = function () { baseInfo(); syncStatus(); updateAnalysis(); };

// --- Tema claro/escuro ---
function applyTheme(t) {
  document.documentElement.dataset.theme = t;
  $("btnTheme").innerHTML = `<i class="bi bi-${t === "dark" ? "sun" : "moon-stars"}"></i>`;
  if (renderer) renderer.setClearColor(t === "dark" ? 0x111827 : 0xffffff, 1);
  store.set("lorentz-theme", t);
}
const toggleTheme = () => applyTheme(document.documentElement.dataset.theme === "dark" ? "light" : "dark");
$("btnTheme").onclick = toggleTheme;
applyTheme(store.get("lorentz-theme") || "light");

// --- Opacidade do campo B ---
$("fieldOp").oninput = () => {
  const o = parseFloat($("fieldOp").value);
  fieldLinesInstanced.material.transparent = true;
  fieldLinesInstanced.material.opacity = o;
  $("fieldOpOut").textContent = o.toFixed(2);
};

// --- Análise: teoria × simulação ---
let E0 = 0;
const kinE = () => (d.g - 1) * P.m * C * C;
function updateAnalysis() {
  if (!d || !d.Bm) {
    ["Rt", "Rs", "Re", "Tt", "Ts", "Te", "Et", "Es", "Ee"].forEach((k) => ($("cmp" + k).textContent = "—"));
    return;
  }
  const gd = guide(), rs = nrm(sub(x, gd)), ts = d.vperp > 0 ? (2 * Math.PI * rs) / d.vperp : 0;
  const err = (a, b) => (a ? (((b - a) / a) * 100).toFixed(2) + "%" : "—");
  $("cmpRt").textContent = fmt(d.r, "m"); $("cmpRs").textContent = fmt(rs, "m"); $("cmpRe").textContent = err(d.r, rs);
  $("cmpTt").textContent = fmt(d.T, "s"); $("cmpTs").textContent = fmt(ts, "s"); $("cmpTe").textContent = err(d.T, ts);
  $("cmpEt").textContent = fmt(E0, "J"); $("cmpEs").textContent = fmt(kinE(), "J"); $("cmpEe").textContent = err(E0, kinE());
}
const baseReset = reset;
reset = function (f) { baseReset(f); E0 = kinE(); };
E0 = kinE();

// --- Tela cheia ---
$("tFull").onclick = () => (document.fullscreenElement ? document.exitFullscreen() : $("stage").requestFullscreen());

// --- Ajuda, atalhos e tutorial ---
$("aboutAuthors").innerHTML = $("loadAuthors").innerHTML;
const TOUR = [
  ["Bem-vindo", "Use <b>Iniciar</b> para simular. Arraste o palco para girar e use scroll para zoom."],
  ["Campo e velocidade", "Mude B e v no painel: a trajetória se adapta na hora. O ritmo é ajustável em <b>Simulação</b>."],
  ["Analise os resultados", "Compare teoria × simulação na seção Análise e ajuste a câmera, o plano de referência e os elementos exibidos."],
];
let tourI = 0;
function showTour(i) {
  tourI = i;
  $("tourStep").textContent = `Passo ${i + 1} de ${TOUR.length}`;
  $("tourTitle").textContent = TOUR[i][0];
  $("tourText").innerHTML = TOUR[i][1];
  $("tourPrev").hidden = i === 0;
  $("tourNext").textContent = i === TOUR.length - 1 ? "Concluir" : "Próximo";
  if (!$("tour").open) $("tour").showModal();
}
const endTour = () => { $("tour").close(); store.set("lorentz-tour", "1"); };
$("tourNext").onclick = () => (tourI === TOUR.length - 1 ? endTour() : showTour(tourI + 1));
$("tourPrev").onclick = () => showTour(tourI - 1);
$("tourSkip").onclick = endTour;
$("btnHelp").onclick = () => $("about").showModal();
$("aboutClose").onclick = () => $("about").close();
$("aboutTour").onclick = () => { $("about").close(); showTour(0); };

document.addEventListener("keydown", (e) => {
  if (e.target.closest("input, select, textarea") || e.ctrlKey || e.metaKey || e.altKey) return;
  const k = e.key.toLowerCase();
  const map = { " ": () => $("play").click(), ".": () => $("stepBtn").click(), r: () => reset(true), c: () => clearTrail(x), f: () => $("tFull").click(), t: toggleTheme, "?": () => $("btnHelp").click() };
  if (map[k]) { e.preventDefault(); map[k](); }
});

// --- Tela de loading: pular com clique/tecla; tutorial só na primeira visita ---
(function loadingExtras() {
  const l = document.getElementById("loading-screen");
  if (!l) return;
  $("loadHint").hidden = false;
  const skip = () => { l.style.opacity = "0"; setTimeout(() => l.remove(), 600); };
  l.addEventListener("click", skip);
  addEventListener("keydown", skip, { once: true });
  if (!store.get("lorentz-tour")) setTimeout(() => showTour(0), 2600);
})();
syncStatus();

/* =========================================================
 9. VISUAL: rastro espesso, rótulos, grade, régua, densidade, ajuda
 ========================================================= */
const dark = () => document.documentElement.dataset.theme === "dark";
const clamp = (a, lo, hi) => Math.min(hi, Math.max(lo, a));

// --- Rastro espesso (Line2): espessura, estilo e comprimento ---
const fat = new THREE.Group();
scene.add(fat);
let fatKey = "";
function updateFat() {
  trailLine.visible = false; // substitui o traço de 1 px original
  const on = $("cTrail").checked;
  fat.visible = on;
  const w = parseFloat($("trailW").value), fade = $("trailMode").value === "fade";
  const key = [trailPointCount, trajectorySegments.length, w, fade, kind, dark(), renderScale, MAX_TRAIL].join();
  if (!on || key === fatKey) return;
  fatKey = key;
  fat.children.slice().forEach((o) => { o.geometry.dispose(); o.material.dispose(); fat.remove(o); });
  const base = new THREE.Color(PART[kind].hex), bg = new THREE.Color(dark() ? 0x111827 : 0xffffff), col = new THREE.Color();
  const size = renderer.getSize(new THREE.Vector2()), total = Math.max(1, trailPointCount - 1);
  let idx = 0;
  trajectorySegments.forEach((s) => {
    const n = s.points.length, pos = [], cols = [];
    for (let i = 0; i < n - 1; i++)
      for (const j of [i, i + 1]) {
        const p = s.points[j];
        pos.push(p[0] * renderScale, p[1] * renderScale, p[2] * renderScale);
        col.copy(bg).lerp(base, fade ? 0.15 + 0.85 * ((idx + j) / total) : 1);
        cols.push(col.r, col.g, col.b);
      }
    idx += n;
    if (n < 2) return;
    const g = new THREE.LineSegmentsGeometry();
    g.setPositions(pos);
    g.setColors(cols);
    const m = new THREE.LineMaterial({ linewidth: w, vertexColors: true });
    m.resolution.set(size.x, size.y);
    const l = new THREE.LineSegments2(g, m);
    l.frustumCulled = false;
    fat.add(l);
  });
}
$("trailLen").oninput = () => {
  MAX_TRAIL = parseInt($("trailLen").value, 10);
  $("trailLenOut").textContent = MAX_TRAIL + " pts";
  while (trailPointCount > MAX_TRAIL && trajectorySegments.length) {
    const f = trajectorySegments[0];
    if (f.points.length <= 1) trajectorySegments.shift(); else f.points.shift();
    trailPointCount--;
  }
};
$("trailW").oninput = () => ($("trailWOut").textContent = $("trailW").value + " px");
addEventListener("resize", () => { fatKey = ""; });

// --- Rótulos v, F, B, r e linha do raio ---
function label(t, c) {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 64;
  const g = cv.getContext("2d");
  g.font = "bold 44px system-ui";
  g.textAlign = g.textBaseline = "center";
  g.textBaseline = "middle";
  g.fillStyle = c;
  g.fillText(t, 32, 34);
  const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(cv), transparent: true, depthTest: false }));
  s.scale.set(2.4, 2.4, 1);
  scene.add(s);
  return s;
}
const lv = label("v", "#F59E0B"), lf = label("F", "#8B5CF6"), lb = label("B", "#10B981"), lr = label("r", "#10B981");
const rLine = new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(), new THREE.Vector3()]), new THREE.LineBasicMaterial({ color: 0x10b981 }));
rLine.frustumCulled = false;
scene.add(rLine);

// --- Plano de referência: fixo na origem, dimensionado pela trajetória ---
// Grade por shader (linhas finas + maiores a cada 5 células, sem cintilação), eixos
// destacados, números com unidade, sombra da trajetória e aviso quando visto de lado.

const PLANE_GAP_FACTOR = 0.06; // fração do raio da órbita (menor = mais rente)
const refPlane = new THREE.Group();
scene.add(refPlane);
let planeKey = "", planeCell = 0, planeH = 0, tickKey = "", shadowKey = "", shadowT = 0;
let trailMinY = 0, planeY = 0, planeYInit = false; // altura (mundo) do ponto mais baixo e do plano
const planeMat = new THREE.ShaderMaterial({
  uniforms: { col: { value: new THREE.Color() }, c: { value: 1 }, H: { value: 30 }, o: { value: 1 } },
  vertexShader: "uniform float H;varying vec2 p;void main(){p=position.xy*H;gl_Position=projectionMatrix*modelViewMatrix*vec4(p,0.,1.);}",
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
  transparent: true, depthWrite: false, side: THREE.DoubleSide, extensions: { derivatives: true },
});
const planeMesh = new THREE.Mesh(new THREE.PlaneGeometry(2, 2), planeMat);
planeMesh.frustumCulled = false;
const ticks = new THREE.Group();
const originDot = new THREE.Mesh(new THREE.SphereGeometry(0.3, 12, 12), new THREE.MeshBasicMaterial({ color: 0x6b7280 }));
refPlane.add(planeMesh, ticks, originDot);
// Sombra da trajetória projetada no plano
const shadowGeo = new THREE.BufferGeometry();
const shadowAttr = new THREE.BufferAttribute(new Float32Array(10000 * 6), 3);
shadowAttr.setUsage(THREE.DynamicDrawUsage);
shadowGeo.setAttribute("position", shadowAttr);
shadowGeo.setDrawRange(0, 0);
const shadow = new THREE.LineSegments(shadowGeo, new THREE.LineBasicMaterial({ color: 0x6b7280, transparent: true, opacity: 0.45, depthWrite: false }));
shadow.frustumCulled = false;
scene.add(shadow);
// Projeção da partícula sobre o plano
const projLine = new THREE.Line(new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(), new THREE.Vector3()]), new THREE.LineBasicMaterial({ color: 0x6b7280, transparent: true, opacity: 0.7 }));
projLine.frustumCulled = false;
const projDot = new THREE.Mesh(new THREE.SphereGeometry(0.25, 12, 12), new THREE.MeshBasicMaterial({ color: 0x6b7280, transparent: true }));
scene.add(projLine, projDot);
const _pn = new THREE.Vector3(), _pu = new THREE.Vector3(), _pw = new THREE.Vector3(), _pf = new THREE.Vector3();
// Plano de referência único: horizontal (XZ), com o eixo vertical da cena sendo Y.
const PLANE_AXES = ["x", "z"];

// Cache de materiais de rótulo (um por texto e tema), compartilhado entre sprites.
const tickMatCache = new Map();
let tickCacheDark = null;
function tickMaterial(t) {
  const dk = dark();
  if (tickCacheDark !== dk) {
    tickMatCache.forEach((m) => { m.map.dispose(); m.dispose(); });
    tickMatCache.clear();
    tickCacheDark = dk;
  }
  let m = tickMatCache.get(t);
  if (!m) {
    const cv = document.createElement("canvas");
    cv.width = 192; cv.height = 64;
    const g = cv.getContext("2d");
    g.font = "600 34px system-ui"; g.textAlign = "center"; g.textBaseline = "middle";
    g.fillStyle = dk ? "#D1D5DB" : "#4B5563";
    g.fillText(t, 96, 34);
    const tex = new THREE.CanvasTexture(cv);
    tex.generateMipmaps = false;
    tex.minFilter = THREE.LinearFilter;
    m = new THREE.SpriteMaterial({ map: tex, transparent: true, depthTest: false, opacity: 0.9 });
    tickMatCache.set(t, m);
    // Evita crescimento indefinido do cache
    if (tickMatCache.size > 200) {
      const first = tickMatCache.keys().next().value;
      const old = tickMatCache.get(first);
      old.map.dispose(); old.dispose();
      tickMatCache.delete(first);
    }
  }
  return m;
}
function tickLabel(t) {
  const s = new THREE.Sprite(tickMaterial(t));
  s.scale.set(6, 2, 1);
  return s;
}
function buildTicks(names) {
  // Materiais são compartilhados/cacheados: apenas remove os sprites.
  ticks.children.slice().forEach((o) => ticks.remove(o));
  const step = 5 * planeCell * renderScale;
  const add1 = (t, x, y) => { const s = tickLabel(t); s.position.set(x, y, 0); ticks.add(s); };
  for (let k = 1; k <= 8 && k * step < planeH * 0.85; k++)
    for (const s of [1, -1]) {
      const t = fmt(s * k * 5 * planeCell, "m");
      add1(t, s * k * step, 2); // ao longo do 1º eixo
      add1(t, 4.2, s * k * step); // ao longo do 2º eixo
    }
  add1("0", 2.2, 2);
  add1(names[0], planeH * 0.93, -2.4);
  add1(names[1], -3, planeH * 0.93);
}
function updatePlane(p, gp) {
  const key = String(renderScale);
  if (key !== planeKey) {
    planeKey = key; planeH = 0; tickKey = ""; shadowKey = ""; planeYInit = false;
    planeCell = nice(4 / renderScale);
    refPlane.rotation.set(Math.PI / 2, 0, 0); // horizontal (normal ao longo de Y)
  }
  const q = refPlane.quaternion, c = planeCell * renderScale;
  _pu.set(1, 0, 0).applyQuaternion(q); _pw.set(0, 1, 0).applyQuaternion(q); _pn.set(0, 0, 1).applyQuaternion(q);

  // Sombra da trajetória e extensão necessária (throttle ~60 ms; imediato após mudar o plano)
  const nowMs = performance.now();
  const lastSeg = trajectorySegments[trajectorySegments.length - 1];
  const lastPt = lastSeg && lastSeg.points[lastSeg.points.length - 1];
  const skey = trailPointCount + "|" + trajectorySegments.length + "|" + key + "|" + (lastPt ? lastPt[0] + lastPt[1] + lastPt[2] : 0);
  if (skey !== shadowKey && (shadowKey === "" || nowMs - shadowT > 60)) {
    shadowKey = skey;
    shadowT = nowMs;
    const a = shadowAttr.array;
    let n = 0, R = Math.hypot(p.dot(_pu), p.dot(_pw)), pu = 0, pw = 0, minY = p.y;
    for (let si = 0; si < trajectorySegments.length; si++) {
      const pts = trajectorySegments[si].points;
      for (let i = 0; i < pts.length; i++) {
        const P0 = pts[i];
        _pf.set(P0[0] * renderScale, P0[1] * renderScale, P0[2] * renderScale);
        if (_pf.y < minY) minY = _pf.y;
        const du = _pf.dot(_pu), dw = _pf.dot(_pw);
        const rr = Math.hypot(du, dw);
        if (rr > R) R = rr;
        if (i > 0 && n + 6 <= a.length) {
          a[n++] = pu * _pu.x + pw * _pw.x; a[n++] = pu * _pu.y + pw * _pw.y; a[n++] = pu * _pu.z + pw * _pw.z;
          a[n++] = du * _pu.x + dw * _pw.x; a[n++] = du * _pu.y + dw * _pw.y; a[n++] = du * _pu.z + dw * _pw.z;
        }
        pu = du; pw = dw;
      }
    }
    trailMinY = minY;
    shadowGeo.setDrawRange(0, n / 3);
    shadowAttr.needsUpdate = true;
    // Extensão só cresce, em passos geométricos para evitar reconstruir marcações a todo momento
    const need = Math.max(30, Math.ceil((R * 1.3 + 2 * c) / c) * c);
    if (need > planeH) { planeH = Math.max(need, planeH * 1.5); tickKey = ""; }
  }
  const tk = planeH + "|" + planeCell + "|" + renderScale + "|" + dark();
  if (tk !== tickKey) { tickKey = tk; buildTicks(PLANE_AXES); }
  // Plano um pouco abaixo: desloca-se ao longo da normal, para o lado "de baixo" da vista
  // (usa camera.up, então não desliza ao orbitar). Vertical de lado → deslocamento nulo.
  // Plano horizontal sempre ABAIXO da trajetória (eixo Y do mundo), a uma distância
  // proporcional ao raio visual da órbita. Ajuste PLANE_GAP_FACTOR.
  const orbitR = d.Bm ? d.r * renderScale : 15;
  // Ponto mais baixo: mínimo entre o rastro já percorrido e a órbita prevista
  // (centro de guia − raio projetado em Y). Assim o plano fica sob a trajetória
  // tanto para elétron (órbita acima da origem) quanto para próton (abaixo).
  const orbitLow = d.Bm ? gp.y - orbitR * Math.sqrt(Math.max(0, 1 - d.Bh[1] * d.Bh[1])) : p.y;
  const lowY = Math.min(trailMinY, orbitLow, p.y);
  const targetY = lowY - Math.max(0.6, PLANE_GAP_FACTOR * orbitR);
  if (!planeYInit) { planeY = targetY; planeYInit = true; }
  else planeY += (targetY - planeY) * 0.2; // suaviza para o plano não tremer
  // Plano horizontal: normal _pn = (0,−1,0) ⇒ posição = _pn · planeOff, com planeOff = −planeY.
  const planeOff = -planeY;
  refPlane.position.copy(_pn).multiplyScalar(planeOff);
  shadow.position.copy(refPlane.position);
  // Aviso de "plano de lado": a opacidade cai quando a câmera fica paralela a ele
  camera.getWorldDirection(_v3cam);
  const f = Math.abs(_v3cam.dot(_pn)), k0 = Math.min(1, Math.max(0, (f - 0.04) / 0.26)), face = k0 * k0 * (3 - 2 * k0);
  const U = planeMat.uniforms;
  U.col.value.set(dark() ? 0x9ca3af : 0x4b6cb7); U.c.value = c; U.H.value = planeH; U.o.value = face;
  ticks.visible = face > 0.25;
  shadow.material.opacity = 0.45 * Math.max(face, 0.35);
  // Projeção da partícula
  const dist = p.dot(_pn) - planeOff;
  _pf.copy(p).addScaledVector(_pn, -dist);
  const t = Math.min(1, Math.max(0, (Math.abs(dist) - 0.05 * c) / (0.35 * c))), kk = t * t * (3 - 2 * t);
  projLine.material.opacity = 0.7 * kk; projDot.material.opacity = kk;
  projLine.visible = projDot.visible = kk > 0.01;
  const pa = projLine.geometry.attributes.position;
  pa.setXYZ(0, p.x, p.y, p.z); pa.setXYZ(1, _pf.x, _pf.y, _pf.z); pa.needsUpdate = true;
  projDot.position.copy(_pf);
}

// --- Densidade do campo B ---
$("fieldN").oninput = () => {
  const n = parseInt($("fieldN").value, 10);
  fieldHalf = (n - 1) / 2;
  $("fieldNOut").textContent = n + " × " + n;
  drawFieldGrid();
};

// --- Ajuda contextual ("?") ---
const HELP = {
  r: "Raio da órbita: r = γmv⊥ / (|q|B). Cresce com a velocidade e diminui com o campo.",
  T: "Período de uma volta: T = 2πγm / (|q|B). Não depende de v⊥ (no regime clássico).",
  v: "Módulo da velocidade. Em campo magnético puro ele é constante: B só muda a direção.",
  par: "Componente de v paralela a B. Não sofre força e define o avanço da hélice.",
  perp: "Componente de v perpendicular a B. É ela que gira a partícula em círculo.",
  pitch: "Passo da hélice: distância percorrida ao longo de B em um período (v∥ · T).",
  g: "Fator de Lorentz γ = 1/√(1 − v²/c²). Perto de 1 vale a mecânica clássica.",
  cmp: "Compara a fórmula analítica com o valor medido na simulação. O erro mostra a qualidade do integrador.",
};
const HELP_KEYS = { "Raio r": "r", "Período T": "T", "|v|": "v", "v∥ (ao B)": "par", "v⊥ (a B)": "perp", "Passo (Pitch)": "pitch", "Fator γ": "g" };
const prevReadouts = readouts;
readouts = function () {
  prevReadouts();
  document.querySelectorAll("#dash .card").forEach((c) => {
    const k = HELP_KEYS[c.firstChild.textContent];
    if (k) c.firstChild.insertAdjacentHTML("beforeend", ` <button class="help" type="button" data-help="${k}" aria-label="O que significa?">?</button>`);
  });
};
document.addEventListener("click", (e) => {
  const b = e.target.closest(".help"), tip = $("tip");
  if (!b) { tip.hidden = true; return; }
  tip.textContent = HELP[b.dataset.help] || "";
  tip.hidden = false;
  const r = b.getBoundingClientRect();
  tip.style.left = clamp(r.left, 8, innerWidth - 250) + "px";
  tip.style.top = r.bottom + 6 + "px";
});
readouts();

// --- Atualizações por quadro (antes de desenhar) ---
const nice = (a) => { const e = Math.pow(10, Math.floor(Math.log10(a))), m = a / e; return (m < 2 ? 1 : m < 5 ? 2 : 5) * e; };
let sbKey = "", legTxt = "";
const legGridEl = $("legGrid"), legGridTxtEl = $("legGridTxt");
const prevRender = renderScene;
renderScene = function () {
  updateFat();
  const on = $("cLabels").checked, p = particleMesh.position;
  const g = guide(), gp = new THREE.Vector3(g[0] * renderScale, g[1] * renderScale, g[2] * renderScale);
  lv.visible = on && vecV.visible;
  if (lv.visible) lv.position.copy(p).addScaledVector(_v3v.set(v[0], v[1], v[2]).normalize(), 7.6);
  lf.visible = on && vecF.visible;
  if (lf.visible) {
    const F = sc(cr(v, P.B), P.q);
    lf.position.copy(p).addScaledVector(_v3f.set(F[0], F[1], F[2]).normalize(), 7.6);
  }
  lb.visible = on && !!d.Bm && $("cField").checked;
  if (lb.visible) lb.position.copy(gp).addScaledVector(_v3cam.set(d.Bh[0], d.Bh[1], d.Bh[2]), 9);
  const showR = !!d.Bm && $("cRadius").checked;
  rLine.visible = showR;
  lr.visible = on && showR;
  if (showR) {
    // Atualiza o atributo existente (setFromPoints recriava o buffer a cada quadro)
    const ra = rLine.geometry.attributes.position;
    ra.setXYZ(0, gp.x, gp.y, gp.z);
    ra.setXYZ(1, p.x, p.y, p.z);
    ra.needsUpdate = true;
    lr.position.copy(gp).lerp(p, 0.5).addScalar(0.8);
  }
  fieldAxisMarkers.children.forEach((c, i) => (c.visible = i < (2 * fieldHalf + 1) ** 2));
  const gOn = $("cGrid").checked;
  refPlane.visible = gOn;
  if (!gOn) projLine.visible = projDot.visible = false;
  shadow.visible = gOn;
  if (gOn) updatePlane(p, gp);
  if (legGridEl.hidden === gOn) legGridEl.hidden = !gOn;
  if (gOn) {
    const lt = "plano: " + fmt(planeCell, "m") + " / célula";
    if (lt !== legTxt) { legTxt = lt; legGridTxtEl.textContent = lt; }
  }
  // Régua de escala (~100 px)
  const sb = $("scalebar"), sOn = $("cScale").checked;
  sb.hidden = !sOn;
  if (sOn) {
    const H = renderer.domElement.clientHeight || 1, dist = camera.position.distanceTo(controls.target);
    const physPerPx = (2 * dist * Math.tan((camera.fov * Math.PI) / 360)) / H / renderScale;
    const L = nice(100 * physPerPx), key = L + "|" + Math.round(L / physPerPx);
    if (key !== sbKey) {
      sbKey = key;
      $("sbLine").style.width = L / physPerPx + "px";
      $("sbLabel").textContent = fmt(L, "m");
    }
  }
  prevRender();
};

// Trava a página no topo: o foco em controles pode rolar o body (overflow:hidden)
// e deixar uma faixa vazia na parte inferior da tela.
function lockPageScroll() {
  const s = document.scrollingElement;
  if (s && s.scrollTop) s.scrollTop = 0;
  if (document.body.scrollTop) document.body.scrollTop = 0;
}
addEventListener("scroll", lockPageScroll);
document.addEventListener("focusin", () => requestAnimationFrame(lockPageScroll));