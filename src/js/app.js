"use strict";

// Marca o início do carregamento para garantir um tempo mínimo de
// exibição da tela de loading (créditos da equipe), independente da
// velocidade de inicialização do motor 3D.
const LOADING_MIN_MS = 5000;
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
const MAX_TRAIL = 3000;
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
const CFG = [
  ["gB", "Bx", "Bx", -2, 2, 0.1, "T"],
  ["gB", "By", "By", -2, 2, 0.1, "T"],
  ["gB", "Bz", "Bz", -2, 2, 0.1, "T"],
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
        // A escala orbital anterior pode tornar cada passo retilíneo
        // gigantesco no espaço visual. Recalibrar somente na troca de
        // regime mantém os snapshots físicos intactos e estabiliza a tela.
        if (previousRegime !== nextRegime) fit();
        rate = d.Bm ? d.T / 2 : 1 / 3;
        readouts();
        info();
        drawFieldGrid();
      } else reset(false);
    }
  };
  rng.oninput = () => set(parseFloat(rng.value));
  num.onchange = () => set(parseFloat(num.value) || 0);
  ctl[id] = set;
});

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
  const count = 5 * 5 * 5; // Grid de 125 setas
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
  for (let i = 0; i < 25; i++) {
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
  fieldLinesInstanced.count = 125;
  fieldHeadsInstanced.count = 125;

  const dir = new THREE.Vector3(d.Bh[0], d.Bh[1], d.Bh[2]).normalize();
  const axis = Math.abs(dir.x) < 0.9 ? new THREE.Vector3(1, 0, 0) : new THREE.Vector3(0, 1, 0);
  const e1 = new THREE.Vector3().crossVectors(dir, axis).normalize();
  const e2 = new THREE.Vector3().crossVectors(dir, e1).normalize();

  const dummy = new THREE.Object3D();
  const q = new THREE.Quaternion().setFromUnitVectors(new THREE.Vector3(0, 1, 0), dir);
  const L = 6; // Comprimento visual no WebGL
  let idx = 0,
    mIdx = 0;

  for (let i = -2; i <= 2; i++) {
    for (let j = -2; j <= 2; j++) {
      const base = new THREE.Vector3().addScaledVector(e1, i * L * 1.6).addScaledVector(e2, j * L * 1.6);

      // Marcador ⊗/⊙ desta coluna: uma única posição na mesma grade
      // e1/e2 das setas, sem repetição em profundidade (k).
      fieldAxisMarkers.children[mIdx++].position.copy(base);

      for (let k = -2; k <= 2; k++) {
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