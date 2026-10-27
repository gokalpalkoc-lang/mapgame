'use strict';
/* =====================================================================
   Frontier — browser territorial expansion game
   Vanilla JS + Canvas. No dependencies.

   Sections:
     1. Constants & state         6. Rails & trains
     2. Map generation            7. Diplomacy
     3. Per-tick scan & economy   8. AI
     4. Attacks                   9. Game loop & win conditions
     5. Buildings, nukes, fallout 10. Camera, input, UI, rendering
   ===================================================================== */

// ============================================================ 1. Constants
const H = 100;                        // map rows; columns follow the screen's aspect ratio
const MIN_W = 100, MAX_W = 200;
let W = 160, N = W * H;
const TICK_MS = 100;

const NEUTRAL = -1, OBSTACLE = -2, FALLOUT = -3;
const B_CITY = 1, B_POST = 2, B_SILO = 3, B_FACTORY = 4;
const BUILD_NAME = { [B_CITY]: 'City', [B_POST]: 'Defense Post', [B_SILO]: 'Missile Silo', [B_FACTORY]: 'Factory' };
const BUILD_SIZE = { [B_CITY]: 3, [B_POST]: 3, [B_SILO]: 3, [B_FACTORY]: 3 }; // footprint is size x size cells
const MODE_TYPE = { factory: B_FACTORY, city: B_CITY, post: B_POST, silo: B_SILO };

const COST = { factory: 1000, city: 1500, post: 1000, silo: 5000, nuke: 3000, recruit: 500 };
const NEUTRAL_COST = 5;               // troops per neutral cell
const FRONT_RATE = 0.05, FRONT_MAX_STEPS = 8; // cells a front can resolve per tick
const ATTACK_LOSS = 2.5;              // attacker loses this multiple of the defender's loss per cell, plus NEUTRAL_COST
const GEN_FALLOFF = 0.5;              // troop generation slows as the pool fills: rate x (1 - GEN_FALLOFF * troops/cap)
const ALLY_WIN_TICKS = 600;           // an all-allies victory must hold this long with no neutral land left
const TROOPS_PER_CELL = 0.5;          // troop generation per owned cell per tick
const CAP_PER_CELL = 100;
const CITY_CAP = 2000;                // extra troop cap per city
const CITY_DEF = 1.5;                 // defense multiplier on a city's cells
const POST_RADIUS = 6, POST_MULT = 2; // defense post radius (from its center) and multiplier
const NUKE_RADIUS = 5, FALLOUT_TICKS = 300, NUKE_FLIGHT = 25, NUKE_RELOAD = 300;
const RECRUIT_TROOPS = 1000;
// Gold comes only from trains: a factory lays rails to nearby buildings and
// sends a train down each one every TRAIN_INTERVAL ticks.
const RAIL_RANGE = 30;                // max track length in cells
const RAIL_MAX_LINKS = 4;             // rails per factory
const TRAIN_INTERVAL = 40;            // ticks between departures on one rail
const TRAIN_SPEED = 0.5;              // cells per tick
const TRAIN_BASE = 30, TRAIN_PER_CELL = 3; // gold per delivery: base + per cell of track
const CITY_TRADE = 1.5;               // deliveries into a city pay this much more
const ALLY_SHARE = 0.5;               // an ally receiving your train earns this share as well
const TRAITOR_TICKS = 600;
const THREAT_MEMORY = 100;
const PROPOSAL_TTL = 150;
const PAIR_COOLDOWN = 300;
const WIN_SHARE = 0.6;
const AI_INTERVAL = 10;               // ticks between AI evaluations (1 s)
const START_TROOPS = 300, START_GOLD = COST.factory, START_RADIUS = 3;

const PERSONALITIES = {
  aggressive: { label: 'Aggressive', attackAt: 0.6, commit: 0.6,  factoryChance: 0.5, postChance: 0.2, cityChance: 0.4, allyChance: 0.45, breakChance: 0.15 },
  defensive:  { label: 'Defensive',  attackAt: 0.9, commit: 0.45, factoryChance: 0.6, postChance: 0.8, cityChance: 0.5, allyChance: 0.8,  breakChance: 0.03 },
  economic:   { label: 'Economic',   attackAt: 0.8, commit: 0.5,  factoryChance: 0.9, postChance: 0.4, cityChance: 0.9, allyChance: 0.7,  breakChance: 0.06 },
};

// ---------------------------------------------------------------- State
let owner, bldgAt, fallout;  // per cell: faction or terrain, building id (0 = none), fallout timer
let terrain;                 // per cell RGB of the bare land
let spawns = [];
let buildings = [];          // { id, type, x, y, size, center, owner }: x/y is the top-left corner
const bById = new Map();
let nextBldgId = 1;
let falloutList = [];        // cell indices currently in fallout
let rails = [], trains = [], railsDirty = true;
let factions = [];
let attacks = [];
let missiles = [];
let effects = [];
let proposals = [];          // alliance proposals waiting on the player
const pairCooldown = new Map();
let tick = 0, paused = false, speed = 1, gameOver = false, ended = false, started = false, allyHold = 0;
let claimable = 0;           // non-obstacle cells
let S = null;                // per-tick scan results
let logLines = [];
let hover = -1, buildMode = null, player = null;
let dirty = true, dirtyUI = true, dirtyLog = true;

// -------------------------------------------------------------- Helpers
const rand = n => Math.floor(Math.random() * n);
const cx = i => i % W;
const cy = i => (i / W) | 0;
const NB = [[1, 0], [-1, 0], [0, 1], [0, -1]];
const NB8 = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
function forNeighbors(i, fn) {
  const x = i % W, y = (i / W) | 0;
  if (x > 0) fn(i - 1);
  if (x < W - 1) fn(i + 1);
  if (y > 0) fn(i - W);
  if (y < H - 1) fn(i + W);
}
function adjacentTo(i, f) {
  const x = i % W, y = (i / W) | 0;
  return (x > 0 && owner[i - 1] === f) || (x < W - 1 && owner[i + 1] === f) ||
         (y > 0 && owner[i - W] === f) || (y < H - 1 && owner[i + W] === f);
}
// True when any cell within Chebyshev distance r of i passes test (or, with all=true, every cell does)
function around(i, r, test, all) {
  const x = cx(i), y = cy(i);
  for (let yy = y - r; yy <= y + r; yy++)
    for (let xx = x - r; xx <= x + r; xx++) {
      const ok = xx >= 0 && yy >= 0 && xx < W && yy < H && test(yy * W + xx);
      if (ok !== !!all) return !all;
    }
  return !!all;
}
function dist2(a, b) { const dx = cx(a) - cx(b), dy = cy(a) - cy(b); return dx * dx + dy * dy; }
function fmt(n) {
  n = Math.floor(n);
  if (n >= 1e6) return (n / 1e6).toFixed(2) + 'M';
  if (n >= 1e4) return (n / 1e3).toFixed(1) + 'k';
  return n.toLocaleString();
}
function clock(t) { const sec = Math.floor(t / 10); return String(Math.floor(sec / 60)).padStart(2, '0') + ':' + String(sec % 60).padStart(2, '0'); }
function pairKey(a, b) { return a < b ? a + '-' + b : b + '-' + a; }
function isTraitor(f) { return tick < f.traitorUntil; }
function addLog(text, cls) {
  logLines.push({ t: tick, text, cls: cls || '' });
  if (logLines.length > 60) logLines.shift();
  dirtyLog = true;
}
function hexRGB(h) { const v = parseInt(h.slice(1), 16); return [v >> 16, (v >> 8) & 255, v & 255]; }
function mix(a, b, t) { return [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t]; }

// Buildings: footprint of a building of this type centered on cell i
function footprint(type, i) {
  const s = BUILD_SIZE[type], o = (s - 1) >> 1;
  return { x: cx(i) - o, y: cy(i) - o, s };
}
function forFootprint(x, y, s, fn) { for (let yy = y; yy < y + s; yy++) for (let xx = x; xx < x + s; xx++) fn(yy * W + xx); }
function bAt(i) { return bldgAt[i] ? bById.get(bldgAt[i]) : null; }
// Squared distance from a building's center to the center of cell i
function bDist2(b, i) { const dx = cx(i) + 0.5 - (b.x + b.size / 2), dy = cy(i) + 0.5 - (b.y + b.size / 2); return dx * dx + dy * dy; }

// ====================================================== 2. Map generation
// Smooth value noise in [0, 1]: a coarse random lattice, smoothstep-interpolated
function noiseField(scale) {
  const gw = Math.ceil(W / scale) + 2, gh = Math.ceil(H / scale) + 2;
  const g = Float32Array.from({ length: gw * gh }, Math.random);
  const out = new Float32Array(N);
  for (let i = 0; i < N; i++) {
    const fx = cx(i) / scale, fy = cy(i) / scale, x0 = fx | 0, y0 = fy | 0;
    let tx = fx - x0, ty = fy - y0;
    tx = tx * tx * (3 - 2 * tx); ty = ty * ty * (3 - 2 * ty);
    const a = g[y0 * gw + x0], b = g[y0 * gw + x0 + 1], c = g[(y0 + 1) * gw + x0], d = g[(y0 + 1) * gw + x0 + 1];
    out[i] = a + (b - a) * tx + (c - a) * ty + (a - b - c + d) * tx * ty;
  }
  return out;
}

const LAND_LO = hexRGB('#aebf86'), LAND_HI = hexRGB('#d2dcae');
const ROCK_LO = hexRGB('#5f6472'), ROCK_HI = hexRGB('#8f95a3'), ROCK_EDGE = hexRGB('#474b57');

function paintTerrain() {
  terrain = new Uint8ClampedArray(N * 3);
  const coarse = noiseField(14), fine = noiseField(4);
  for (let i = 0; i < N; i++) {
    const n = coarse[i] * 0.7 + fine[i] * 0.3;
    let c;
    if (owner[i] === OBSTACLE) {
      let edge = false;
      forNeighbors(i, q => { if (owner[q] !== OBSTACLE) edge = true; });
      c = mix(ROCK_LO, ROCK_HI, n);
      if (edge) c = mix(c, ROCK_EDGE, 0.45);
    } else c = mix(LAND_LO, LAND_HI, n);
    terrain[i * 3] = c[0]; terrain[i * 3 + 1] = c[1]; terrain[i * 3 + 2] = c[2];
  }
}

function generateMap() {
  N = W * H;
  owner = new Int8Array(N); bldgAt = new Int32Array(N); fallout = new Uint16Array(N);
  const m = 14;                       // inset from the corners, clear of the HUD panels
  spawns = [[m, m], [W - 1 - m, m], [m, H - 1 - m], [W - 1 - m, H - 1 - m]].map(([x, y]) => y * W + x);
  for (let attempt = 0; attempt < 100; attempt++) {
    owner.fill(NEUTRAL); bldgAt.fill(0); fallout.fill(0);
    buildings = []; bById.clear(); falloutList = [];

    // Obstacle blobs via random walks until ~10% of the map
    const target = Math.floor(N * 0.10);
    let count = 0;
    while (count < target) {
      let x = rand(W), y = rand(H);
      const size = 8 + rand(50);
      for (let k = 0; k < size && count < target; k++) {
        const i = y * W + x;
        if (owner[i] !== OBSTACLE) { owner[i] = OBSTACLE; count++; }
        const d = NB[rand(4)];
        x = Math.max(0, Math.min(W - 1, x + d[0]));
        y = Math.max(0, Math.min(H - 1, y + d[1]));
      }
    }
    // Clear spawn areas
    const clear = START_RADIUS + 2;
    for (const s of spawns)
      for (let y = cy(s) - clear; y <= cy(s) + clear; y++)
        for (let x = cx(s) - clear; x <= cx(s) + clear; x++)
          if (x >= 0 && y >= 0 && x < W && y < H) owner[y * W + x] = NEUTRAL;

    // Connectivity: all spawns must be reachable from spawn 0
    const seen = new Uint8Array(N);
    const q = [spawns[0]]; seen[q[0]] = 1;
    while (q.length) {
      const i = q.pop();
      forNeighbors(i, n => { if (!seen[n] && owner[n] !== OBSTACLE) { seen[n] = 1; q.push(n); } });
    }
    if (!spawns.every(i => seen[i])) continue;
    for (let i = 0; i < N; i++) if (!seen[i]) owner[i] = OBSTACLE; // seal unreachable pockets

    claimable = 0;
    for (let i = 0; i < N; i++) if (owner[i] !== OBSTACLE) claimable++;
    paintTerrain();
    return;
  }
  throw new Error('Could not generate a connected map');
}

function initFactions() {
  const ais = ['aggressive', 'defensive', 'economic'].sort(() => Math.random() - 0.5);
  const defs = [
    { name: 'You',     color: '#4f8ef7', isPlayer: true },
    { name: 'Crimson', color: '#e5484d', p: ais[0] },
    { name: 'Verdant', color: '#2f9e64', p: ais[1] },
    { name: 'Amber',   color: '#f2a33a', p: ais[2] },
  ];
  factions = defs.map((d, i) => ({
    id: i, name: d.name, color: d.color, rgb: hexRGB(d.color), isPlayer: !!d.isPlayer,
    personality: d.p ? PERSONALITIES[d.p] : null,
    troops: START_TROOPS, gold: START_GOLD, cells: 0, cap: CAP_PER_CELL, troopGen: 0, goldGen: 0,
    alive: true, commit: d.p ? 0.2 : 0.5,
    allies: new Set(), traitorUntil: 0, threat: new Map(), state: 'Build', nukeReady: 0,
  }));
  player = factions[0];
  factions.forEach((f, i) => {
    const s = spawns[i];
    around(s, START_RADIUS, c => { claimCell(c, f); return false; });
    addBuilding(f, s, B_CITY);          // free capital
  });
}

// ================================================ 3. Per-tick scan & economy
// One pass over the grid: border cell counts, neutral frontier per faction,
// adjacency between factions, centroids, and building tallies.
function scan() {
  const F = factions.length;
  const s = {
    border: new Int32Array(F), neutralAdj: [], adj: [],
    sx: new Float64Array(F), sy: new Float64Array(F),
    cities: new Int32Array(F), silos: [], posts: [], factories: [],
  };
  for (let f = 0; f < F; f++) { s.neutralAdj.push([]); s.adj.push(new Int32Array(F)); s.silos.push([]); s.posts.push([]); s.factories.push([]); }
  let o = 0, border = false;
  const check = n => {
    const q = owner[n];
    if (q === NEUTRAL) { border = true; s.neutralAdj[o].push(n); }
    else if (q >= 0 && q !== o) { border = true; s.adj[o][q]++; }
  };
  for (let i = 0; i < N; i++) {
    o = owner[i]; if (o < 0) continue;
    const x = i % W, y = (i / W) | 0;
    s.sx[o] += x; s.sy[o] += y;
    border = false;
    if (x > 0) check(i - 1);
    if (x < W - 1) check(i + 1);
    if (y > 0) check(i - W);
    if (y < H - 1) check(i + W);
    if (border) s.border[o]++;
  }
  for (const b of buildings) {
    if (b.type === B_CITY) s.cities[b.owner]++;
    else if (b.type === B_SILO) s.silos[b.owner].push(b);
    else if (b.type === B_POST) s.posts[b.owner].push(b);
    else if (b.type === B_FACTORY) s.factories[b.owner].push(b);
  }
  S = s;
}

// Troops grow with land; gold is earned by trains (see updateRails)
function economy() {
  for (const f of factions) {
    if (!f.alive) continue;
    f.cap = f.cells * CAP_PER_CELL + S.cities[f.id] * CITY_CAP;
    const fill = f.cap > 0 ? Math.min(1, f.troops / f.cap) : 0;
    f.troopGen = f.cells * TROOPS_PER_CELL * (1 - GEN_FALLOFF * fill);
    f.troops = Math.min(f.cap, f.troops + f.troopGen);
  }
}

// Defense of one cell: defender troops / defender border cells,
// doubled near a defense post, x1.5 on a city. This is what the defender
// loses when the cell falls; the attacker must beat attackCost(def).
function attackCost(def) { return def * ATTACK_LOSS + NEUTRAL_COST; }
function shielded(i, d) { return S.posts[d.id].some(p => bDist2(p, i) <= POST_RADIUS * POST_RADIUS); }
function cellDefense(i, d) {
  let def = d.troops / Math.max(1, S.border[d.id]);
  if (shielded(i, d)) def *= POST_MULT;
  const b = bAt(i);
  if (b && b.type === B_CITY && b.owner === d.id) def *= CITY_DEF;
  return def;
}

function claimCell(i, f) {
  const old = owner[i];
  if (old === f.id) return;
  if (old >= 0) factions[old].cells--;
  owner[i] = f.id; f.cells++;
  const b = bAt(i);
  if (b && b.center === i && b.owner !== f.id) {   // buildings follow their center cell
    const prev = factions[b.owner];
    if (f.isPlayer || prev.isPlayer)
      addLog(`<b>${f.name}</b> captured a ${BUILD_NAME[b.type]} from <b>${prev.name}</b>`, f.isPlayer ? 'good' : 'bad');
    b.owner = f.id; railsDirty = true;
  }
  if (old >= 0 && factions[old].cells <= 0) eliminate(factions[old]);
  dirty = true;
}

function eliminate(f) {
  if (!f.alive) return;
  f.alive = false; f.troops = 0; f.gold = 0; f.cells = 0; f.state = 'Dead';
  for (const a of attacks) if (a.attacker === f.id) a.done = true;
  for (const g of f.allies) factions[g].allies.delete(f.id);
  f.allies.clear();
  proposals = proposals.filter(p => p.from !== f.id);
  addLog(f.isPlayer ? 'You have been eliminated!' : `<b>${f.name}</b> has been eliminated!`, f.isPlayer ? 'bad' : 'good');
  dirtyUI = true;
}

// =========================================================== 4. Attacks
// An attack is a front: a set of target cells adjacent to the attacker that
// is consumed a few cells per tick, so fights play out over time.
function addFrontier(a, c) { if (!a.set.has(c)) { a.set.add(c); a.frontier.push(c); } }

function launchAttack(att, target, startCell) {
  if (!att.alive) return false;
  if (target >= 0 && (att.allies.has(target) || !factions[target].alive)) return false;
  const force = Math.floor(att.troops * att.commit);
  if (force < NEUTRAL_COST) { if (att.isPlayer) flash('Not enough troops committed.', true); return false; }
  const frontier = [];
  if (target === NEUTRAL) {
    if (startCell == null || owner[startCell] !== NEUTRAL || !adjacentTo(startCell, att.id)) return false;
    frontier.push(startCell);
  } else {
    for (let i = 0; i < N; i++) if (owner[i] === target && adjacentTo(i, att.id)) frontier.push(i);
    if (!frontier.length) { if (att.isPlayer) flash('You do not share a border with that faction.', true); return false; }
  }
  att.troops -= force;
  let a = attacks.find(a => a.attacker === att.id && a.target === target && !a.done);
  if (a) { a.force += force; for (const c of frontier) addFrontier(a, c); }
  else {
    a = { attacker: att.id, target, force, frontier: [], set: new Set(), done: false, started: tick };
    for (const c of frontier) addFrontier(a, c);
    attacks.push(a);
  }
  if (target >= 0) {
    const t = factions[target];
    const prev = t.threat.get(att.id);
    t.threat.set(att.id, { force: (prev ? prev.force : 0) + force, tick });
    if (att.isPlayer) addLog(`You attack <b>${t.name}</b> with ${fmt(force)} troops`, 'good');
    else if (t.isPlayer) addLog(`<b>${att.name}</b> attacks you with ${fmt(force)} troops!`, 'bad');
  }
  dirtyUI = true;
  return true;
}

function processAttacks() {
  for (const a of attacks) {
    if (a.done) continue;
    const att = factions[a.attacker];
    if (!att.alive) { a.done = true; continue; }
    if (a.target >= 0) {
      const t = factions[a.target];
      if (!t.alive || att.allies.has(a.target)) { att.troops += a.force; a.done = true; continue; }
    }
    let steps = Math.min(FRONT_MAX_STEPS, Math.max(1, Math.ceil(a.frontier.length * FRONT_RATE)));
    while (steps-- > 0 && !a.done) {
      if (a.frontier.length === 0) {           // nothing left to take: survivors go home
        att.troops = Math.min(att.cap, att.troops + a.force);
        a.done = true; break;
      }
      const k = rand(a.frontier.length);
      const c = a.frontier[k];
      a.frontier[k] = a.frontier[a.frontier.length - 1]; a.frontier.pop(); a.set.delete(c);
      if (owner[c] !== a.target || !adjacentTo(c, a.attacker)) continue;

      if (a.target === NEUTRAL) {
        if (a.force >= NEUTRAL_COST) {
          a.force -= NEUTRAL_COST;
          claimCell(c, att);
          forNeighbors(c, n => { if (owner[n] === NEUTRAL) addFrontier(a, n); });
        } else a.done = true;
      } else {
        const t = factions[a.target];
        const def = cellDefense(c, t), cost = attackCost(def);
        if (a.force > cost) {
          a.force -= cost;
          t.troops = Math.max(0, t.troops - def);
          claimCell(c, att);
          forNeighbors(c, n => { if (owner[n] === a.target) addFrontier(a, n); });
          if (!t.alive) { att.troops += a.force; a.done = true; }
        } else {
          a.done = true; a.force = 0;
          if (att.isPlayer) addLog(`Your attack on <b>${t.name}</b> was repelled`, 'bad');
          else if (t.isPlayer) addLog(`You repelled <b>${att.name}</b>'s attack`, 'good');
        }
      }
    }
  }
  attacks = attacks.filter(a => !a.done);
}

// ============================================ 5. Buildings, nukes, fallout
// Why a building of this type can't go at cell i ('' when it can)
function canPlace(f, i, type) {
  const { x, y, s } = footprint(type, i);
  if (x < 0 || y < 0 || x + s > W || y + s > H) return 'Too close to the edge of the map.';
  let why = '';
  forFootprint(x, y, s, c => {
    if (why) return;
    if (owner[c] !== f.id) why = `A ${BUILD_NAME[type]} needs ${s}×${s} tiles of your own land.`;
    else if (bldgAt[c]) why = 'That overlaps another building.';
  });
  return why;
}

function addBuilding(f, i, type) {
  const { x, y, s } = footprint(type, i);
  const b = { id: nextBldgId++, type, x, y, size: s, center: i, owner: f.id };
  buildings.push(b); bById.set(b.id, b);
  forFootprint(x, y, s, c => { bldgAt[c] = b.id; });
  railsDirty = true; dirty = true;
  return b;
}

function placeBuilding(f, i, type, cost) {
  if (f.gold < cost || canPlace(f, i, type)) return false;
  f.gold -= cost; addBuilding(f, i, type); dirtyUI = true;
  if (f.isPlayer) addLog(`Built a ${BUILD_NAME[type]}`, 'good');
  return true;
}

function removeBuilding(b) {
  forFootprint(b.x, b.y, b.size, c => { if (bldgAt[c] === b.id) bldgAt[c] = 0; });
  buildings = buildings.filter(x => x !== b); bById.delete(b.id); b.dead = true;
  railsDirty = true; dirty = true;
}

function recruit(f) {
  if (f.gold < COST.recruit || f.troops >= f.cap) return false;
  f.gold -= COST.recruit; f.troops = Math.min(f.cap, f.troops + RECRUIT_TROOPS); dirtyUI = true;
  return true;
}

function launchNuke(f, target) {
  const silos = S.silos[f.id];
  if (!silos.length || f.gold < COST.nuke || owner[target] === OBSTACLE || tick < f.nukeReady) return false;
  f.nukeReady = tick + NUKE_RELOAD;
  let from = silos[0].center;
  for (const s of silos) if (dist2(s.center, target) < dist2(from, target)) from = s.center;
  f.gold -= COST.nuke;
  missiles.push({ from, to: target, owner: f.id, t: 0, total: NUKE_FLIGHT });
  addLog(`<b>${f.name}</b> launched a nuke!`, f.isPlayer ? 'good' : 'bad');
  dirtyUI = true;
  return true;
}

function updateMissiles() {
  for (const m of missiles) { m.t++; if (m.t >= m.total) detonate(m); }
  missiles = missiles.filter(m => m.t < m.total);
}

function detonate(m) {
  const tx = cx(m.to), ty = cy(m.to), r2 = NUKE_RADIUS * NUKE_RADIUS;
  const affected = new Map(); // faction -> cells lost
  const hit = new Set();      // buildings with any cell in the blast
  for (let y = ty - NUKE_RADIUS; y <= ty + NUKE_RADIUS; y++) {
    for (let x = tx - NUKE_RADIUS; x <= tx + NUKE_RADIUS; x++) {
      if (x < 0 || y < 0 || x >= W || y >= H) continue;
      if ((x - tx) ** 2 + (y - ty) ** 2 > r2) continue;
      const i = y * W + x, o = owner[i];
      if (o === OBSTACLE) continue;
      if (o >= 0) { affected.set(o, (affected.get(o) || 0) + 1); factions[o].cells--; }
      if (bldgAt[i]) hit.add(bAt(i));
      if (o !== FALLOUT) falloutList.push(i);
      owner[i] = FALLOUT; fallout[i] = FALLOUT_TICKS;
    }
  }
  hit.forEach(removeBuilding);
  const shooter = factions[m.owner];
  for (const [o, lost] of affected) {
    const f = factions[o];
    const before = f.cells + lost;
    const loss = Math.min(f.troops, f.troops * (lost / before) * 1.5);
    f.troops -= loss;
    if (o !== m.owner) {
      f.threat.set(m.owner, { force: loss + lost * 50, tick });
      if (shooter.allies.has(o)) breakAlliance(shooter, f);
      if (f.isPlayer || shooter.isPlayer)
        addLog(`<b>${shooter.name}</b>'s nuke hit <b>${f.name}</b>: ${lost} tiles, ${fmt(loss)} troops`, f.isPlayer ? 'bad' : 'good');
    }
    if (f.cells <= 0) eliminate(f);
  }
  effects.push({ kind: 'blast', x: tx + 0.5, y: ty + 0.5, t: 0, total: 25 });
  dirty = true; dirtyUI = true;
}

function updateFallout() {
  if (!falloutList.length) return;
  let changed = false;
  falloutList = falloutList.filter(i => {
    if (--fallout[i] > 0) return true;
    owner[i] = NEUTRAL; changed = true; return false;
  });
  if (changed) dirty = true;
}

// ===================================================== 6. Rails & trains
// A factory lays track to up to RAIL_MAX_LINKS of the nearest buildings of
// its owner or allies, routed through land they hold and around other
// buildings. Each rail sends a train every TRAIN_INTERVAL ticks and the
// delivery pays the factory's owner. A rail breaks as soon as any cell under
// it is lost, a building is put on it, or either end changes hands.
let seen, parent, depth, stamp = 0;   // BFS scratch, sized with the map
let onTrack;                          // per cell: number of rails crossing it

function railLand(f, c) { const o = owner[c]; return o === f.id || (o >= 0 && f.allies.has(o)); }
function linksOf(b) { let n = 0; for (const r of rails) if (r.a === b || r.b === b) n++; return n; }
function linked(a, b) { return rails.some(r => (r.a === a && r.b === b) || (r.a === b && r.b === a)); }
function trainReward(r) { return Math.round((TRAIN_BASE + TRAIN_PER_CELL * r.len) * (r.b.type === B_CITY ? CITY_TRADE : 1)); }

function buildRails(fac) {
  const f = factions[fac.owner];
  let free = RAIL_MAX_LINKS - linksOf(fac);
  if (free <= 0) return;
  stamp++;
  const q = [];
  forFootprint(fac.x, fac.y, fac.size, c => { seen[c] = stamp; parent[c] = -1; depth[c] = 0; q.push(c); });
  const found = new Set();
  const open = c => railLand(f, c) && (!bldgAt[c] || bldgAt[c] === fac.id);
  for (let h = 0; h < q.length && free > 0; h++) {
    const c = q[h], x = c % W, y = (c / W) | 0;
    if (depth[c] >= RAIL_RANGE) continue;
    for (const [dx, dy] of NB8) {
      const nx = x + dx, ny = y + dy;
      if (nx < 0 || ny < 0 || nx >= W || ny >= H) continue;
      const n = ny * W + nx;
      if (seen[n] === stamp || !railLand(f, n)) continue;
      if (dx && dy && (!open(y * W + nx) || !open(ny * W + x))) continue; // no squeezing past corners
      seen[n] = stamp; parent[n] = c; depth[n] = depth[c] + 1;
      const id = bldgAt[n];
      if (!id) { q.push(n); continue; }
      const b = bById.get(id);              // track never runs through other buildings
      if (found.has(b) || free <= 0) continue;
      found.add(b);
      if ((b.owner === f.id || f.allies.has(b.owner)) && !linked(fac, b) &&
          (b.type !== B_FACTORY || linksOf(b) < RAIL_MAX_LINKS)) { layRail(fac, b, n); free--; }
    }
  }
}

// Visit the cells under the straight run between the centers of cells a and b;
// stops early when fn returns false. Laying and checking track must sample alike.
function forSegment(a, b, fn) {
  const ax = cx(a) + 0.5, ay = cy(a) + 0.5, bx = cx(b) + 0.5, by = cy(b) + 0.5;
  const steps = Math.ceil(Math.hypot(bx - ax, by - ay) * 4);
  for (let k = 0; k <= steps; k++)
    if (fn(Math.floor(ay + (by - ay) * k / steps) * W + Math.floor(ax + (bx - ax) * k / steps)) === false) return false;
  return true;
}

function layRail(fac, b, entry) {
  const f = factions[fac.owner];
  const path = [b.center];
  for (let c = entry; c !== -1; c = parent[c]) path.push(c);
  path.push(fac.center);
  path.reverse();
  const ok = c => railLand(f, c) && (!bldgAt[c] || bldgAt[c] === fac.id || bldgAt[c] === b.id);
  // Straighten the BFS path into the longest runs the land allows
  const keep = [path[0]];
  for (let i = 0; i < path.length - 1;) {
    let j = path.length - 1;
    while (j > i + 1 && !forSegment(path[i], path[j], ok)) j--;
    keep.push(path[j]); i = j;
  }
  const pts = keep.map(c => ({ x: cx(c) + 0.5, y: cy(c) + 0.5 }));
  const cum = [0], cells = new Set();
  for (let k = 1; k < pts.length; k++) {
    cum.push(cum[k - 1] + Math.hypot(pts[k].x - pts[k - 1].x, pts[k].y - pts[k - 1].y));
    forSegment(keep[k - 1], keep[k], c => { cells.add(c); });
  }
  for (const c of cells) onTrack[c]++;
  rails.push({ a: fac, b, owner: f.id, pts, cum, len: cum[cum.length - 1], cells: [...cells], next: tick + 10 + rand(TRAIN_INTERVAL) });
}

function railValid(r) {
  if (r.a.dead || r.b.dead || r.a.owner !== r.owner) return false;
  const f = factions[r.owner];
  if (!f.alive || (r.b.owner !== r.owner && !f.allies.has(r.b.owner))) return false;
  for (const c of r.cells) {
    const id = bldgAt[c];
    if (!railLand(f, c) || (id && id !== r.a.id && id !== r.b.id)) return false;
  }
  return true;
}

// World position and heading at distance d along a rail
function railPoint(r, d) {
  d = Math.max(0, Math.min(r.len, d));
  let k = 1;
  while (k < r.cum.length - 1 && r.cum[k] < d) k++;
  const a = r.pts[k - 1], b = r.pts[k], t = (d - r.cum[k - 1]) / (r.cum[k] - r.cum[k - 1] || 1);
  return { x: a.x + (b.x - a.x) * t, y: a.y + (b.y - a.y) * t, ang: Math.atan2(b.y - a.y, b.x - a.x) };
}

function deliver(r) {
  const g = trainReward(r), f = factions[r.owner], to = factions[r.b.owner];
  f.gold += g;
  if (to !== f) to.gold += g * ALLY_SHARE;
  if (f.isPlayer || to.isPlayer)
    effects.push({ kind: 'gold', x: r.b.x + r.b.size / 2, y: r.b.y, text: '+' + fmt(f.isPlayer ? g : g * ALLY_SHARE), t: 0, total: 18 });
}

function updateRails() {
  for (const r of rails) if (!railValid(r)) { r.dead = true; railsDirty = true; for (const c of r.cells) onTrack[c]--; }
  if (railsDirty) { rails = rails.filter(r => !r.dead); trains = trains.filter(t => !t.rail.dead); }
  // Rebuild after any change, and every 3 s so growing land can open new routes
  if (railsDirty || tick % 30 === 0) {
    railsDirty = false;
    for (const b of buildings) if (b.type === B_FACTORY) buildRails(b);
  }
  for (const r of rails) if (tick >= r.next) { r.next = tick + TRAIN_INTERVAL; trains.push({ rail: r, d: 0 }); }
  for (const t of trains) { t.d += TRAIN_SPEED; if (t.d >= t.rail.len) deliver(t.rail); }
  trains = trains.filter(t => t.d < t.rail.len);
  // Expected income per tick, for the UI
  for (const f of factions) f.goldGen = 0;
  for (const r of rails) {
    const g = trainReward(r) / TRAIN_INTERVAL;
    factions[r.owner].goldGen += g;
    if (r.b.owner !== r.owner) factions[r.b.owner].goldGen += g * ALLY_SHARE;
  }
}

// ========================================================= 7. Diplomacy
function formAlliance(a, b) {
  a.allies.add(b.id); b.allies.add(a.id);
  a.threat.delete(b.id); b.threat.delete(a.id);
  for (const x of attacks) {
    if ((x.attacker === a.id && x.target === b.id) || (x.attacker === b.id && x.target === a.id)) {
      const att = factions[x.attacker]; att.troops = Math.min(att.cap, att.troops + x.force); x.done = true;
    }
  }
  attacks = attacks.filter(x => !x.done);
  proposals = proposals.filter(p => p.from !== a.id && p.from !== b.id);
  addLog(`<b>${a.name}</b> and <b>${b.name}</b> formed an alliance`, (a.isPlayer || b.isPlayer) ? 'good' : '');
  railsDirty = true; dirty = true; dirtyUI = true;
}

function breakAlliance(breaker, victim) {
  if (!breaker.allies.has(victim.id)) return;
  breaker.allies.delete(victim.id); victim.allies.delete(breaker.id);
  breaker.traitorUntil = tick + TRAITOR_TICKS;
  pairCooldown.set(pairKey(breaker.id, victim.id), tick);
  victim.threat.set(breaker.id, { force: 1, tick });
  addLog(`<b>${breaker.name}</b> betrayed <b>${victim.name}</b> and is now a traitor`, victim.isPlayer ? 'bad' : '');
  railsDirty = true; dirty = true; dirtyUI = true;
}

function canPropose(from, to) {
  if (!from.alive || !to.alive || from === to || from.allies.has(to.id)) return false;
  if (isTraitor(from)) return false;
  const last = pairCooldown.get(pairKey(from.id, to.id));
  return last === undefined || tick - last >= PAIR_COOLDOWN;
}

function propose(from, to) {
  if (!canPropose(from, to)) return;
  pairCooldown.set(pairKey(from.id, to.id), tick);
  if (to.isPlayer) {
    if (!proposals.some(p => p.from === from.id)) {
      proposals.push({ from: from.id, expires: tick + PROPOSAL_TTL });
      addLog(`<b>${from.name}</b> proposes an alliance`, 'good');
    }
  } else if (aiAccepts(to, from)) {
    formAlliance(from, to);
  } else if (from.isPlayer) {
    addLog(`<b>${to.name}</b> rejected your alliance proposal`, 'bad');
  }
  dirtyUI = true;
}

function aiAccepts(ai, from) {
  if (isTraitor(from)) return false;
  let p = ai.personality.allyChance;
  if (ai.threat.size) p += 0.3;                       // under attack: wants friends
  if (from.troops > ai.troops * 2.5) p -= 0.3;        // too dominant to trust
  if (from.cells / claimable > 0.4) p -= 0.4;         // about to win
  const strongest = factions.reduce((m, f) => (f.alive && f.cells > m.cells ? f : m), factions[0]);
  if (strongest !== from && strongest !== ai && S.adj[ai.id][strongest.id] > 0) p += 0.2; // common big neighbor
  return Math.random() < p;
}

function expireProposals() {
  const before = proposals.length;
  proposals = proposals.filter(p => p.expires > tick && factions[p.from].alive && !player.allies.has(p.from));
  if (proposals.length !== before) dirtyUI = true;
}

// ================================================================= 8. AI
function adjacentEnemies(f) {
  return factions.filter(g => g.alive && g !== f && !f.allies.has(g.id) && S.adj[f.id][g.id] > 0);
}

function ownCells(f) {
  const out = [];
  for (let i = 0; i < N; i++) if (owner[i] === f.id) out.push(i);
  return out;
}

function aiThink(f) {
  const P = f.personality;
  const ratio = f.cap > 0 ? f.troops / f.cap : 0;
  for (const [id, t] of f.threat) if (tick - t.tick > THREAT_MEMORY) f.threat.delete(id);
  const enemies = adjacentEnemies(f);

  aiBuild(f, P, ratio, enemies);
  aiDiplomacy(f, P, enemies);

  // Counter-attack whoever hit us hardest recently
  let threatId = -1, best = 0;
  for (const [id, t] of f.threat) if (t.force > best && enemies.some(e => e.id === id)) { best = t.force; threatId = id; }
  if (threatId >= 0 && ratio > 0.3 && Math.random() < 0.5) {
    f.state = 'Counter'; f.commit = 0.4;
    if (launchAttack(f, threatId, null)) return;
  }
  // State A: expand into neutral land with 20%
  const neutral = S.neutralAdj[f.id];
  if (neutral.length) {
    f.state = 'Expand'; f.commit = 0.2;
    launchAttack(f, NEUTRAL, neutral[rand(neutral.length)]);
    return;
  }
  // State B: attack a neighbor when the pool is nearly full
  if (ratio > P.attackAt && enemies.length) {
    f.state = 'Attack'; f.commit = P.commit;
    launchAttack(f, pickTarget(f, enemies).id, null);
    return;
  }
  // State C: accumulate
  f.state = 'Build';
}

// Weighted random target: longer border and weaker enemies are preferred,
// traitors and recent aggressors even more so.
function pickTarget(f, enemies) {
  const weights = enemies.map(e =>
    (S.adj[f.id][e.id] / (e.troops + 100)) * (isTraitor(e) ? 3 : 1) * (f.threat.has(e.id) ? 2 : 1));
  let total = weights.reduce((a, b) => a + b, 0), r = Math.random() * total;
  for (let i = 0; i < enemies.length; i++) { r -= weights[i]; if (r <= 0) return enemies[i]; }
  return enemies[enemies.length - 1];
}

function crossesTrack(i, type) {
  const { x, y, s } = footprint(type, i);
  let hit = false;
  forFootprint(x, y, s, c => { if (onTrack[c]) hit = true; });
  return hit;
}

// Try a few random cells from pool and build on the best-scoring valid one
// that leaves existing rails intact.
// interior: keep a ring of own land around the footprint, away from the front.
function aiPlace(f, pool, type, cost, score, interior) {
  let best = -1, bestScore = -Infinity;
  const r = (BUILD_SIZE[type] >> 1) + 1;
  for (let k = 0; k < 60 && pool.length; k++) {
    const i = pool[rand(pool.length)];
    if (canPlace(f, i, type) || crossesTrack(i, type) || (interior && !around(i, r, c => owner[c] === f.id, true))) continue;
    const sc = score(i) + Math.random();
    if (sc > bestScore) { bestScore = sc; best = i; }
  }
  return best >= 0 && placeBuilding(f, best, type, cost);
}

// Buildings at a useful rail distance from cell i
function railTargets(i, list) {
  return list.filter(b => { const d = bDist2(b, i); return d >= 25 && d <= (RAIL_RANGE * 0.7) ** 2; }).length;
}

function aiBuild(f, P, ratio, enemies) {
  const own = ownCells(f);
  const facs = S.factories[f.id];
  const mine = buildings.filter(b => b.owner === f.id);
  const wantFactory = f.gold >= COST.factory && facs.length < Math.min(8, 1 + Math.floor(f.cells / 400)) && (!facs.length || Math.random() < P.factoryChance);
  const wantCity = f.gold >= COST.city && f.cells >= 40 && (ratio > 0.7 || Math.random() < P.cityChance);
  const wantPost = f.gold >= COST.post && enemies.length && Math.random() < P.postChance;
  const built =
    (wantFactory && aiPlace(f, own, B_FACTORY, COST.factory, i => Math.min(RAIL_MAX_LINKS, railTargets(i, mine)) || -Infinity, true)) ||
    (wantCity && aiPlace(f, own, B_CITY, COST.city, i => railTargets(i, facs), true)) ||
    (wantPost && aiPost(f, own, enemies)) ||
    (f.gold >= COST.silo && f.cells >= 150 && !S.silos[f.id].length && aiPlace(f, own, B_SILO, COST.silo, () => 0, true));
  if (!built && S.silos[f.id].length && f.gold >= COST.nuke && Math.random() < 0.5) aiNuke(f, own);
  if (f.gold >= COST.recruit && ratio < 0.4 && f.threat.size) recruit(f);
}

// Shield the border with the strongest enemy, away from existing posts
function aiPost(f, own, enemies) {
  const target = enemies.reduce((m, e) => (e.troops > m.troops ? e : m), enemies[0]);
  const pool = own.filter(i => around(i, 4, c => owner[c] === target.id));
  return aiPlace(f, pool, B_POST, COST.post,
    i => S.posts[f.id].some(p => bDist2(p, i) <= POST_RADIUS * POST_RADIUS) ? -Infinity : 0, false);
}

function aiNuke(f, own) {
  const victims = factions.filter(g => g.alive && g !== f && !f.allies.has(g.id) && g.cells >= 60);
  if (!victims.length) return;
  const v = victims.reduce((m, g) => (f.threat.has(g.id) && !f.threat.has(m.id) ? g : m), victims[rand(victims.length)]);
  const vCells = ownCells(v);
  const assets = buildings.filter(b => b.owner === v.id && b.type !== B_POST).map(b => b.center);
  const pool = assets.length && Math.random() < 0.7 ? assets : vCells;
  const minD = (NUKE_RADIUS + 2) ** 2;
  for (let tries = 0; tries < 12; tries++) {
    const t = pool[rand(pool.length)];
    let safe = true;
    for (const c of own) if (dist2(c, t) < minD) { safe = false; break; }
    if (safe) { launchNuke(f, t); break; }
  }
}

function aiDiplomacy(f, P, enemies) {
  // Seek friends when a neighbor outguns us
  if (enemies.length && !isTraitor(f) && Math.random() < 0.15) {
    const strongest = enemies.reduce((m, e) => (e.troops > m.troops ? e : m), enemies[0]);
    if (strongest.troops > f.troops * 1.3) {
      const cand = factions.filter(g => g.alive && g !== f && g !== strongest && !f.allies.has(g.id) && !isTraitor(g) && canPropose(f, g));
      if (cand.length) propose(f, cand[rand(cand.length)]);
    }
  }
  // Betray when there is nobody else left to fight
  if (!enemies.length && f.allies.size && f.troops / f.cap > 0.9 && Math.random() < P.breakChance) {
    const allies = [...f.allies].map(id => factions[id]).filter(g => g.alive && S.adj[f.id][g.id] > 0);
    if (allies.length) breakAlliance(f, allies.reduce((m, g) => (g.troops < m.troops ? g : m), allies[0]));
  }
}

// ============================================ 9. Game loop & win conditions
function doTick() {
  tick++;
  scan();
  processAttacks();
  updateMissiles();
  updateFallout();
  updateRails();        // after combat so lost land cuts its rails this tick
  economy();            // after combat so returning troops are clamped to the (possibly smaller) cap
  expireProposals();
  effects.forEach(e => e.t++); effects = effects.filter(e => e.t < e.total);
  for (const f of factions)
    if (f.alive && !f.isPlayer && (tick + f.id * 3) % AI_INTERVAL === 0) aiThink(f);
  if (!ended) checkGameOver();
  dirtyUI = true;
}

function checkGameOver() {
  const alive = factions.filter(f => f.alive);
  for (const f of alive) if (f.cells / claimable >= WIN_SHARE) {
    endGame(f.isPlayer, `${f.name} control${f.isPlayer ? '' : 's'} ${Math.round(f.cells / claimable * 100)}% of the map.`);
    return;
  }
  if (!player.alive) { endGame(false, 'Your last tile has fallen.'); return; }
  const enemies = alive.filter(f => f !== player && !player.allies.has(f.id));
  if (!enemies.length && alive.length === 1) { endGame(true, 'You are the last faction standing.'); return; }
  // Shared victory: every survivor allied with you, no neutral land left, held for a minute
  const neutralLeft = alive.some(f => S.neutralAdj[f.id].length > 0);
  allyHold = (!enemies.length && !neutralLeft) ? allyHold + 1 : 0;
  if (allyHold >= ALLY_WIN_TICKS) endGame(true, 'Every surviving faction is your ally.');
}

function endGame(win, text) {
  gameOver = true; ended = true;
  ui.overlayTitle.textContent = win ? 'Victory' : 'Defeat';
  ui.overlayText.textContent = text;
  ui.overlay.classList.remove('hidden');
  addLog(win ? 'Victory!' : 'Defeat.', win ? 'good' : 'bad');
}

function resetGame() {
  W = Math.max(MIN_W, Math.min(MAX_W, Math.round(H * innerWidth / Math.max(1, innerHeight))));
  tick = 0; gameOver = false; ended = false; paused = false; allyHold = 0;
  attacks = []; missiles = []; effects = []; proposals = []; logLines = [];
  rails = []; trains = []; railsDirty = true; nextBldgId = 1;
  pairCooldown.clear(); buildMode = null; hover = -1;
  generateMap();
  seen = new Int32Array(N); parent = new Int32Array(N); depth = new Int16Array(N); stamp = 0; onTrack = new Uint16Array(N);
  initFactions();
  player.commit = ui.commit.value / 100;
  scan(); economy();
  baseCanvas.width = W; baseCanvas.height = H; baseImg = bctx.createImageData(W, H);
  fitView();
  ui.overlay.classList.add('hidden');
  ui.pause.textContent = '❚❚';
  buildLeaderboard();
  addLog('A new world. Claim it.');
  setBuildMode(null);
  dirty = true; dirtyUI = true; dirtyLog = true;
}

// ======================================== 10. Camera, input, UI, rendering
const ui = {};
function $(id) { return document.getElementById(id); }

// ---------------------------------------------------------------- Camera
// screen = world * s + offset, where one world unit is one cell
const cam = { s: 1, ox: 0, oy: 0, fit: 1, moved: false };
let vw = 0, vh = 0, dpr = 1;

function resize() {
  dpr = window.devicePixelRatio || 1; vw = innerWidth; vh = innerHeight;
  ui.canvas.width = Math.round(vw * dpr); ui.canvas.height = Math.round(vh * dpr);
  if (cam.moved) { cam.fit = Math.min(vw / W, vh / H); clampView(); } else fitView();
}
// Fill the screen with the map; zooming out can still show all of it
function fitView() {
  cam.fit = Math.min(vw / W, vh / H);
  cam.s = Math.max(vw / W, vh / H);
  cam.ox = (vw - W * cam.s) / 2; cam.oy = (vh - H * cam.s) / 2; cam.moved = false;
}
function clampView() {
  cam.s = Math.max(cam.fit * 0.9, Math.min(cam.fit * 8, cam.s));
  const m = 160, mw = W * cam.s, mh = H * cam.s;
  cam.ox = mw + 2 * m <= vw ? (vw - mw) / 2 : Math.min(m, Math.max(vw - mw - m, cam.ox));
  cam.oy = mh + 2 * m <= vh ? (vh - mh) / 2 : Math.min(m, Math.max(vh - mh - m, cam.oy));
}
function zoomAt(px, py, factor) {
  const s = Math.max(cam.fit * 0.9, Math.min(cam.fit * 8, cam.s * factor)), k = s / cam.s;
  cam.ox = px - (px - cam.ox) * k; cam.oy = py - (py - cam.oy) * k; cam.s = s; cam.moved = true;
  clampView();
}
function panBy(dx, dy) { cam.ox += dx; cam.oy += dy; cam.moved = true; clampView(); }
function screenCell(px, py) {
  const x = Math.floor((px - cam.ox) / cam.s), y = Math.floor((py - cam.oy) / cam.s);
  if (x < 0 || y < 0 || x >= W || y >= H) return -1;
  return y * W + x;
}

// ------------------------------------------------------------ Hints & modes
let hintTimer = 0;
const DEFAULT_HINT = 'Click land touching yours to expand or attack · drag to pan · scroll to zoom';
const MODE_HINT = {
  factory: 'Place a Factory: it lays rails to up to 4 nearby buildings and sends gold-earning trains.',
  city: 'Place a City: +2000 troop cap, ×1.5 defense, and trains delivering here pay ×1.5.',
  post: `Place a Defense Post: ×2 defense on your land within ${POST_RADIUS} tiles.`,
  silo: 'Place a Missile Silo to unlock nukes.',
  nuke: `Pick a target: radius ${NUKE_RADIUS}. Right-click or Esc to cancel.`,
};

function setBuildMode(mode) {
  buildMode = mode;
  document.querySelectorAll('.tool[data-mode]').forEach(b => b.classList.toggle('active', b.dataset.mode === mode));
  ui.canvas.classList.toggle('build', !!mode);
  clearTimeout(hintTimer);
  ui.buildHint.classList.remove('warn');
  ui.buildHint.textContent = mode ? MODE_HINT[mode] : DEFAULT_HINT;
}
// A short-lived message in the hint bar; it falls back to the current mode's hint
function flash(text, warn) {
  ui.buildHint.textContent = text;
  ui.buildHint.classList.toggle('warn', !!warn);
  clearTimeout(hintTimer);
  hintTimer = setTimeout(() => setBuildMode(buildMode), 2500);
}

function onCanvasClick(ev) {
  const i = screenCell(ev.clientX, ev.clientY);
  if (i < 0 || !player.alive || gameOver) return;
  if (buildMode === 'nuke') {
    if (!S.silos[player.id].length) return flash('You need a Missile Silo first.', true);
    if (player.gold < COST.nuke) return flash('Not enough gold for a nuke.', true);
    if (tick < player.nukeReady) return flash(`Silo reloading: ${Math.ceil((player.nukeReady - tick) / 10)} s.`, true);
    if (owner[i] === OBSTACLE) return flash('Cannot target mountains.', true);
    launchNuke(player, i); setBuildMode(null); return;
  }
  if (buildMode) {
    const type = MODE_TYPE[buildMode], cost = COST[buildMode];
    if (player.gold < cost) return flash('Not enough gold.', true);
    const why = canPlace(player, i, type);
    if (why) return flash(why, true);
    placeBuilding(player, i, type, cost);
    if (!ev.shiftKey) setBuildMode(null);   // shift-click keeps building
    return;
  }
  const o = owner[i];
  if (o === player.id) return flash('That is already your land.');
  if (o === OBSTACLE) return flash('Mountains are impassable.', true);
  if (o === FALLOUT) return flash('Radioactive fallout. Wait for it to clear.', true);
  if (o === NEUTRAL) {
    if (!adjacentTo(i, player.id)) return flash('Expand from a tile that touches your territory.', true);
    if (launchAttack(player, NEUTRAL, i)) flash(`Expanding with ${Math.round(player.commit * 100)}% of your troops.`);
    return;
  }
  if (player.allies.has(o)) return flash(`${factions[o].name} is your ally. Break the alliance first.`, true);
  launchAttack(player, o, null);
}

const BUILD_INFO = {
  [B_CITY]: '+2000 troop cap · ×1.5 defense',
  [B_POST]: `×2 defense within ${POST_RADIUS} tiles`,
  [B_SILO]: 'Launches nukes',
};
function tooltipFor(i) {
  const o = owner[i];
  if (o === OBSTACLE) return 'Mountains (impassable)';
  if (o === FALLOUT) return `Radioactive fallout\nclears in ${Math.ceil(fallout[i] / 10)} s`;
  if (o === NEUTRAL) return `Neutral land\n${NEUTRAL_COST} troops to claim`;
  const f = factions[o];
  let s = f.name + (f.isPlayer ? ' (you)' : player.allies.has(o) ? ' (ally)' : '') + (isTraitor(f) ? ' — traitor' : '');
  if (!f.isPlayer) { const d = cellDefense(i, f); s += `\nAttack cost: ${fmt(attackCost(d))} (defender loses ${fmt(d)})`; }
  if (f.personality) s += `\n${f.personality.label}, ${f.state}`;
  if (shielded(i, f)) s += '\nShielded by a Defense Post';
  const b = bAt(i);
  if (b) {
    const bo = factions[b.owner];
    s += `\n\n${BUILD_NAME[b.type]}${bo !== f ? ` (${bo.name})` : ''}`;
    if (b.type === B_FACTORY) {
      const own = rails.filter(r => r.a === b);
      const g = own.reduce((t, r) => t + trainReward(r), 0) / TRAIN_INTERVAL * 10;
      s += `\n${own.length} / ${RAIL_MAX_LINKS} rails · ${g.toFixed(1)} gold/s`;
    } else {
      s += '\n' + BUILD_INFO[b.type];
      const n = rails.filter(r => r.b === b).length;
      if (n) s += `\n${n} rail${n > 1 ? 's' : ''} delivering here`;
    }
  }
  return s;
}

// ---------------------------------------------------------- Panels
const TOOLS = [
  { mode: 'factory', type: B_FACTORY, label: 'Factory', key: '1', tip: 'Lays rails to nearby buildings; its trains earn gold' },
  { mode: 'city', type: B_CITY, label: 'City', key: '2', tip: '+2000 troop cap, ×1.5 defense, better train income' },
  { mode: 'post', type: B_POST, label: 'Defense', key: '3', tip: `×2 defense on your land within ${POST_RADIUS} tiles` },
  { mode: 'silo', type: B_SILO, label: 'Silo', key: '4', tip: 'Unlocks nukes' },
  { mode: 'nuke', type: 'nuke', label: 'Nuke', key: '5', tip: `Radius ${NUKE_RADIUS} blast, leaves fallout` },
  { id: 'recruit', type: 'recruit', label: 'Recruit', key: '6', tip: `Turn ${COST.recruit} gold into ${RECRUIT_TROOPS} troops` },
];

function buildTools() {
  for (const t of TOOLS) {
    const btn = document.createElement('button');
    btn.className = 'tool';
    if (t.mode) btn.dataset.mode = t.mode; else btn.id = t.id;
    btn.title = `${t.tip} (${t.key})`;
    const cost = t.mode ? COST[t.mode] : `${COST.recruit}`;
    btn.innerHTML = `<canvas width="${40 * dpr}" height="${40 * dpr}"></canvas><span class="name">${t.label}</span><span class="cost">${cost}</span><kbd>${t.key}</kbd>`;
    const g = btn.querySelector('canvas').getContext('2d');
    g.scale(dpr, dpr);
    drawIcon(g, t.type, 1, 1, 38, typeof t.type === 'number' ? '#4f8ef7' : '#475569');
    btn.addEventListener('click', () => t.mode ? setBuildMode(buildMode === t.mode ? null : t.mode) : doRecruit());
    ui.tools.appendChild(btn);
  }
  ui.recruit = $('recruit');
}

function doRecruit() { if (recruit(player)) flash(`Recruited ${RECRUIT_TROOPS} troops.`); }

function buildLeaderboard() {
  ui.leaderboard.innerHTML = '';
  for (const f of factions) {
    const row = document.createElement('div');
    row.className = 'frow' + (f.isPlayer ? ' me' : '');
    row.innerHTML = `<span class="sw" style="background:${f.color}"></span>
      <div><div class="fname"></div><div class="fsub"></div><div class="share"><div style="background:${f.color}"></div></div></div>
      <div class="fnum"></div><div class="fa"></div>`;
    if (!f.isPlayer) {
      const btn = document.createElement('button');
      btn.addEventListener('click', () => {
        if (player.allies.has(f.id)) {
          if (confirm(`Break your alliance with ${f.name}? You will be marked a traitor for 60 s.`)) breakAlliance(player, f);
        } else if (canPropose(player, f)) propose(player, f);
        dirtyUI = true;
      });
      row.querySelector('.fa').appendChild(btn);
      f.btn = btn;
    } else f.btn = null;
    f.row = row; ui.leaderboard.appendChild(row);
  }
}

function updateUI() {
  const p = player;
  ui.troops.textContent = fmt(p.troops); ui.cap.textContent = fmt(p.cap);
  ui.troopBar.style.width = (p.cap ? Math.min(100, p.troops / p.cap * 100) : 0) + '%';
  ui.gen.textContent = '+' + fmt(p.troopGen * 10) + '/s';
  ui.gold.textContent = fmt(p.gold);
  ui.goldGen.textContent = '+' + (p.goldGen * 10).toFixed(1) + '/s';
  const myRails = rails.filter(r => r.owner === p.id).length, myTrains = trains.filter(t => t.rail.owner === p.id).length;
  ui.railInfo.textContent = S.factories[p.id].length
    ? `${myRails} rail${myRails === 1 ? '' : 's'} · ${myTrains} train${myTrains === 1 ? '' : 's'} running`
    : 'Build a Factory to earn gold';
  ui.cells.textContent = (p.cells / claimable * 100).toFixed(1) + '%';
  ui.cellCount.textContent = `${fmt(p.cells)} tiles · win at ${WIN_SHARE * 100}%`;

  const threats = [...p.threat.entries()].filter(([, t]) => tick - t.tick <= THREAT_MEMORY).map(([id]) => factions[id].name);
  let status = 'Peaceful', tone = '';
  if (!p.alive) { status = 'Eliminated'; tone = 'bad'; }
  else if (isTraitor(p)) { status = `Traitor (${Math.ceil((p.traitorUntil - tick) / 10)} s)`; tone = 'warn'; }
  else if (threats.length) { status = 'Under attack: ' + threats.join(', '); tone = 'bad'; }
  else if (attacks.some(a => a.attacker === p.id && a.target >= 0)) { status = 'Attacking'; tone = 'info'; }
  else if (allyHold > 0) { status = `Allied victory in ${Math.ceil((ALLY_WIN_TICKS - allyHold) / 10)} s`; tone = 'info'; }
  else if (attacks.some(a => a.attacker === p.id)) { status = 'Expanding'; tone = 'info'; }
  ui.status.textContent = status;
  ui.statusPill.dataset.tone = tone;
  ui.time.textContent = clock(tick);

  // tools
  document.querySelectorAll('.tool[data-mode]').forEach(b => {
    const m = b.dataset.mode;
    b.disabled = !p.alive || p.gold < COST[m] || (m === 'nuke' && (!S.silos[p.id].length || tick < p.nukeReady));
  });
  ui.recruit.disabled = !p.alive || p.gold < COST.recruit || p.troops >= p.cap;

  // factions
  const sorted = [...factions].sort((a, b) => b.cells - a.cells);
  for (const f of sorted) {
    const r = f.row;
    r.classList.toggle('dead', !f.alive);
    let tag = '';
    if (!f.alive) tag = '<span class="tag dead">out</span>';
    else if (!f.isPlayer && player.allies.has(f.id)) tag = '<span class="tag ally">ally</span>';
    if (f.alive && isTraitor(f)) tag += '<span class="tag traitor">traitor</span>';
    r.querySelector('.fname').innerHTML = f.name + tag;
    r.querySelector('.fsub').textContent = (f.personality ? `${f.personality.label} · ${f.alive ? f.state : '—'} · ` : '') + `${fmt(f.gold)} gold`;
    r.querySelector('.share > div').style.width = Math.min(100, f.cells / claimable / WIN_SHARE * 100) + '%';
    r.querySelector('.fnum').innerHTML = `${(f.cells / claimable * 100).toFixed(1)}%<span class="muted">${fmt(f.troops)} troops</span>`;
    if (f.btn) {
      const allied = player.allies.has(f.id);
      f.btn.textContent = allied ? 'Break' : 'Ally';
      f.btn.className = allied ? 'secondary' : '';
      f.btn.disabled = !f.alive || !player.alive || (!allied && !canPropose(player, f));
      f.btn.title = allied ? 'Break alliance (you become a traitor)' : isTraitor(player) ? 'Nobody allies with a traitor' : 'Propose an alliance';
    }
    ui.leaderboard.appendChild(r);
  }

  // diplomacy
  if (proposals.length !== ui.proposals.childElementCount || proposals.some((p, i) => ui.proposals.children[i].dataset.from != p.from)) {
    ui.proposals.innerHTML = '';
    for (const pr of proposals) {
      const f = factions[pr.from];
      const div = document.createElement('div');
      div.className = 'toast glass'; div.dataset.from = pr.from;
      div.innerHTML = `<span class="sw" style="background:${f.color}"></span><span><b>${f.name}</b> offers an alliance</span>`;
      const yes = document.createElement('button'); yes.textContent = 'Accept';
      const no = document.createElement('button'); no.textContent = 'Decline'; no.className = 'secondary';
      yes.onclick = () => { formAlliance(player, f); };
      no.onclick = () => { proposals = proposals.filter(x => x !== pr); dirtyUI = true; };
      div.append(yes, no); ui.proposals.appendChild(div);
    }
  }
  dirtyUI = false;
}

function updateLog() {
  const lines = logLines.slice(-6);
  ui.log.innerHTML = lines.map((l, k) =>
    `<li class="${l.cls}" style="opacity:${(0.45 + 0.55 * (k + 1) / lines.length).toFixed(2)}"><span class="t">${clock(l.t)}</span>${l.text}</li>`).join('');
  dirtyLog = false;
}

// ---------------------------------------------------------------- Icons
// Glyphs are drawn in a unit square; drawIcon scales one onto a footprint
// inside a dark badge ringed with the owner's color. The dock uses the same art.
function dot(g, x, y, r) { g.beginPath(); g.arc(x, y, r, 0, Math.PI * 2); g.fill(); }
const GLYPHS = {
  [B_CITY](g) {
    g.fillStyle = '#e2e8f0';
    g.fillRect(0.2, 0.46, 0.17, 0.32); g.fillRect(0.41, 0.24, 0.19, 0.54); g.fillRect(0.64, 0.38, 0.16, 0.4);
    g.fillStyle = '#facc15';
    for (const [x, y] of [[0.45, 0.31], [0.52, 0.31], [0.45, 0.42], [0.52, 0.42], [0.45, 0.53], [0.52, 0.53],
                          [0.24, 0.53], [0.3, 0.53], [0.68, 0.46], [0.74, 0.46], [0.68, 0.57], [0.74, 0.57]])
      g.fillRect(x, y, 0.04, 0.05);
  },
  [B_POST](g) {
    g.fillStyle = '#60a5fa';
    g.beginPath(); g.moveTo(0.5, 0.17); g.lineTo(0.78, 0.27); g.lineTo(0.76, 0.5);
    g.quadraticCurveTo(0.73, 0.71, 0.5, 0.84); g.quadraticCurveTo(0.27, 0.71, 0.24, 0.5); g.lineTo(0.22, 0.27); g.closePath(); g.fill();
    g.fillStyle = '#dbeafe';
    g.beginPath(); g.moveTo(0.5, 0.26); g.lineTo(0.5, 0.74); g.quadraticCurveTo(0.34, 0.65, 0.32, 0.5); g.lineTo(0.31, 0.33); g.closePath(); g.fill();
  },
  [B_SILO](g) {
    g.fillStyle = '#ef4444';
    g.beginPath(); g.moveTo(0.4, 0.52); g.lineTo(0.27, 0.72); g.lineTo(0.4, 0.68); g.closePath(); g.fill();
    g.beginPath(); g.moveTo(0.6, 0.52); g.lineTo(0.73, 0.72); g.lineTo(0.6, 0.68); g.closePath(); g.fill();
    g.fillStyle = '#f8fafc';
    g.beginPath(); g.moveTo(0.5, 0.14); g.quadraticCurveTo(0.61, 0.26, 0.6, 0.4); g.lineTo(0.6, 0.7); g.lineTo(0.4, 0.7);
    g.lineTo(0.4, 0.4); g.quadraticCurveTo(0.39, 0.26, 0.5, 0.14); g.fill();
    g.fillStyle = '#ef4444';
    g.beginPath(); g.moveTo(0.5, 0.14); g.quadraticCurveTo(0.58, 0.22, 0.595, 0.3); g.lineTo(0.405, 0.3); g.quadraticCurveTo(0.42, 0.22, 0.5, 0.14); g.fill();
    g.fillStyle = '#f59e0b';
    g.beginPath(); g.moveTo(0.43, 0.72); g.lineTo(0.5, 0.86); g.lineTo(0.57, 0.72); g.closePath(); g.fill();
  },
  [B_FACTORY](g) {
    g.fillStyle = 'rgba(226,232,240,0.85)';
    dot(g, 0.71, 0.15, 0.05); dot(g, 0.8, 0.1, 0.035);
    g.fillStyle = '#fbbf24';
    g.beginPath(); g.moveTo(0.18, 0.8); g.lineTo(0.18, 0.5); g.lineTo(0.34, 0.4); g.lineTo(0.34, 0.5); g.lineTo(0.5, 0.4); g.lineTo(0.5, 0.5);
    g.lineTo(0.64, 0.4); g.lineTo(0.64, 0.22); g.lineTo(0.77, 0.22); g.lineTo(0.77, 0.8); g.closePath(); g.fill();
    g.fillStyle = '#1e293b';
    for (const x of [0.23, 0.37, 0.51]) g.fillRect(x, 0.6, 0.08, 0.09);
  },
  nuke(g) {
    g.fillStyle = '#facc15'; dot(g, 0.5, 0.5, 0.34);
    g.fillStyle = '#111827'; dot(g, 0.5, 0.5, 0.06);
    for (let k = 0; k < 3; k++) {
      const a = -Math.PI / 2 + k * Math.PI * 2 / 3;
      g.beginPath(); g.arc(0.5, 0.5, 0.29, a - 0.52, a + 0.52); g.arc(0.5, 0.5, 0.1, a + 0.52, a - 0.52, true); g.closePath(); g.fill();
    }
  },
  recruit(g) {
    g.fillStyle = '#4ade80';
    dot(g, 0.42, 0.36, 0.12);
    g.beginPath(); g.moveTo(0.2, 0.8); g.quadraticCurveTo(0.2, 0.54, 0.42, 0.54); g.quadraticCurveTo(0.64, 0.54, 0.64, 0.8); g.closePath(); g.fill();
    g.fillRect(0.66, 0.31, 0.18, 0.06); g.fillRect(0.72, 0.25, 0.06, 0.18);
  },
};

function drawIcon(g, type, x, y, size, ring) {
  g.save(); g.translate(x, y); g.scale(size, size);
  g.fillStyle = 'rgba(17,21,30,0.92)'; g.strokeStyle = ring; g.lineWidth = 0.08;
  g.beginPath(); g.roundRect(0.06, 0.06, 0.88, 0.88, 0.2); g.fill(); g.stroke();
  GLYPHS[type](g);
  g.restore();
}

// ---------------------------------------------------------------- Render
let ctx, baseCanvas, bctx, baseImg, protMask, zoneEdges = [];
const FALLOUT_RGB = hexRGB('#7c3aed');

// Static layer at one pixel per cell: terrain, territory, borders and the
// hatched defense-post zones. Redrawn only when the map changes.
function drawBase() {
  protMask = new Uint8Array(N);       // faction id + 1 on cells a defense post shields
  for (const b of buildings) {
    if (b.type !== B_POST) continue;
    around(b.center, POST_RADIUS + 1, c => {
      if (owner[c] === b.owner && bDist2(b, c) <= POST_RADIUS * POST_RADIUS) protMask[c] = b.owner + 1;
      return false;
    });
  }
  const d = baseImg.data;
  for (let i = 0; i < N; i++) {
    const o = owner[i], x = i % W, y = (i / W) | 0;
    let r = terrain[i * 3], g = terrain[i * 3 + 1], b = terrain[i * 3 + 2];
    if (o >= 0) {
      const c = factions[o].rgb;
      const edge = (x > 0 && owner[i - 1] !== o) || (x < W - 1 && owner[i + 1] !== o) ||
                   (y > 0 && owner[i - W] !== o) || (y < H - 1 && owner[i + W] !== o);
      if (edge) { r = c[0] * 0.72; g = c[1] * 0.72; b = c[2] * 0.72; }
      else {
        r += (c[0] - r) * 0.55; g += (c[1] - g) * 0.55; b += (c[2] - b) * 0.55;
        if (protMask[i]) { const k = ((x - y) & 3) === 0 ? 0.34 : 0.14; r += (255 - r) * k; g += (255 - g) * k; b += (255 - b) * k; }
      }
    } else if (o === FALLOUT) {
      const k = ((x + y) & 1) ? 0.75 : 0.6;
      r += (FALLOUT_RGB[0] - r) * k; g += (FALLOUT_RGB[1] - g) * k; b += (FALLOUT_RGB[2] - b) * k;
    }
    const p = i * 4; d[p] = r; d[p + 1] = g; d[p + 2] = b; d[p + 3] = 255;
  }
  bctx.putImageData(baseImg, 0, 0);
  // Outline each zone where the shield ends
  zoneEdges = [];
  for (let i = 0; i < N; i++) {
    const m = protMask[i]; if (!m) continue;
    const x = i % W, y = (i / W) | 0;
    if (x === 0 || protMask[i - 1] !== m) zoneEdges.push(x, y, x, y + 1);
    if (x === W - 1 || protMask[i + 1] !== m) zoneEdges.push(x + 1, y, x + 1, y + 1);
    if (y === 0 || protMask[i - W] !== m) zoneEdges.push(x, y, x + 1, y);
    if (y === H - 1 || protMask[i + W] !== m) zoneEdges.push(x, y + 1, x + 1, y + 1);
  }
  dirty = false;
}

function drawRails(g, px) {
  if (!rails.length) return;
  g.beginPath();
  for (const r of rails) { g.moveTo(r.pts[0].x, r.pts[0].y); for (let k = 1; k < r.pts.length; k++) g.lineTo(r.pts[k].x, r.pts[k].y); }
  g.lineJoin = 'round'; g.lineCap = 'round';
  g.strokeStyle = 'rgba(32,26,20,0.9)'; g.lineWidth = Math.max(0.38, 3.5 * px); g.stroke();
  g.lineCap = 'butt'; g.strokeStyle = '#efe7d4'; g.lineWidth = Math.max(0.16, 1.5 * px);
  g.setLineDash([0.5, 0.45]); g.stroke(); g.setLineDash([]);
}

// Locomotive in the owner's color pulling two gold wagons
function drawTrains(g, fr) {
  g.lineWidth = 0.08; g.strokeStyle = 'rgba(12,14,20,0.9)';
  for (const t of trains) {
    const r = t.rail, head = t.d + fr * TRAIN_SPEED;
    for (let k = 2; k >= 0; k--) {
      const d = head - k * 0.85;
      if (d < 0) continue;
      const p = railPoint(r, d);
      g.save(); g.translate(p.x, p.y); g.rotate(p.ang);
      g.fillStyle = k ? '#f5c542' : factions[r.owner].color;
      g.beginPath(); g.roundRect(-0.38, -0.25, 0.76, 0.5, 0.12); g.fill(); g.stroke();
      g.restore();
    }
  }
}

// Ghost footprint while placing, plus the post's range or the likely rail links
function drawPreview(g, px) {
  if (hover < 0 || (drag && drag.moved)) return;
  const type = MODE_TYPE[buildMode];
  g.lineWidth = 1.5 * px;
  if (!type) {
    const x = cx(hover), y = cy(hover);
    g.strokeStyle = '#fff'; g.strokeRect(x, y, 1, 1);
    if (buildMode === 'nuke') {
      g.strokeStyle = 'rgba(255,60,60,0.9)'; g.setLineDash([4 * px, 3 * px]);
      g.beginPath(); g.arc(x + 0.5, y + 0.5, NUKE_RADIUS + 0.5, 0, Math.PI * 2); g.stroke(); g.setLineDash([]);
    }
    return;
  }
  const fp = footprint(type, hover), mx = fp.x + fp.s / 2, my = fp.y + fp.s / 2;
  const ok = !canPlace(player, hover, type) && player.gold >= COST[buildMode];
  g.fillStyle = ok ? 'rgba(74,222,128,0.35)' : 'rgba(248,113,113,0.4)'; g.fillRect(fp.x, fp.y, fp.s, fp.s);
  g.globalAlpha = 0.8; drawIcon(g, type, fp.x, fp.y, fp.s, player.color); g.globalAlpha = 1;
  g.setLineDash([4 * px, 3 * px]);
  if (type === B_POST) {
    g.strokeStyle = 'rgba(255,255,255,0.85)'; g.beginPath(); g.arc(mx, my, POST_RADIUS, 0, Math.PI * 2); g.stroke();
  } else {
    // A factory reaches out to any friendly building; anything else gets reached by factories
    const near = buildings
      .filter(b => (b.owner === player.id || player.allies.has(b.owner)) && (type === B_FACTORY || b.type === B_FACTORY))
      .map(b => ({ b, d: Math.hypot(b.x + b.size / 2 - mx, b.y + b.size / 2 - my) }))
      .filter(o => o.d <= RAIL_RANGE).sort((a, b) => a.d - b.d).slice(0, RAIL_MAX_LINKS);
    g.strokeStyle = 'rgba(252,211,77,0.9)'; g.beginPath();
    for (const { b } of near) { g.moveTo(mx, my); g.lineTo(b.x + b.size / 2, b.y + b.size / 2); }
    g.stroke();
  }
  g.setLineDash([]);
}

// Name and troops pill at each territory's centroid (screen space)
function drawLabels(g) {
  g.textAlign = 'center'; g.textBaseline = 'middle';
  for (const f of factions) {
    if (!f.alive || !f.cells) continue;
    const x = (S.sx[f.id] / f.cells + 0.5) * cam.s + cam.ox, y = (S.sy[f.id] / f.cells + 0.5) * cam.s + cam.oy;
    const fs = Math.max(11, Math.min(20, Math.sqrt(f.cells) * cam.s * 0.12));
    const l1 = (isTraitor(f) ? '⚠ ' : '') + f.name, l2 = fmt(f.troops) + (player.allies.has(f.id) ? ' · ally' : '');
    const f1 = `600 ${fs}px Inter, system-ui, sans-serif`, f2 = `500 ${(fs * 0.85).toFixed(1)}px Inter, system-ui, sans-serif`;
    g.font = f1; const w1 = g.measureText(l1).width;
    g.font = f2; const w = Math.max(w1, g.measureText(l2).width) + fs, h = fs * 2.3;
    g.fillStyle = 'rgba(15,19,27,0.72)'; g.beginPath(); g.roundRect(x - w / 2, y - h / 2, w, h, fs * 0.45); g.fill();
    g.strokeStyle = f.color; g.lineWidth = 1.5; g.stroke();
    g.font = f1; g.fillStyle = '#fff'; g.fillText(l1, x, y - fs * 0.5);
    g.font = f2; g.fillStyle = '#fde68a'; g.fillText(l2, x, y + fs * 0.55);
  }
}

function drawPopups(g, fr) {
  g.font = '700 13px Inter, system-ui, sans-serif'; g.textAlign = 'center'; g.lineWidth = 3; g.strokeStyle = 'rgba(15,19,27,0.85)';
  for (const e of effects) {
    if (e.kind !== 'gold') continue;
    const p = Math.min(1, (e.t + fr) / e.total), x = e.x * cam.s + cam.ox, y = e.y * cam.s + cam.oy - 4 - p * 22;
    g.globalAlpha = 1 - p * p; g.strokeText(e.text, x, y); g.fillStyle = '#fde047'; g.fillText(e.text, x, y);
  }
  g.globalAlpha = 1;
}

function render(ts) {
  if (dirty) drawBase();
  const g = ctx, px = 1 / cam.s, fr = Math.min(1, acc / TICK_MS);
  g.setTransform(dpr, 0, 0, dpr, 0, 0);
  g.fillStyle = '#101a24'; g.fillRect(0, 0, vw, vh);
  g.setTransform(dpr * cam.s, 0, 0, dpr * cam.s, dpr * cam.ox, dpr * cam.oy);   // world space: 1 unit = 1 cell
  g.strokeStyle = 'rgba(0,0,0,0.35)'; g.lineWidth = 6 * px; g.strokeRect(-3 * px, -3 * px, W + 6 * px, H + 6 * px);
  g.imageSmoothingEnabled = false;
  g.drawImage(baseCanvas, 0, 0);

  if (zoneEdges.length) {
    g.beginPath();
    for (let k = 0; k < zoneEdges.length; k += 4) { g.moveTo(zoneEdges[k], zoneEdges[k + 1]); g.lineTo(zoneEdges[k + 2], zoneEdges[k + 3]); }
    g.lineCap = 'square'; g.strokeStyle = 'rgba(255,255,255,0.8)'; g.lineWidth = 1.5 * px; g.stroke();
  }

  // Active fronts
  const pulse = 0.3 + 0.25 * Math.sin(ts / 120);
  for (const a of attacks) {
    const mine = a.attacker === player.id || (a.target === player.id);
    g.fillStyle = a.target === player.id ? `rgba(255,80,80,${pulse})` : `rgba(255,255,255,${mine ? pulse : pulse * 0.6})`;
    for (const c of a.frontier) g.fillRect(cx(c), cy(c), 1, 1);
  }

  drawRails(g, px);
  drawTrains(g, fr);    // under the badges, so trains pull into buildings like stations
  for (const b of buildings) drawIcon(g, b.type, b.x, b.y, b.size, factions[b.owner].color);

  // Missiles in flight
  for (const m of missiles) {
    const p = Math.min(1, (m.t + fr) / m.total);
    const x0 = cx(m.from) + 0.5, y0 = cy(m.from) + 0.5, x1 = cx(m.to) + 0.5, y1 = cy(m.to) + 0.5;
    const x = x0 + (x1 - x0) * p, y = y0 + (y1 - y0) * p - Math.sin(p * Math.PI) * 9;
    g.strokeStyle = 'rgba(255,255,255,0.35)'; g.lineWidth = px; g.setLineDash([3 * px, 3 * px]);
    g.beginPath(); g.moveTo(x0, y0); g.lineTo(x1, y1); g.stroke(); g.setLineDash([]);
    g.strokeStyle = 'rgba(255,60,60,0.9)'; g.lineWidth = 1.5 * px; g.beginPath(); g.arc(x1, y1, NUKE_RADIUS, 0, Math.PI * 2); g.stroke();
    g.fillStyle = '#fff'; dot(g, x, y, 0.5);
    g.fillStyle = factions[m.owner].color; dot(g, x, y, 0.28);
  }

  // Blast rings
  for (const e of effects) {
    if (e.kind !== 'blast') continue;
    const p = Math.min(1, (e.t + fr) / e.total);
    g.strokeStyle = `rgba(255,${Math.floor(200 - 150 * p)},0,${1 - p})`; g.lineWidth = 3 * px;
    g.beginPath(); g.arc(e.x, e.y, (NUKE_RADIUS + 1) * p, 0, Math.PI * 2); g.stroke();
    if (p < 0.4) { g.fillStyle = `rgba(255,255,220,${0.6 * (1 - p / 0.4)})`; dot(g, e.x, e.y, NUKE_RADIUS); }
  }

  if (started) drawPreview(g, px);
  g.setTransform(dpr, 0, 0, dpr, 0, 0);
  drawLabels(g);
  drawPopups(g, fr);
}

// ------------------------------------------------------------------ Loop
let last = 0, acc = 0;
function frame(ts) {
  if (last && started && !paused && !gameOver) acc += Math.min(ts - last, 500) * speed;
  last = ts;
  let n = 0;
  while (acc >= TICK_MS && n < 40) { doTick(); acc -= TICK_MS; n++; }
  if (acc > TICK_MS * 40) acc = 0;
  if (dirtyUI) updateUI();
  if (dirtyLog) updateLog();
  render(ts);
  requestAnimationFrame(frame);
}

// ----------------------------------------------------------------- Input
let drag = null;          // pointer press: pans once it moves a few pixels, otherwise it is a click
let helpPaused = false;

function updateHover(ev) {
  hover = started ? screenCell(ev.clientX, ev.clientY) : -1;
  if (hover < 0 || (drag && drag.moved)) { ui.tooltip.classList.add('hidden'); return; }
  ui.tooltip.textContent = tooltipFor(hover);
  ui.tooltip.classList.remove('hidden');
  const tw = ui.tooltip.offsetWidth, th = ui.tooltip.offsetHeight;
  ui.tooltip.style.left = (ev.clientX + 16 + tw > vw ? ev.clientX - tw - 12 : ev.clientX + 16) + 'px';
  ui.tooltip.style.top = (ev.clientY + 16 + th > vh ? ev.clientY - th - 12 : ev.clientY + 16) + 'px';
}

function togglePause() {
  paused = !paused;
  ui.pause.textContent = paused ? '▶' : '❚❚';
  ui.pause.title = paused ? 'Resume (Space)' : 'Pause (Space)';
}

function showHelp(open) {
  ui.help.classList.toggle('hidden', !open);
  if (!started) return;
  if (open && !paused) { helpPaused = true; togglePause(); }
  else if (!open && helpPaused) { helpPaused = false; if (paused) togglePause(); }
}

function toggleFullscreen() {
  if (document.fullscreenElement) document.exitFullscreen();
  else if (document.documentElement.requestFullscreen) document.documentElement.requestFullscreen().catch(() => {});
}

// Play enters browser fullscreen first, so the new map is sized for it
function startGame() {
  const go = () => { ui.menu.classList.add('hidden'); ui.hud.classList.remove('hidden'); resetGame(); started = true; };
  const el = document.documentElement;
  if (el.requestFullscreen && !document.fullscreenElement) el.requestFullscreen().then(() => setTimeout(go, 150), go);
  else go();
}

function init() {
  ['troops', 'cap', 'troopBar', 'gen', 'gold', 'goldGen', 'railInfo', 'cells', 'cellCount', 'status', 'statusPill', 'time',
   'commit', 'commitVal', 'buildHint', 'tools', 'leaderboard', 'factions', 'factionsToggle', 'proposals', 'log',
   'pause', 'speed', 'restart', 'fitView', 'fullscreen', 'helpBtn', 'tooltip', 'hud', 'menu', 'play', 'menuHelp',
   'help', 'helpClose', 'overlay', 'overlayTitle', 'overlayText', 'overlayRestart', 'overlayWatch'].forEach(id => ui[id] = $(id));
  ui.canvas = $('game');
  ctx = ui.canvas.getContext('2d');
  baseCanvas = document.createElement('canvas');
  bctx = baseCanvas.getContext('2d');
  resize();
  buildTools();

  ui.commit.addEventListener('input', () => { player.commit = ui.commit.value / 100; ui.commitVal.textContent = ui.commit.value + '%'; });
  ui.commit.addEventListener('change', () => ui.commit.blur());
  ui.pause.addEventListener('click', togglePause);
  ui.speed.addEventListener('change', () => { speed = parseFloat(ui.speed.value); ui.speed.blur(); });
  ui.restart.addEventListener('click', () => { if (ended || confirm('Abandon this game and start a new one?')) resetGame(); });
  ui.fitView.addEventListener('click', fitView);
  ui.fullscreen.addEventListener('click', toggleFullscreen);
  ui.helpBtn.addEventListener('click', () => showHelp(true));
  ui.menuHelp.addEventListener('click', () => showHelp(true));
  ui.helpClose.addEventListener('click', () => showHelp(false));
  ui.help.addEventListener('click', ev => { if (ev.target === ui.help) showHelp(false); });
  ui.factionsToggle.addEventListener('click', () => {
    const c = ui.factions.classList.toggle('collapsed');
    ui.factionsToggle.textContent = c ? '+' : '–';
  });
  ui.play.addEventListener('click', startGame);
  ui.overlayRestart.addEventListener('click', resetGame);
  ui.overlayWatch.addEventListener('click', () => { ui.overlay.classList.add('hidden'); gameOver = false; });
  // Buttons drop focus after a click so Space keeps meaning pause
  document.addEventListener('click', ev => { const b = ev.target.closest('button'); if (b) b.blur(); });

  const c = ui.canvas;
  c.addEventListener('pointerdown', ev => {
    drag = { x: ev.clientX, y: ev.clientY, ox: cam.ox, oy: cam.oy, moved: false, button: ev.button };
    c.setPointerCapture(ev.pointerId);
  });
  c.addEventListener('pointermove', ev => {
    if (drag) {
      const dx = ev.clientX - drag.x, dy = ev.clientY - drag.y;
      if (!drag.moved && dx * dx + dy * dy > 36) { drag.moved = true; c.classList.add('panning'); }
      if (drag.moved) { cam.ox = drag.ox + dx; cam.oy = drag.oy + dy; cam.moved = true; clampView(); }
    }
    updateHover(ev);
  });
  c.addEventListener('pointerup', ev => {
    if (drag && !drag.moved && started) {
      if (drag.button === 0) onCanvasClick(ev);
      else if (drag.button === 2) setBuildMode(null);
    }
    drag = null; c.classList.remove('panning');
  });
  c.addEventListener('pointercancel', () => { drag = null; c.classList.remove('panning'); });
  c.addEventListener('pointerleave', () => { hover = -1; ui.tooltip.classList.add('hidden'); });
  c.addEventListener('contextmenu', ev => ev.preventDefault());
  c.addEventListener('wheel', ev => {
    ev.preventDefault();
    const dy = ev.deltaMode === 1 ? ev.deltaY * 16 : ev.deltaY;
    zoomAt(ev.clientX, ev.clientY, Math.exp(-dy * 0.0015));
  }, { passive: false });
  window.addEventListener('resize', resize);

  document.addEventListener('keydown', ev => {
    if (ev.code === 'Escape' && !ui.help.classList.contains('hidden')) { showHelp(false); return; }
    if (!started || ev.target.tagName === 'INPUT' || ev.target.tagName === 'SELECT') return;
    const tool = TOOLS.find(t => 'Digit' + t.key === ev.code);
    if (tool) { if (tool.mode) setBuildMode(buildMode === tool.mode ? null : tool.mode); else doRecruit(); return; }
    switch (ev.code) {
      case 'Space': ev.preventDefault(); togglePause(); break;
      case 'Escape': setBuildMode(null); break;
      case 'KeyF': toggleFullscreen(); break;
      case 'KeyH': showHelp(ui.help.classList.contains('hidden')); break;
      case 'Digit0': case 'Home': fitView(); break;
      case 'ArrowLeft': case 'KeyA': panBy(80, 0); break;
      case 'ArrowRight': case 'KeyD': panBy(-80, 0); break;
      case 'ArrowUp': case 'KeyW': panBy(0, 80); break;
      case 'ArrowDown': case 'KeyS': panBy(0, -80); break;
    }
  });

  resetGame();            // a world to look at behind the menu
  requestAnimationFrame(frame);
}

if (typeof document !== 'undefined' && document.readyState !== 'loading') init();
else if (typeof document !== 'undefined') document.addEventListener('DOMContentLoaded', init);
