// sokoban-solver: a push-based A* Sokoban solver built for make.fun's
// "Build the best Sokoban solver" bounty.
//
// Why it beats a plain move-based A*: the levels this contest draws are
// clusters of small rooms (3-4 boxes each) opening off one hallway, and a
// box can never leave its room, so the solver
//   1. splits the level into its rooms (the hallway squares a box could
//      never bring to a goal are cut away; each remaining part holding
//      boxes is one room),
//   2. solves every room on its own with an A* search over pushes (not
//      steps), which is push-optimal for that room, and the rooms' optima
//      add up to the level's optimum,
//   3. falls back to a whole-level push A* when a level does not split.
// The push A* uses a transposition table keyed by the box squares plus
// the canonical square of the player's reachable region, an admissible
// heuristic (the cheapest assignment of boxes to goals under true
// one-box push distances, computed exactly for up to six boxes and by a
// per-box minimum above that), and two deadlock prunes that never remove
// a solvable state: dead squares (a lone box there reaches no goal) and
// frozen 2x2 blocks of walls and boxes holding a box off its goal.
// All budgets are counted in expanded states, never in wall time, and
// every tie is broken by a fixed order, so two runs write the same bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// The four steps: [dx, dy, letter]. The order is fixed and breaks ties;
// opposite directions sit side by side, so k ^ 1 is the reverse of k.
const DIRS = [
  [0, -1, 'u'],
  [0, 1, 'd'],
  [-1, 0, 'l'],
  [1, 0, 'r'],
];
const INF = 1e9;
// Work budgets, in expanded push states: deterministic, never the clock.
const ROOM_CAP = 2_000_000;
const WHOLE_CAP = 2_000_000;

/** A level in XSB text: width, height, walls (frame padded as walls), goals, boxes, player. */
function parseLevel(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
    }
  }
  boxes.sort((a, b) => a - b);
  return { w, h, wall, goals, boxes, player };
}

/** nbr[i][k]: the square one step from i in direction k, or -1 when off the board. */
function neighborTable(w, h) {
  const nbr = new Int32Array(w * h * 4).fill(-1);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      for (let k = 0; k < 4; k++) {
        const nx = x + DIRS[k][0];
        const ny = y + DIRS[k][1];
        if (nx >= 0 && nx < w && ny >= 0 && ny < h) nbr[i * 4 + k] = ny * w + nx;
      }
    }
  }
  return nbr;
}

/**
 * The fewest pushes that bring a lone box from any square to `goal`,
 * ignoring the other boxes: a breadth-first walk backwards from the goal
 * over reverse pushes (a box at b came from b-d only when the square the
 * player stood on, b-2d, is open floor). -1 where no push sequence works.
 */
function boxDistances(wall, nbr, size, goal) {
  const dist = new Int32Array(size).fill(-1);
  dist[goal] = 0;
  const queue = [goal];
  for (let qi = 0; qi < queue.length; qi++) {
    const b = queue[qi];
    // Reverse push: the box arrived at b by a push in direction k, so it
    // stood at from = b - step(k) and the player stood at from - step(k).
    for (let k = 0; k < 4; k++) {
      const from = nbr[b * 4 + (k ^ 1)];
      if (from < 0 || wall[from] || dist[from] >= 0) continue;
      const stand = nbr[from * 4 + (k ^ 1)];
      if (stand < 0 || wall[stand]) continue;
      dist[from] = dist[b] + 1;
      queue.push(from);
    }
  }
  return dist;
}

/** The squares from which a lone box reaches some goal (dist >= 0 to one). */
function liveSquares(goalDist, size) {
  const live = new Uint8Array(size);
  for (const dist of goalDist) {
    for (let i = 0; i < size; i++) if (dist[i] >= 0) live[i] = 1;
  }
  return live;
}

/**
 * Marks the squares the player reaches from `from` with boxes (boxFlag)
 * in the way, using `seen`/`stamp`; returns the lowest square reached,
 * the canonical name of the player's region.
 */
function floodRegion(wall, nbr, size, boxFlag, from, seen, stamp, stack) {
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n];
    if (p < low) low = p;
    for (let k = 0; k < 4; k++) {
      const q = nbr[p * 4 + k];
      if (q >= 0 && !wall[q] && !boxFlag[q] && seen[q] !== stamp) {
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
  }
  return low;
}

/** Whether the box just pushed to t froze a 2x2 block of walls/boxes with a box off its goal. */
function frozenBlock(w, wall, boxFlag, goalFlag, t) {
  const tx = t % w;
  const ty = Math.floor(t / w);
  for (const [ox, oy] of [[0, 0], [-1, 0], [0, -1], [-1, -1]]) {
    const x = tx + ox;
    const y = ty + oy;
    if (x < 0 || y < 0 || x + 1 >= w) continue;
    const a = y * w + x;
    const cells = [a, a + 1, a + w, a + w + 1];
    let blocked = true;
    let offGoal = false;
    for (const c of cells) {
      if (!wall[c] && !boxFlag[c]) { blocked = false; break; }
      if (boxFlag[c] && !goalFlag[c]) offGoal = true;
    }
    if (blocked && offGoal) return true;
  }
  return false;
}

/** The shortest walk from `from` to `to` around walls and boxes, in lower LURD letters. */
function walkMoves(wall, nbr, boxFlag, from, to) {
  if (from === to) return '';
  const size = wall.length;
  const prev = new Int32Array(size).fill(-1);
  const how = new Int8Array(size).fill(-1);
  const queue = [from];
  prev[from] = from;
  for (let qi = 0; qi < queue.length; qi++) {
    const p = queue[qi];
    if (p === to) break;
    for (let k = 0; k < 4; k++) {
      const q = nbr[p * 4 + k];
      if (q < 0 || wall[q] || boxFlag[q] || prev[q] !== -1) continue;
      prev[q] = p;
      how[q] = k;
      queue.push(q);
    }
  }
  if (prev[to] === -1) return null;
  let s = '';
  for (let p = to; p !== from; p = prev[p]) s = DIRS[how[p]][2] + s;
  return s;
}

/**
 * A push-optimal solution of one (sub-)level as a move string, or null
 * when the expansion budget runs out first. A* over pushes: a state is
 * the sorted box squares plus the player's region; the cost so far is
 * pushes; the estimate is the cheapest box-to-goal assignment under the
 * one-box push distances (exact matching for up to six boxes, a sum of
 * per-box minima above that) — admissible, so the first goal state
 * popped is push-optimal.
 */
function solvePushes(w, h, wall, goals, boxes0, player0, cap) {
  const size = w * h;
  const nbr = neighborTable(w, h);
  const goalFlag = new Uint8Array(size);
  for (const g of goals) goalFlag[g] = 1;
  const goalDist = goals.map((g) => boxDistances(wall, nbr, size, g));
  const live = liveSquares(goalDist, size);
  if (boxes0.some((b) => !live[b])) return null;
  const n = boxes0.length;
  if (n === 0) return '';

  // Admissible estimate for a box set. The exact matching below reads
  // goalDist[j] for j < n, so it runs only when goals and boxes balance
  // (always true of a room, and of any solvable level); an unbalanced
  // board takes the per-box minimum over all its goals instead.
  const dp = new Float64Array(1 << Math.max(1, n));
  const heuristic = (boxes) => {
    if (n <= 6 && goals.length === n) {
      // dp[mask]: cheapest cost of putting the first popcount(mask)
      // boxes onto the goals named by mask.
      dp.fill(INF, 0, 1 << n);
      dp[0] = 0;
      for (let mask = 0; mask < (1 << n); mask++) {
        const i = popcount(mask);
        if (i >= n || dp[mask] >= INF) continue;
        for (let j = 0; j < n; j++) {
          if (mask & (1 << j)) continue;
          const d = goalDist[j][boxes[i]];
          if (d < 0) continue;
          const nm = mask | (1 << j);
          if (dp[mask] + d < dp[nm]) dp[nm] = dp[mask] + d;
        }
      }
      return dp[(1 << n) - 1];
    }
    let sum = 0;
    for (const b of boxes) {
      let best = INF;
      for (let j = 0; j < goalDist.length; j++) {
        const d = goalDist[j][b];
        if (d >= 0 && d < best) best = d;
      }
      if (best >= INF) return INF;
      sum += best;
    }
    return sum;
  };

  const boxFlag = new Uint8Array(size);
  const seen = new Int32Array(size);
  // A second mark array for the regions of child states: a child's flood
  // must never overwrite the marks of the region being expanded, which
  // the remaining pushes of this state are still checked against.
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  const keyOf = (boxes, regionLow) => String.fromCharCode(regionLow, ...boxes);

  // State store: parallel arrays; a push is encoded boxFrom * 4 + dir.
  const sBoxes = [boxes0.slice()];
  const sPlayer = [player0];
  const sParent = [-1];
  const sPush = [-1];
  const sG = [0];
  const sKey = [''];
  for (const b of boxes0) boxFlag[b] = 1;
  stamp++;
  const startRegion = floodRegion(wall, nbr, size, boxFlag, player0, seen, stamp, stack);
  for (const b of boxes0) boxFlag[b] = 0;
  sKey[0] = keyOf(boxes0, startRegion);
  const best = new Map([[sKey[0], 0]]);

  // The open list: a binary heap on (f, deeper first, earlier first).
  const heap = [];
  let counter = 0;
  const hLess = (a, b) => a[0] < b[0] || (a[0] === b[0] && (a[1] > b[1] || (a[1] === b[1] && a[2] < b[2])));
  const hPush = (e) => {
    let i = heap.length;
    heap.push(e);
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!hLess(heap[i], heap[p])) break;
      [heap[i], heap[p]] = [heap[p], heap[i]];
      i = p;
    }
  };
  const hPop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && hLess(heap[c + 1], heap[c])) c++;
        if (!hLess(heap[c], heap[i])) break;
        [heap[i], heap[c]] = [heap[c], heap[i]];
        i = c;
      }
    }
    return top;
  };
  hPush([heuristic(boxes0), 0, counter++, 0]);

  let found = -1;
  let expanded = 0;
  while (heap.length > 0 && expanded < cap) {
    const [, , , s] = hPop();
    if (best.get(sKey[s]) !== sG[s]) continue; // a cheaper route superseded this entry
    const boxes = sBoxes[s];
    if (boxes.every((b) => goalFlag[b])) { found = s; break; }
    expanded++;
    for (const b of boxes) boxFlag[b] = 1;
    stamp++;
    floodRegion(wall, nbr, size, boxFlag, sPlayer[s], seen, stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length; bi++) {
      const b = boxes[bi];
      for (let k = 0; k < 4; k++) {
        const target = nbr[b * 4 + k];
        const stand = nbr[b * 4 + (k ^ 1)];
        if (target < 0 || stand < 0) continue;
        if (seen[stand] !== here) continue; // the player cannot stand there
        if (wall[target] || boxFlag[target] || !live[target]) continue;
        boxFlag[b] = 0;
        boxFlag[target] = 1;
        const frozen = frozenBlock(w, wall, boxFlag, goalFlag, target);
        let childKey = null;
        let childBoxes = null;
        if (!frozen) {
          childBoxes = boxes.slice();
          childBoxes[bi] = target;
          childBoxes.sort((a, b2) => a - b2);
          stamp++;
          const region = floodRegion(wall, nbr, size, boxFlag, b, mark, stamp, stack);
          childKey = keyOf(childBoxes, region);
        }
        boxFlag[target] = 0;
        boxFlag[b] = 1;
        if (frozen) continue;
        const g = sG[s] + 1;
        const seenG = best.get(childKey);
        if (seenG !== undefined && seenG <= g) continue;
        const hEst = heuristic(childBoxes);
        if (hEst >= INF) continue;
        best.set(childKey, g);
        const t = sBoxes.length;
        sBoxes.push(childBoxes);
        sPlayer.push(b); // after the push the player stands where the box was
        sParent.push(s);
        sPush.push(b * 4 + k);
        sG.push(g);
        sKey.push(childKey);
        hPush([g + hEst, g, counter++, t]);
      }
    }
    for (const b of boxes) boxFlag[b] = 0;
  }
  if (found < 0) return null;

  // The push path, root last; then the moves: walk to each push, push.
  const path = [];
  for (let s = found; s > 0; s = sParent[s]) path.push(sPush[s]);
  path.reverse();
  const curFlag = new Uint8Array(size);
  const curBoxes = new Set(boxes0);
  for (const b of boxes0) curFlag[b] = 1;
  let player = player0;
  let moves = '';
  for (const push of path) {
    const boxFrom = Math.floor(push / 4);
    const k = push % 4;
    const stand = nbr[boxFrom * 4 + (k ^ 1)];
    const walk = walkMoves(wall, nbr, curFlag, player, stand);
    if (walk === null) return null;
    moves += walk + DIRS[k][2];
    const boxTo = nbr[boxFrom * 4 + k];
    curFlag[boxFrom] = 0;
    curFlag[boxTo] = 1;
    curBoxes.delete(boxFrom);
    curBoxes.add(boxTo);
    player = boxFrom;
  }
  return moves;
}

function popcount(x) {
  let c = 0;
  while (x) { x &= x - 1; c++; }
  return c;
}

/**
 * The level's rooms: cut the squares of the player's own row that no box
 * could ever bring to a goal (the hallway) out of the floor; each part
 * left is a room. Null when the level is no set of rooms: a box starts
 * in the hallway, a goal lies outside every part, or a part's boxes and
 * goals do not balance.
 */
function splitRooms(L) {
  const { w, h, wall, goals, boxes, player } = L;
  const size = w * h;
  const nbr = neighborTable(w, h);
  const goalDist = goals.map((g) => boxDistances(wall, nbr, size, g));
  const live = liveSquares(goalDist, size);
  const row = Math.floor(player / w);
  const cut = new Uint8Array(size);
  for (let x = 0; x < w; x++) {
    const i = row * w + x;
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(size).fill(-1);
  const rooms = [];
  const stack = [];
  for (let s = 0; s < size; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const id = rooms.length;
    const squares = [s];
    part[s] = id;
    stack.push(s);
    while (stack.length > 0) {
      const p = stack.pop();
      for (let k = 0; k < 4; k++) {
        const q = nbr[p * 4 + k];
        if (q >= 0 && !wall[q] && !cut[q] && part[q] < 0) {
          part[q] = id;
          squares.push(q);
          stack.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) {
    if (part[g] < 0) return null;
    rooms[part[g]].goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/** The square the player stands on after playing `moves` from `from`. */
function endOf(w, from, moves) {
  let p = from;
  for (const ch of moves) {
    p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  }
  return p;
}

/** The moves that solve one level text, or '' when no search solves it. */
function solveLevel(text) {
  const L = parseLevel(text);
  const goalFlag = new Uint8Array(L.w * L.h);
  for (const g of L.goals) goalFlag[g] = 1;
  if (L.boxes.every((b) => goalFlag[b])) return '';
  const rooms = splitRooms(L);
  if (rooms !== null) {
    let player = L.player;
    let moves = '';
    let ok = true;
    const done = new Array(rooms.length).fill(false);
    for (let ri = 0; ri < rooms.length; ri++) {
      const room = rooms[ri];
      // The other rooms' boxes stand as walls: an undone room's at their
      // start squares, a done room's on its goals.
      const wall = L.wall.slice();
      rooms.forEach((other, oi) => {
        if (oi === ri) return;
        for (const s of done[oi] ? other.goals : other.boxes) wall[s] = 1;
      });
      const sub = solvePushes(L.w, L.h, wall, room.goals.slice().sort((a, b) => a - b), room.boxes.slice().sort((a, b) => a - b), player, ROOM_CAP);
      if (sub === null) { ok = false; break; }
      moves += sub;
      player = endOf(L.w, player, sub);
      done[ri] = true;
    }
    if (ok) return moves;
    // A room beat the budget: try the whole level before giving up.
    const whole = solvePushes(L.w, L.h, L.wall, L.goals, L.boxes, L.player, WHOLE_CAP);
    return whole !== null ? whole : moves;
  }
  const whole = solvePushes(L.w, L.h, L.wall, L.goals, L.boxes, L.player, WHOLE_CAP);
  return whole !== null ? whole : '';
}

for (const id of readdirSync(I).sort()) {
  const moves = solveLevel(readFileSync(join(I, id, 'level.txt'), 'utf8'));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
