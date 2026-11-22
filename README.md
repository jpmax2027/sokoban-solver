# Sokoban Solver — push-optimal, room by room

A Sokoban solver for make.fun's [“Build the best Sokoban solver, 21 November 2026”](https://make.fun/bounty/sokoban-solver-01-run-20261121) bounty. One program, `main.ts` (Node 22, no dependencies), reads every instance of a set from `/input/<id>/level.txt` (XSB format) and writes the player's moves to `/output/<id>/solution.txt`.

## How it works

The contest's levels are clusters of small rooms (3–4 boxes each) opening off a single hallway, and a box pushed out of its room can never come back — so each room is an independent problem and the level's push optimum is the sum of its rooms' optima. The solver exploits exactly that:

1. **Room split.** Squares of the player's own row that no box could ever bring to a goal (the hallway) are cut away; each remaining part of the floor that holds boxes is one room. Rooms are solved in turn, the other rooms' boxes standing as walls (a finished room's boxes on its goals).
2. **Push-based A\* per room.** The search runs over pushes, not steps: a state is the sorted box squares plus the canonical lowest square of the player's reachable region, kept in a transposition table. The heuristic is admissible — the cheapest assignment of boxes to goals under true one-box push distances (reverse-push BFS from each goal), computed as an exact minimum-cost matching for up to six boxes and as a sum of per-box minima above that — so the first solution found is **push-optimal** for the room.
3. **Deadlock pruning** that never removes a solvable state: dead squares (a lone box there reaches no goal) and frozen 2×2 blocks of walls and boxes holding a box off its goal.
4. **Whole-level fallback.** A level that does not split into balanced rooms is searched whole with the same push A\*.

Budgets are counted in expanded states, never in wall time, and every tie is broken by a fixed order, so two executions of the program write byte-identical answers.

## Results

On the kit's practice set the solver answers all five instances in exactly the optimal number of pushes (13, 16, 29, 47, 60 — score 1,000,000 of 1,000,000) in about 0.2 s total, against the house baseline plain-astar 1.0.0's 200,000. The same perfect score holds on ten further sets drawn locally with the kit's own generator.

## Layout

- `main.ts` — the whole solver: parser, room split, push A\*, move reconstruction, and the set driver.
- `LICENSE` — MIT.
- `.makefun/owner.json` — the entrant's wallet claim file.
