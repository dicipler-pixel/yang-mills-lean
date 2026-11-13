# Yang-Mills harness blueprint — 12 November 2026

System of record for the agent team working on `dicipler-pixel/yang-mills-lean` at commit `ff9c203`.
Orchestrator: Claude (this session). Research programme of Jeromie Beasley.

## Design (after LeanMarathon, arXiv 2606.05400, and the planner / generator / evaluator split)

1. One blueprint (this file) holds every target, its acceptance check and its kill condition.
2. Each agent has one contract and one output folder. No agent edits another agent's files.
3. Agents only propose. A result is accepted only when a script exits 0 under the orchestrator's
   own rerun, with exact arithmetic where the claim is exact. No result is accepted on an agent's say-so.
4. Stage 1 is adversarial review of what exists. Stage 2 builds only on what survived stage 1.
5. Kill conditions are written here before the run. A failed target is recorded, not hidden.
6. Nothing is pushed to GitHub by an agent. The orchestrator commits accepted artifacts to one branch.

## Stage 1 targets (check what exists)

| ID | Target | Owner | Acceptance check | Kill condition |
|---|---|---|---|---|
| V1 | Every Python verifier in the repo reruns from a clean copy | verifier | exit code 0 and the stated counts (20 certificates, 58 targets, window-wall cells) reproduced | any nonzero exit, or a count that differs from the document that quotes it |
| A1 | Two-square electric spectrum through 40/3 is exactly the 19 states of TWO_PLAQUETTES.md | auditor | an independent enumeration from SU(3) tensor rules, sharing no code with the repo, gives cumulative dimensions 1,5,7,9,11,13,15,19 and next level 43/3 | any state with energy <= 40/3 missing or extra |
| A2 | On the five graphs the C <= 8 physical space is the constant plus both orientations of each 4- and 6-cycle, and the omitted floor is 28/3 | auditor | independent support enumeration gives retained dimensions 7, 11, 15, 45, 95 and no admissible state with 8 < C < 28/3 | a counterexample support or a different dimension |
| A3 | Allocation coefficients of LOCAL_ENERGY_FLOORS.md (7/2, 3, 2, 20/11 average) | auditor | recomputed from the graphs | any mismatch |
| A4 | One sampled spatial certificate reproduced end to end without repo code | auditor | independent float eigenvalue of the retained pencil lies above the certified lower bound, and the certified bound is below a larger-basis reference gap | certified bound above a converged reference gap |

## Stage 2 targets (make it stronger)

| ID | Target | Owner | Acceptance check | Kill condition |
|---|---|---|---|---|
| S1 | Two-square cell: certified gap lower bounds beyond the 19-state cutoff, where the present certificate fails or is weak (lambda = 3, 4, then 6, 8) | strengthener | exact or outward-interval inertia certificate with complete-tail floor, a rejected shifted control, and bound <= the ECUT 250 float gap in the repo table | bound exceeds the float reference, or the hidden floor argument has a gap |
| S2 | One-plaquette efficiency table: smallest cutoff at which the scalar and the matrix certificates each reach a fixed fraction of the gap, lambda in {1, 10, 100} | strengthener (after S1) or orchestrator | script reproduces orchestrator's numbers at lambda = 100 (matrix N = 25, scalar positive near N = 50) | disagreement with the independent check |
| P1 | Prior-art section naming the partitioning / intermediate-problem lineage beside Feshbach-Schur | orchestrator | every cited statement located in its source | a citation that cannot be located |

## Ledger

Results are appended below by the orchestrator only.

### 12 November 2026 — stage 1 and stage 2 results (each rerun by the orchestrator)

| ID | Result | Evidence |
|---|---|---|
| V1 | 38 of 47 script runs pass as shipped; the 58-target recheck passes (two squares, strip, corner, cube, double cube); `scripts/verify.py --gate-only` passes | `harness/verifier/VERIFY_LEDGER.md` |
| V1 | FAIL as shipped: `research/2026-11-10/window_wall_endpoints/certify_slopes.py` has a hardcoded path `/workspace/yang-mills-lean/...`; it passes in a scratch copy with the path corrected | same ledger |
| V1 | Count mismatches: `kyfan_certificate_grey/README.md` says 25 trial vectors, the script prints 26; `varying_s_lp.py` prints strip t <= 36/35 while the README lists t = 1 from `strip_settle.py` | same ledger |
| V1 | NOT RUN: the Lean build (no Lean in the harness workspace), `theta_reference.py`, and the ECUT 200 to 300 sweeps | same ledger |
| A1 | SURVIVES: cumulative dimensions 1, 5, 7, 9, 11, 13, 15, 19; nothing between 40/3 and 43/3 | `harness/auditor/audit_a1.py` |
| A2 | SURVIVES: dimensions 7, 11, 15, 45, 95; no state with 8 < C < 28/3 on any of the five graphs (137,979 link subsets on two cubes) | `harness/auditor/audit_a2.py` |
| A3 | SURVIVES: 7/2, 3, 2; two-cube faces 11/6 (eight), 2 (two), 4/3 (shared), average 20/11 | `harness/auditor/audit_a3.py` |
| A4 | SURVIVES as a necessary condition only: 2 g(7/2) = 5.762609 <= 5.794723 | `harness/auditor/audit_a4.py` |
| S1 | Two-square gap certified with exact matrices: >= 4.834242 at lambda = 3 (ECUT 50, 760 states), >= 5.205208 at 4, >= 6.433831 at 6 (ECUT 60, 1343 states), >= 7.792135 at 8; each control rejected; each bound below the ECUT 250 reference gap. Orchestrator rerun: exit 0 in 229 s | `harness_strengthener/certify_twosquare_extended.py` |
| S1 | OPEN: the coefficient formula for multiplication by Tr U on blocks with multiplicity is a hand derivation, supported by exact identities and 12-digit agreement with the independent float build, not yet proved independently | `harness_strengthener/STRENGTHENER.md` |
| S2 | Matrix certificate reaches 99% of the one-plaquette gap at N = 3, 8, 19 for lambda = 1, 10, 100; the scalar bound needs N = 15 at lambda = 1, does not reach 99% by N = 80 at 10 or 100, and first turns positive at N = 45 for lambda = 100 | `harness_strengthener/one_plaquette_efficiency.py` |
| P1 | Not done yet | |

Document gaps found by the auditor (no number changes): `SPATIAL_BASES.md` says five graphs and defines four; `TWO_PLAQUETTES.md` uses the squared multiplicity without justification; 20/11 is the average of the even split on two cubes, not the split itself.
