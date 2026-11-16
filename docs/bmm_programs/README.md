# Programs for "The BMM symmetrising trace conjecture for all exceptional complex reflection groups"

This folder holds the programs behind the computations of the paper, their input data, and their complete output.
Each program writes a **record**: a text file in the group's folder that lists every identity tested and its result.
All records are included, so the results can be checked without running anything.

Statement numbers in this file refer to the draft of the paper of 16 November 2026. The program comments and the
records cite an earlier numbering; Section 8 translates it.

## 1. What is verified, and where

One machine serves all 28 non-real exceptional groups, with **one procedure for every coset table**: the setRow
procedure of §4.3 of the paper (Example 4.8, Remark 4.9). A group is described by its **group file**
`GNN/groupNN.toml`, and the same five programs run for every group (`julia programs/NAME.jl GNN`, or
`./run.sh GNN STEP`):

| step | program | record | what it does | arithmetic |
|---|---|---|---|---|
| bfs | `bfs_basis.jl` | `1_bfs_basis.txt` | finds the coset table of the basis A by setRow sweeps and writes it as a program, `cosettableNN.txt` | mod p |
| modular | `zbasis_modular.jl` | `2_zbasis_modular.txt` | the candidate B and every test of the proof at one point (Modular tests 1 and 2, Lemmas 3.11, 3.12) | mod p |
| proof | `bmm_proof.jl` | `3_bmm_proof.txt` | **the proof**: Theorem 4.10 (A is a basis), then the conditions of the conjecture for τ_B | exact |
| traces | `trace_values.jl` | `4_trace_values.txt` | values τ(T_w) of the canonical trace | exact |
| orders | `bfs_orders.jl` | `5_bfs_orders.txt` | the rows of Figure 2: every ordering o of the three generating sets (G4–G29) | mod p |

| Claim of the paper | Groups | Record |
|---|---|---|
| Theorem 4.10: BFS_o is a basis (o = the ordering of the group file; for G32 the seeded tree of §6.3.3) | all | `3_bmm_proof.txt`, stage "Coset table of A" |
| Proposition 5.11 and Theorem 5.12: B_j is a z^k-basis and τ_{B_j} satisfies the conjecture | G4–G29 | `3_bmm_proof.txt` |
| Proposition 6.3 (the parabolic criterion) with the pairings of §6.3; Theorem 6.11 | G31–G34 | `3_bmm_proof.txt` |
| Remark 6.12: the parabolic freeness conjecture for each pair of consecutive levels of the towers | G31–G34 | `3_bmm_proof.txt`, the stages "Coset table of A" of every level and of the top |
| Modular test 1 (Lemma 3.11) for B_j; the triple (J,i,m) of E_j (§5.3, Table 1) | G4–G29 | `2_zbasis_modular.txt` |
| Figure 2, rows G4–G29 | G4–G29 | `5_bfs_orders.txt` |
| values of the canonical trace | all | `4_trace_values.txt` |

A proof record ends with a line `all N tests true`; a record written through `run.sh` then ends with
`# <date>  exit code 0`. Every `testing ... true` line names the identity it checked. Records 1, 2 and 5 are computed
modulo p at one point: they guide the search and can only prove negative results (det ≠ ±1 means "not a basis").
Every proof is exact.

Two libraries run the setRow procedure. They differ only in the coefficients of the coset table, i.e. in the
parabolic subgroup P of the basis B_P · T_o (Definition 4.5); the group file names the one it uses (field `engine`):

| engine | groups | P and the coefficients of the table | library |
|---|---|---|---|
| cyclic (default) | G4–G29 | U = ⟨u⟩ cyclic; coefficients in H(U) ⊗ R' | `lib/hecke.jl` and the rest of `lib/` |
| tower | G31–G34 | P non-cyclic, built as a tower 1 < P_1 < … < P; coefficients in H(P), a flat algebra built level by level, each level's table filled by the same procedure | `lib/tower/` (`setrow.jl`: the procedure over H(P)) |

Whatever the engine, the proof tests the same conditions in the same stages (Section 4).

## 2. Requirements and a first run

Julia 1.12 (tested with 1.12.5) and the package Chevie 0.1.11. The files `Project.toml` and `Manifest.toml` pin Chevie
and its dependencies to the versions that produced the records; every other package used is in Julia's standard
library. Install them once, from this folder:

    julia --project=. -e 'import Pkg; Pkg.instantiate()'

Then, from this folder:

    julia --project=. programs/bmm_proof.jl G4     # about 15 s; rewrites G4/3_bmm_proof.txt
    ./run.sh G4                                    # the same, niced, with the threads and memory cap of the group file (systemd-run)

Running a program overwrites its record; only dates and times should differ from the shipped version.
Time and memory: for G4–G29 each program takes 10 s – 3 min and less than 3 GB, except the proof for G19 (16 min,
4.4 GB). G31: about 23 min for the four steps (the proof 11 min, the traces 9 min, 1.7 GB). G32: about 20 min (the proof 16 min,
2.1 GB). G33: about 2 min. G34 (`./run.sh G34 all`, on a machine with 16 GB of memory; the group file sets the memory
cap to 14G and Julia's `--heap-size-hint` to 11G): 1 h 56 min and 8.2 GB for the step bfs, 30 h and 13 GB for the proof
(the Gram matrix of H(G33), exact), 24 min and 8.5 GB for the traces. G34 has no record 2: its step modular is not run,
the exact proof being the one that proves the result. The proof of G34 does not test two braid relations of G33,
s4 s2 s3 s4 s2 s3 = s3 s4 s2 s3 s4 s2 = s2 s3 s4 s2 s3 s4, on the 756 cosets of the top (field `proof_skip_top_relations`
of the group file; its record says so where they would be). They are a check of the implementation, not a step of
the proof: B is a basis because the table closes. They hold modulo p in `G34/1_bfs_basis.txt`, and they are tested
exactly at the level G33 of the tower.

## 3. Conventions

* **Words.** A word is a list of letters. Letters 1..n are the generators s_1..s_n in the order of the group file,
  n+1 is the central element z, and a negative letter is an inverse: `[1, 2, -1]` is s_1 s_2 s_1^-1.
* **Parameters.** Hecke relations are written as (2.2) of the paper: T^k = r_{k-1} T^{k-1} + ... + r_1 T + r_0, with one
  list per conjugacy class. They are named e_j (order 2), c_j (3), a_j (4), d_j (5) (b_j, f_j for a second class of
  order 3 or 2), where the paper writes a_(s,j) for the class of s; r_0 is invertible, and
  R = Z[r_j][r_0^±1] is the ring R(W) of §2.1 of the paper.
* **Exact means over R' = R/(r_0 - 1)**, i.e. every invertible parameter set to 1 (the ring R̄(W) of §3.1 of the paper).
  Nothing is lost (§3.2 of the paper):
  * each tested identity is between homogeneous elements of the same degree (Lemmas 3.6, 3.7);
  * a homogeneous element of R that maps to 0 in R' is 0, and one that maps to ±1 is a unit (Lemma 3.3);
  * `lift_to_R` (`lib/poly.jl`) restores the powers of r_0, and a unit determinant appears as ±1;
  * coefficients are overflow-checked Int64 (`lib/poly.jl`; for the engine cyclic the group file can ask for Int128
    with `coefficients = "Int128"`, which no group needs; the engine tower uses `lib/tower/ring.jl`, Int64 only).

  G31, G33 and G34 are computed over Z[e1] (T² = e1 T + 1), G32 over Z[c1, c2] (T³ = c2 T² + c1 T + 1).
* **Modular** means modulo p = 15013, at a point of R'. The defaults are the values 11, 13, 17, ... for the
  non-invertible parameters; `--point=` and `--p=` override them.

## 4. The group file, the data and the records

Each folder `GNN/` holds the group file, the data and the records.

* `groupNN.toml`: the **group file**. It gives the generators, the Hecke and braid relations, z, the parabolic
  (the letter u for the engine cyclic; the tower `[[level]]` for the engine tower), the ordering o of BFS_o, k, the
  triple (J,i,m) of E_j, and, where listed, the Gram determinant det Gram(τ_B). The header of `lib/spec.jl` matches each field
  with the notation of the paper; the header of `lib/tower/driver.jl` lists the fields of the engine tower.
* `basisNN.txt`: the words X of the basis B. For G4–G29, B = {T_z^(kj)}·{T_u^m}·T_X is the z^k-basis B_j
  (Definition 5.3). For G31, X_31 = T_o(P\W), o = (s2, s3, s4, s5, s1), over P = ⟨s1, s2, s3, s5⟩ ≅ G(4,2,3)
  (§6.3.2); for G32, X_32 = T^σ_(s1,s2,s3,s4)(P\W), the seeded tree of §6.3.3 over P = G25; for G33 and
  G34, Marin–Pfeiffer's coset words X_33 over A4 and X_34 over G33 (§6.3.1).
* `cosettableNN.txt`: the vector enumeration of A, as a program of `makeEdge`/`setRow` commands (Remark 4.9,
  Example 4.8); the rule of each `setRow` is gen, inv or rel. For G31–G34 it is the table of the top level, over H(P);
  the levels below are rebuilt by the same procedure at each run.
* `3_F0.txt` (G4–G29, when F_0 has at most 40 000 terms): the block F_0 written out by the proof. `G31/pairing31.txt`: the set
  Y_31 = T_(s1,s2,s3,s4,s5,z)(P\W) of the pairing of G31 (§6.3.2). `G32/family32.txt`: the pairing (Y_32, Y'_32) of §6.3.3.

**The stages of `3_bmm_proof.txt`**, the same for every engine. Each runs over R'.

| stage | identities tested | what they prove |
|---|---|---|
| Coset table of A | every command of `cosettableNN.txt` executes exactly (the table closes) | A spans, hence is a basis: Propositions 2.4 and 3.8 (1), Theorem 4.10 |
| Relations of H on the table | the Hecke and braid relations, T_z central | a check of the implementation |
| Bimodule map (engine tower) | E(x_n T_s) = δ_(n,1) T_s for s in P | Lemma 6.1 |
| Linear form t: symmetry | t(a T_s) = t(T_s a) for every a in A (G4–G29) or in B = B_P · X (G31–G34, at every level of the tower), and every generator s | Proposition 5.7 (the symmetry criterion); (V1) of §5.3; Proposition 6.7 |
| Values on B | t(b) = δ_(b,1) for b in B (G4–G29; for G31–G34, B = B_P · X is the basis of the table and this holds by the definition of t, as the record states) | t = τ_B: (V3) of §5.3; §6.1 |
| Pairing | the blocks F_r of Gram_t(B, B^-1) vanish for r > 0 and det F_0 = ±1; or the pairing matrix over H(P) is triangular with unit diagonal, or eliminates with unit pivots | B is a basis and t a symmetrising trace: Lemmas 5.9, 5.10 and (V2) (G4–G29), Lemma 6.2 and Propositions 6.3, 6.4 (G31–G34) |
| Condition (3) | t(b^-1 T_π) = 0 for b ≠ 1, t(T_π) a unit | condition (3) of Conjecture 2.5, in the form (2.4): (V4) (G4–G29), Lemma 6.9 (G31–G34) |
| Result | — | Theorem 5.12 / Theorem 6.11; det Gram(τ_B), derived, not computed: its exponents read off the degrees of the basis, its sign (−1)^((\|W\| − I)/2) at the group-algebra point, I the number of w in W with w² = 1 (not in the paper) |

For G4–G29 the linear form t is E_j of §5.3: t(h) = [T_u^m T_(w_i)](T_z^-kJ h), the coefficient of T_u^m T_(w_i) in A,
with the triple (J,i,m) of Table 1 (G17, G18, G19, G27) or (0,1,0) (t = λ_1^A, all other groups); for
G31–G34 it is τ^P ∘ E_X, the coefficient of 1 on B_P·X. Condition (2) holds by specialisation and is not computed.

The basis A of G7, G11, G13 and G15 is a BFS_o on which λ_1^A is already the
canonical trace, with o = (s, t, z), (s, z, u), (t, u, s), (s, t, z), so their triple is (0,1,0).

**G16 and G21.** Their basis A is also a quasi-symmetric BFS_o (λ_1^A is the canonical trace), with o = (s, z, t)
for G16 and o = (s, t) for G21, so their triple is (0,1,0). For G21 no ordering with z has a complete table
(`G21/5_bfs_orders.txt`, family (2)); (s, t) is its only quasi-symmetric ordering whose table completes.

## 5. The engines, in a few words

* **cyclic** (`lib/hecke.jl`, `trace.jl`, `tests.jl`, …): the coset table of A lives in Λ^N with Λ = H(⟨u⟩) ⊗ R'; a
  `setRow` command computes one row from the tree, a Hecke relation or a braid identity (§4.3); the table found modulo
  p by `bfs_basis.jl` is replayed exactly by `bmm_proof.jl`. The blocks F_r are computed from |X| coordinate vectors
  against |X| functionals (`lib/tests.jl`, header), and det F_0 by Bareiss elimination.
* **tower** (`lib/tower/`): H(P) is built as a flat algebra from its own coset table one level below, each table
  filled by the setRow procedure (`setrow.jl`) with coefficients in the algebra of the level below; at the top, the
  program `cosettableNN.txt` found modulo p is executed exactly. Every level is proved with the conditions of
  Proposition 6.3 before it becomes the coefficient algebra of the next. The symmetry is Proposition 5.7 on B = B_P · X for
  every generator s: t(b x T_s) = τ_P(b E(x T_s)) and t(T_s b x) = Σ_n τ_P((T_s b)_n E(x_n x)), with the rows T_s b
  computed along the tree of B_P, the columns (E(x_n x))_n along the suffixes of the words of X, and τ_P(h h') through
  the Gram matrix of H(P), itself computed through the table of the level below (`twostep.jl`, `test_symmetry`,
  `gram_from_table!`). The pairings (Proposition 6.3 (2)):
  * G31 (§6.3.2): the table and t = τ^P ∘ E_X live on X_31; the pairing is M_X(Y_31, Ȳ_31) with
    Y_31 = T_(s1,...,s5,z)(P\W) (`pairing31.txt`) and Ȳ_31 = { rev(w) z^-i : w z^i in Y_31 }. Ordered by the number
    of letters z, M is block triangular with triangular diagonal blocks, and all diagonal entries are basis elements
    of H(P).
  * G32 (§6.3.3): M_X(Y_32, Y'_32) with the family `family32.txt`, unitriangular.
  * G33, G34 (§6.3.1): M_X(X, X̄), X̄ the reversed words: block triangular, its non-trivial blocks (one of size 6 for
    G33; sizes 3 and 18 for G34) eliminated over H(P) with unit pivots. The level G33 of the tower of G34 is proved
    with the same pairing as the top of G33 (`pairing = "rev"` in that `[[level]]` of `G34/group34.toml`): below the
    top, the engine otherwise asks M_X(X, X̄) to be triangular, which fails at that level (the block of size 6).
  Condition (3) through ζ (G31–G34 at the top, ζ = z^j with ζ² = π): ψ = M_ζ e_1 lives on one coset c, and
  t(T_π) = τ_P((T_ζ)_c ψ_c). The coefficient (T_ζ)_c of x_c in T_ζ is computed as Σ_n (T_u)_n (M_v e_c)_n with
  ζ = u v, v = z: the row of T_u = T_z^(j-1) against the column M_z e_c (`driver.jl`, `condition3_pieces`).

## 6. The canonical trace in other computations

    using Chevie; include("lib/hecke.jl")
    T = load_trace("G16")                     # any group: the table and the trace (G34 builds its exact table first: hours)
    can_trace(T, [1, 2, -1])                  # τ(T_s T_t T_s^-1) in R
    can_trace(T, [[1], [1, 2], [3]])          # several words; trace(T, w) gives the value in R'

On a section basis (Conjecture 2.6) the canonical trace is the coefficient of 1. The values are lifted to R(W) by
homogeneity (Remark 5.13).

## 7. Running everything

`./run.sh GNN STEP` runs one step niced, in the Julia environment of this folder, with the threads, the memory cap and
Julia's heap-size hint of the group file (`threads`, `memory`, `heap`; `THREADS`, `MEMMAX` and `HEAP` override them).
`./run.sh GNN all` runs the steps listed in the group file (`steps`; default bfs modular proof traces orders;
G31–G33: bfs modular proof traces; G34: bfs proof traces). A step an engine does not have (orders for tower) says so
and exits with code 3.

`./run_all.sh` remakes every record of G4–G33 (about an hour); G34 is run by hand (`./run.sh G34 all`, or one step at
a time), since its steps take hours each. `run_all.sh` skips any record that already ends with `exit code 0` and logs
its progress in `run_all.log`. Once the environment is instantiated (Section 2) nothing needs the internet: Chevie
comes from the local Julia depot, and `run.sh` keeps the package manager offline. A step cut short by a reboot leaves a record without `exit code 0`, so running
`./run_all.sh` again resumes at that step; a single step restarts from its beginning, except the steps modular and
proof of the engine tower (G31–G34), which resume from a checkpoint.

**Checkpoints (engine tower, steps modular and proof).** The step runs a fixed list of pieces: each stage of each
level and of the top, the long stages cut into pieces (the relations line by line; the columns of the pairing
M(X, rev X), the column ψ of T_π or T_ζ, the row of T_u and the column M_v e_c (ζ = u v), and the walk of the tree in
condition (3), in 24 slices each). After a piece, at
most every 30 minutes (environment variable `CHECKPOINT_SECONDS`), the step writes its partial results to
`GNN/checkpoint/<record>.jls`, with the counts of the tests and the length of the record. Run again after an
interruption (power loss, reboot, out of memory), it rebuilds the tables and algebras of the pieces already done,
silently (each level by the setRow procedure, the top by the program of the table file; G34: about 25 minutes
exactly), cuts its record back to the checkpoint, writes a line `# <date>  resumed from the checkpoint written on
<date> after: <piece>; ...`, and continues. Nothing else in the record changes: an interrupted and resumed run gives
the same record as an uninterrupted one, apart from these lines, the dates and the times (tested on G31, G32 and G33,
including runs killed with SIGKILL in the middle of a piece). A checkpoint is used only by the same programs (every
`.jl` file of `lib/` and `programs/`), group file, data files and command line; it is deleted when the record is
finished. Details: `lib/tower/driver.jl`, "the plan and the checkpoints".

**The record of G34.** Its proof ran 30 h and was resumed twice from a checkpoint (the two lines `resumed` of
`G34/3_bmm_proof.txt`). Between the interruptions the programs changed in three places, none of which changes a
value: the field `proof_skip_top_relations` (14 November), a faster addition of terms in `lib/tower/ring.jl`
(`combine!`, 15 November: the same terms in the same order, with the same overflow checks), and products formed depth
first in `lib/tower/alg.jl` (`mul_path`, `taumul`, 15 November). Each time the checkpoint was carried over to the new
programs by hand, and the proofs of G31, G32 and G33 were rerun with them and gave their records line for line. So
the record of G34 was written by three versions of the programs: up to line 17 of the relations of the top by those of
13 November, up to the columns of the pairing by those of 14 November, and the rest (the pairing matrix and condition
(3)) by the programs shipped here. A run from the start with the shipped programs takes 30 h (Section 2).

## 8. Statement numbers

This file cites the draft of the paper of 16 November 2026. The program comments and the records call the paper
`bmm.pdf` and cite an earlier numbering (and, for the exponents of the Gram determinants, a version of 3 November);
in particular their "Table 2" (the Gram determinants) is not the Table 2 of the paper (the levels of the towers). The
statements they cite are:

| in the records | statement | in the paper |
|---|---|---|
| §3.3 | the setRow procedure | §4.3 |
| Lemma 2.6 | Modular test 1 | Lemma 3.11 |
| Proposition 3.8 | a closed coset table: BFS_o spans, hence is a basis | Proposition 2.4, §4.3 |
| Theorem 3.11 | BFS_o is a basis | Theorem 4.10 |
| Proposition 4.11 | the symmetry criterion | Proposition 5.7 |
| Lemma 4.13 | the pairing lemma | Lemma 5.9 |
| Lemma 4.16 | the blocks F_r of Gram(B, B^-1) | Lemma 5.10 |
| Proposition 4.17, Theorem 4.18 | the conjecture for G4–G29 | Proposition 5.11, Theorem 5.12 |
| Corollary 5.10 (3 November) | the exponents of det Gram(τ_B) | not in the paper |
| §5.1, Lemma 5.1 | E_X and its bimodule property | §6.1, Lemma 6.1 |
| Lemma 5.2 | the factorisation of the Gram matrix | Lemma 6.2 |
| Proposition 5.3 | the parabolic criterion | Proposition 6.3 |
| Proposition 5.3 (3), via (2.4) | Condition (3) at the top of a tower | Lemma 6.9, via (2.4) |
| Proposition 5.4 | M(X, rev X), its blocks eliminated | Proposition 6.4 |
| Theorem 5.6 | the conjecture for G31–G34 | Theorem 6.11 |
| Figure 2 | the breadth-first candidates | Figure 2 |
| Table 2 | the Gram determinants | not in the paper |
| Sections 4 and 5 (in the headings) | G4–G29; G31–G34 | Sections 5 and 6 |

## 9. Files

    README.md           this file
    run.sh, run_all.sh  launchers
    Project.toml, Manifest.toml   the Julia environment: Chevie 0.1.11 and its dependencies, as used for the records
    programs/           bfs_basis, zbasis_modular, bmm_proof, trace_values, bfs_orders (.jl): one program per step,
                        for every group
    lib/                hecke.jl (coset tables, vector enumeration; loads the rest), trace.jl (can_trace, load_trace),
                        tests.jl (the tests of §5), spec.jl (group files), lambda.jl (H(U) ⊗ R'), poly.jl (R', lift_to_R),
                        modp.jl, determinants.jl (Bareiss), report.jl (records), cantrace.jl (can_trace, engine tower)
    lib/tower/          the engine of G31–G34: driver.jl (the steps), twostep.jl (E, t, the tests and the pairings),
                        setrow.jl (the setRow procedure over H(P), its programs and their execution), coset.jl (tables
                        over H(P)), alg.jl (H(P) as a flat algebra), ring.jl (exact packed polynomials, the modular point)
    G4 ... G34/         group file, basis, coset table, records 1-5 (G31–G33: 1-4; G34: 1, 3, 4), and the files named
                        in Section 4
