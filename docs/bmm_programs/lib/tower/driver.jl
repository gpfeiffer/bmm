#############################################################################
##
##  driver.jl — the engine "tower" (G31, G32, G33, G34): the steps of programs/*.jl
##
##  bmm.pdf, Section 5.  The group file (GNN/groupNN.toml) gives a tower of
##  parabolic subgroups P_0 < P_1 < ... < P_r = W, bottom first, P_0 = <u>
##  cyclic (its [[level]] tables; the top level is W).  For i ≥ 1 the coset
##  table of level i writes
##        H(P_i) = ⊕_n H(P_(i-1)) x_n,   x_1 = 1, x_2, ... the words of a
##                                        coset tree X of P_(i-1) \ P_i,
##  with coefficients in H(P_(i-1)), the algebra of the level below (a "flat
##  algebra", lib/tower/alg.jl, with its basis B_(P_(i-1)) and its trace, the
##  coefficient of 1).  E = E_X is the coefficient of x_1, t = τ_(P_(i-1)) ∘ E,
##  and B_(P_i) = B_(P_(i-1)) · X.  Every level is proved with the conditions
##  of Proposition 5.3 before it becomes the coefficient algebra of the next.
##  The stages of the records (the identities are explained in
##  lib/tower/twostep.jl):
##
##    Coset table of A             the table is complete (Proposition 3.8; Theorem 3.11): every table is filled
##                                 by the setRow procedure of bmm.pdf §3.3 (setrow.jl) from the relations of W
##                                 among the letters of P_i; at the top, the exact execution of the setRow
##                                 program cosettableNN.txt written by the step bfs
##    Relations of H on the table  the Hecke and braid relations hold on the table (a check of the code)
##    Bimodule map                 E(x_n T_s) = δ_(n,1) T_s for s in P_(i-1)               (Lemma 5.1)
##    Linear form t: symmetry      t(b T_s) = t(T_s b) for every generator s and every b in B = B_(P_(i-1)) · X
##                                 (Proposition 4.11, directly on the basis B)
##    Values on B                  t(b) = δ_(b,1) on B, so t = τ_B                (§5.1: τ_B = τ_P ∘ E_X)
##    Pairing                      M(Y_1, Y_2) = (E(u_i v_j)) over H(P_(i-1)) is triangular with units on
##                                 the diagonal, so det Gram(τ_B) is a unit                (Lemma 5.2; 4.16)
##    Condition (3)                t(b^-1 T_π) = 0 for b ≠ 1 in B, t(T_π) = 1  (Proposition 5.3 (3), via (2.4))
##    Result                       all tests true: τ_B satisfies the conjecture            (Theorem 5.6)
##
##  Exact means over R' = R/(r_0 - 1): Z[e1] (G31, G33, G34, T^2 = e1 T + 1)
##  or Z[c1, c2] (G32, T^3 = c2 T^2 + c1 T + 1).  Each tested identity is
##  between homogeneous elements of the same degree, so it holds over
##  R = Z[r_j][r_0^±1] (the homogeneity argument of bmm.pdf of 3 November,
##  Lemmas 5.6–5.9).  Modular means modulo p at a point of R'.
##
##  The fields of the group file read here (besides those of lib/spec.jl):
##    [[level]]  name, gens, over (the letters of the level below), order, bfs; pi (condition (3) with T_π)
##               or zeta (through ζ, ζ² = π); zword (a central z_P of the level: the units ± b z_P^j of the
##               pairing one level up); pairing (absent: M(X, rev X) is triangular with units on the diagonal;
##               "rev": its blocks eliminated with unit pivots over H(P_(i-1)), the test of the top of G33, used
##               by the level G33 of G34)
##    the top    bfs (or --order), seeds (Definition 5.5), zeta, pairing ("ztree": the sets
##               Y_1 = T_o'(P\W) with the letter z, o' = pairing_bfs, listed in the file pairing_words, and Y_2
##               their partners, G31; "rev": a z-basis; or a file: the second family of G32), family, garside
##               and garside_perm (Δ with T_Δ T_s = T_σ(s) T_Δ and T_Δ² = T_z), consequences (tested, never used
##               by the setRow procedure); proof_skip_top_relations (relations of braid that the step proof does
##               not test on the cosets of the top, G34; see proof_skip); setrow_z (false: the tables have no columns of z and z^-1); basis (the
##               words Y of B = Z^k · B_P · T_Y) and table (the setRow program of the top level)
##
##  The steps (run_step), each writing a record GNN/N_name.txt:
##    bfs      1_bfs_basis.txt       every table modulo p, by the setRow procedure; writes the setRow program
##                                   of the top level (cosettableNN.txt), the words of the basis file (basisNN.txt) and,
##                                   for pairing = "ztree", the words of Y_1 (pairing_words)
##    modular  2_zbasis_modular.txt  every test modulo p at the point, the top table executed from cosettableNN.txt
##    proof    3_bmm_proof.txt       every test, exact
##    traces   4_trace_values.txt    values of the canonical trace τ (can_trace), also load_trace("G31")
##  Options: --order=12345 (the ordering of the top tree; records and files get the suffix _12345),
##  --family=compz|revz|compDelta|revDelta (G32: the second family of the pairing, file family32_<family>.txt),
##  --p=15013, --point=11,13 (the prime and the point of the modular steps), --words="1,-2;z" (traces),
##  --symdepth=17 (the depth of the rows x_n x in the symmetry test; deeper words go through columns).
##
#############################################################################

using Chevie
isdefined(Main, :testing)   || include("../report.jl")      # the records: say, testing, stage
isdefined(Main, :GroupSpec) || include("../spec.jl")        # the group file
isdefined(Main, :CanTrace)  || include("../cantrace.jl")    # can_trace for G31, ..., G34
isdefined(Main, :Tower)     || include("twostep.jl")        # the engine: module Tower

# ==== the data of the group file and of the command line ====================================================

# the options of the command line; the defaults come from the group file
struct TowerOptions
    order::Vector{Int}       # --order: the ordering o of the top tree (default: the field bfs)
    family::String           # --family: the second family of the pairing (G32; default: the field family)
    p::Int                   # --p, --point: the prime and the point of the modular steps (r_1, ..., r_(k-1))
    point::Vector{Int}
    otag::String             # "_<order>" for an ordering other than the default: the files cosettable, basis
    tag::String              # otag and "_<family>" for another family: the records and the family file
    zcolumns::Bool           # the columns of z and z^-1 are part of the setRow tables (field setrow_z, default true)
end
# the options of this run (ARGS)
function tower_options(S::GroupSpec)
    o = argval("order", "")
    if isempty(o)
        order = S.bfs
    elseif occursin(",", o)
        order = parseword(o)
    else
        order = [parse(Int, c) for c in o]                          # --order=12345
    end
    fam0 = get(S.opts, "family", ""); fam = argval("family", fam0)
    pt = argval("point", "")
    point = isempty(pt) ? [11, 13, 17, 19][1:S.orders[1]-1] : parse.(Int, split(pt, ","))
    otag = order == S.bfs ? "" : "_" * join(order)
    TowerOptions(order, fam, parse(Int, argval("p", "15013")), point, otag, otag * (fam == fam0 ? "" : "_" * fam),
                 get(S.opts, "setrow_z", true))
end
const METHODNAME = "the setRow procedure (bmm.pdf §3.3)"        # how every table is filled (setrow.jl)
# a file name with a tag: cosettable32.txt -> cosettable32_2134.txt
tagged(file, tag) = isempty(tag) ? file : replace(file, r"\.txt$" => tag * ".txt")

# the ground ring: R' (exact) or F_p at the point (modular); the names of the parameters are those of the group file
function tower_ring(S::GroupSpec, opt::TowerOptions; exact::Bool)
    (nclasses(S) == 1 && allequal(S.orders)) || error("$(S.name): the engine tower needs one class of reflections")
    k = S.orders[1]; r = S.params[1]                                 # r = names of r_0, r_1, ..., r_(k-1)
    empty!(Tower.LETTERS); append!(Tower.LETTERS, S.letters)
    exact ? Tower.hecke_exact(k, Symbol.(r[2:end]), Symbol(r[1])) : Tower.hecke_shadow(k, opt.p, opt.point, r[2:end])
end

# a level of the tower: P_i = <gens> over P_(i-1), in the letters of the group file
struct TowerLevel
    index::Int                   # i: 0 at the bottom; the top is W
    name::String                 # the type of P_i: A2, G(4,2,3), ...
    order::Int                   # |P_i| (0: not given)
    gens::Vector{Int}
    bfs::Vector{Int}             # the ordering of its coset tree
    seeds::Vector{Vector{Int}}   # words through which the tree passes (Definition 5.5; G32)
    pi::Vector{Int}              # condition (3) tested directly with T_π, π this word, or
    zeta::Vector{Int}            #   through a central ζ with ζ² = π (the letter z written out)
    zetaname::String             #   ζ as written in the group file
    zword::Vector{Int}           # a central element z_P of P_i: the units ± b z_P^j of the pairing one level up
end
wordfield(d, key) = parseword(string(get(d, key, "")))              # the word of a key of a [[level]] (empty if absent)
# a word with the letter z (n + 1) replaced by the word of z
withz(S, w) = reduce(vcat, [abs(l) == zletter(S) ? (l > 0 ? S.zword : -reverse(S.zword)) : [l] for l in w]; init = Int[])
# a word as a power of its shortest period: (s1 s4)³, z²
function powerword(S, w)
    n = length(w)
    for p in 1:n-1
        (n % p == 0 && w == repeat(w[1:p], n ÷ p)) || continue
        return p == 1 ? wordstr(S, w) : "(" * wordstr(S, w[1:p]) * ")" * sup(n ÷ p)
    end
    wordstr(S, w)
end
# the levels of the group file, bottom first, then W; checked to form a tower
function tower_levels(S::GroupSpec, opt::TowerOptions)
    Ls = TowerLevel[]
    for (i, d) in enumerate(S.levels)
        gens = wordfield(d, "gens"); bfs = wordfield(d, "bfs"); ζ = wordfield(d, "zeta"); over = wordfield(d, "over")
        Set(over) == Set(i == 1 ? Int[] : Ls[i-1].gens) || error("$(S.name): level $(i - 1) must lie over level $(i - 2)")
        push!(Ls, TowerLevel(i - 1, d["name"], get(d, "order", 0), gens, isempty(bfs) ? gens : bfs, Vector{Int}[],
                             withz(S, wordfield(d, "pi")), withz(S, ζ), powerword(S, ζ), wordfield(d, "zword")))
    end
    ζ = parseword(get(S.opts, "zeta", ""))
    push!(Ls, TowerLevel(length(Ls), S.name, S.order, collect(1:ngens(S)), opt.order,
                         "--noseeds" in ARGS ? Vector{Int}[] : parseword.(get(S.opts, "seeds", String[])),
                         Int[], withz(S, ζ), powerword(S, ζ), S.zword))
    for i in 2:length(Ls)
        issubset(Ls[i-1].gens, Ls[i].gens) || error("$(S.name): level $(i - 1) does not contain level $(i - 2)")
        isempty(Ls[i].pi) == isempty(Ls[i].zeta) && error("$(S.name): level $(i - 1) needs pi or zeta (condition (3))")
    end
    isempty(ζ) || (all(==(zletter(S)), ζ) && 2 * length(ζ) == S.pipower) || error("$(S.name): zeta must be z^j with 2j = pipower")
    Ls
end
level_name(L::TowerLevel) = "H($(L.name))"

# a word in the letters of the group file as a word in the letters 1, 2, ... of the level (the positions in L.gens)
function local_letter(L::TowerLevel, l::Int)
    j = findfirst(==(abs(l)), L.gens)
    j === nothing && error("the letter $(abs(l)) is not a generator of $(L.name)")
    sign(l) * j
end
local_word(L::TowerLevel, w) = Int[local_letter(L, l) for l in w]
# the relations of a list (pairs of words of the group file) among the letters of the level, in its letters:
# each level uses the relations of W that involve only its own letters
level_relations(L::TowerLevel, rels) = [(local_word(L, l), local_word(L, r)) for (l, r) in rels if all(g -> abs(g) in L.gens, vcat(l, r))]
# the field consequences: relations that hold on the tables but are never used by the setRow procedure
consequences(S) = [Tuple(parseword.(split(c, "="))) for c in get(S.opts, "consequences", String[])]
# the field proof_skip_top_relations: relations of the field braid that the step proof does not test on the cosets of
# the top (G34, 14 Nov 2026: exactly they did not fit in memory).  Their lines of the stage "Relations of H on the
# table" read "not computed"; the plan keeps its pieces (a checkpoint stays valid).  These tests are a check of the code:
# B is a basis because the table closes (bmm.pdf §3, the span of B is a right ideal); the step bfs tests them modulo p.
proof_skip(S) = [Tuple(parseword.(split(c, "="))) for c in get(S.opts, "proof_skip_top_relations", String[])]
const PROOF_SKIP_WHY = "field proof_skip_top_relations of the group file: a check of the code, not needed for the proof " *
                       "(B is a basis because the table closes, bmm.pdf §3); tested modulo p by the step bfs, 1_bfs_basis.txt"

# W as a permutation group (Chevie's crg); the letter g is the generator chevie[g]
tower_group(S::GroupSpec) = Tower.Grp(S.name, gens(crg(S.chevie_group))[S.chevie])
# the coset tree X of P_(i-1) \ P_i (breadth first for the ordering of the level, through its seeds) and the empty
# table of H(P_i) over A = H(P_(i-1)) on it
function level_table(Ls, i, A, W; zword = Int[])
    L = Ls[i]; sub = local_word(L, Ls[i-1].gens); n = length(L.gens)
    C = Tower.Cosets(Tower.Grp(L.name, W.gens[L.gens]), sub)
    withz = any(l -> !(abs(l) in L.gens), L.bfs)            # the ordering contains the letter z (n + 1): a tree with z
    withz && isempty(zword) && error("$(L.name): a tree with the letter z needs the columns of z (setrow_z = true)")
    if isempty(zword)
        X = Tower.bfs_tree(C, local_word(L, L.bfs); seeds = [local_word(L, s) for s in L.seeds])
        Tower.Table(L.name, A, n, sub, X, Tower.coset_action(C, X; order = L.order); glob = L.gens)
    else                                            # the letter z (n + 1) has columns of its own (setrow_z)
        zp = Tower.product(W, zword); perms = vcat(W.gens[L.gens], [zp])
        o = [abs(l) in L.gens ? local_letter(L, l) : n + 1 for l in L.bfs]
        X = withz ? Tower.bfs_letters(C, o, perms) : Tower.bfs_tree(C, o; seeds = [local_word(L, s) for s in L.seeds])
        Tower.Table(L.name, A, n, sub, X, Tower.coset_action(C, X; perms = perms, order = L.order); zword = zword, glob = L.gens)
    end
end
# the table of the top level: with the columns of z unless the group file says setrow_z = false
top_table(S, Ls, A, W, opt) = level_table(Ls, length(Ls), A, W; zword = opt.zcolumns ? S.zword : Int[])
# the relators used at a level: the relations of W among its letters, and at the top with the letter z, z = zword
# and z s = s z
level_relators(T, rels) = Tower.sr_relators(T, rels)
# one sweep of the setRow procedure reported
function sweepline(pass, (found, ngen, ninv, nrel, op))
    say(@sprintf("  sweep %d: %d setRow's (gen %d, inv %d, rel %d), %d rows open  %s", pass, found, ngen, ninv, nrel, op, stamp()))
end
# the table of a level filled by the setRow procedure; returns (ok, the program lines, a note for the record)
function fill_table!(T, rels, opt; report = nothing)
    lines, ok, passes = Tower.sr_enumerate!(T, level_relators(T, rels); report = report)
    ok, lines, "$(length(passes)) sweeps, $(T.N - 1) tree edges, $(count(l -> startswith(l, "setRow"), lines)) setRow's"
end
# A = T_o(P<z^k> \ W), the breadth-first tree of the cosets of P<z^k>: the words of the z^k-basis Z^k · B_P · T_A
function zbasis_words(S, Ls, W, order)
    P = Ls[end-1].gens; zp = Tower.product(W, S.zword)^S.zstep        # z^k as a permutation
    Pz = Tower.closure(W, vcat(W.gens[P], [zp])); img = Tower.images(W)
    C = Tower.Cosets(W, P, Pz, h -> minimum(img(p * h) for p in Pz))
    Tower.bfs_tree(C, order), Pz, zp
end
# Y_1 = T_o'(P\W) for an ordering o' of the generators and the letter z (n + 1): the breadth-first tree of the cosets
# of P in W with z as one more letter (the pairing "ztree")
function ztree_words(S, Ls, W, o)
    zp = Tower.product(W, S.zword)
    Tower.bfs_letters(Tower.Cosets(W, Ls[end-1].gens), o, vcat(W.gens, [zp]))
end
# the words of a basis file (one per line, letters separated by commas, e the empty word, # a comment)
read_words(file) = [parseword(t) for t in (strip(split(l, "#")[1]) for l in eachline(file)) if !isempty(t)]
# a basis file: the comment lines, then the words
function write_words(file, words, comment)
    open(file, "w") do io
        for c in comment; println(io, "# ", c); end
        for w in words; println(io, isempty(w) ? "e" : join(w, ",")); end
    end
end
# the lines of a setRow program (lines that are not comments)
read_steps(file) = [l for l in eachline(file) if !startswith(l, "#") && !isempty(strip(l))]
letterlist(S, g) = join(S.letters[g], ", ")                          # the letters g as text: s1, s2, s4

# ==== the stages of one level ================================================================================

# the levels below the top name themselves in the title of each stage
where_(S, Ls, i; full = false) = i == length(Ls) ? "" :
    ", level $(Ls[i].index)" * (full ? ": $(level_name(Ls[i])) over $(level_name(Ls[i-1])), $(Ls[i].name) = <$(letterlist(S, Ls[i].gens))>" : "")

# the bottom: H(P_0) = H(<u>) with the basis 1, T_u, ..., T_u^(e-1); τ is the coefficient of 1.  The pairing
# lemma (Lemma 4.13) for H(P_0): det Gram(τ) is a unit, so τ is a symmetrising trace of H(P_0).
function prove_bottom(S, Ls, q)
    A = Tower.cyclic_alg(q); u = "T_" * S.letters[Ls[1].gens[1]]
    basis = join(vcat("1", ["$u$(sup(j))" for j in 1:q.k-1]), ", ")             # 1, T_u, T_u², ...
    stage("Pairing, level 0: $(level_name(Ls[1])) with the basis $basis (Lemma 4.13)")
    d = Tower.gram_det(A)
    testing("det Gram(τ) on the basis $basis is a unit", Tower.isunit(d); note = "det = $d")
    A
end

# Coset table of A, below the top: the table closes by setRow sweeps from the relations of W among the letters of
# P_i, so B_(P_(i-1)) · X spans H(P_i) and is a basis (Proposition 3.8)
function stage_level_table(S, Ls, i, T, rels, W, opt)
    L = Ls[i]
    stage("Coset table of A$(where_(S, Ls, i; full = true)) (Proposition 3.8)")
    L.order > 0 && testing("|$(L.name)| = $(L.order)", length(Tower.closure(W, W.gens[L.gens])) == L.order)
    ok, _, note = fill_table!(T, rels, opt)
    testing("the table of $(level_name(L)) over $(level_name(Ls[i-1])) closes by setRow sweeps (§3.3) from the relations of W among " *
            letterlist(S, L.gens), ok; note = "$(T.N) cosets; $note")
    Tower.statistics(T)
    T.N <= 12 && say("coset words x_n: " * join([Tower.wordstr(T, w) for w in T.words], ", "))
end

# Relations of H on the table: the Hecke relations, the relations of W among the letters of the level, and the
# consequences of the group file (a check of the code, not needed for the proof).  Below the top the level is then
# turned into the flat algebra H(P_i), the coefficients of the next level, which is tested on the same relations.
function stage_relations(S, Ls, i, T, rels, cons; flat = true)
    st = Dict{Symbol,Any}(:T => T)
    run_pieces(relation_pieces(S, Ls, i, rels, cons, T.nletters; flat = flat), st)
    flat ? st[:AL] : nothing
end
# the same in pieces (see "the plan and the checkpoints" below): the stage line, the lines of Tower.test_R one by
# one, the consequences, the flat algebra (st[:AL]); nl = the number of letters of the table (generators and z)
function relation_pieces(S, Ls, i, rels, cons, nl; flat = true, skip = Tuple{Vector{Int},Vector{Int}}[])
    L = Ls[i]; n = Tower.test_R_count(length(L.gens), nl, length(rels)); lv = piece_where(Ls, i)
    ps = Piece[("$lv, relations: the stage", function (st)
        stage("Relations of H on the table$(where_(S, Ls, i))")
        st[:T].nletters == nl || error("relation_pieces: the table has $(st[:T].nletters) letters, not $nl")
    end)]
    for j in 1:n
        r = j - 1 - (nl > length(L.gens) + 1 ? 1 : 0) - length(L.gens)     # the relation of the line j (Tower.test_R_piece)
        if 1 <= r <= length(rels) && rels[r] in skip
            push!(ps, ("$lv, relations: line $j of $n", st -> Tower.notcomputed(
                "$(Tower.wordstr(st[:T], rels[r][1])) = $(Tower.wordstr(st[:T], rels[r][2])) on all cosets", PROOF_SKIP_WHY)))
        else
            push!(ps, ("$lv, relations: line $j of $n", st -> Tower.test_R_piece(st[:T], rels, j)))
        end
    end
    for c in cons
        push!(ps, ("$lv, relations: a consequence", st ->
            testing("$(Tower.wordstr(st[:T], c[1])) = $(Tower.wordstr(st[:T], c[2])) on all cosets (a consequence, not used by the setRow procedure)",
                    Tower.test_relation(st[:T], c))))
    end
    flat && push!(ps, ("$lv, relations: the flat algebra", function (st)
        A = Tower.FlatAlg(st[:T], level_name(L)); st[:AL] = A
        testing("the flat algebra $(level_name(L)) of rank $(A.d) satisfies its relations", Tower.test_flat(A, vcat(rels, cons)))
    end, st -> (st[:AL] = Tower.FlatAlg(st[:T], level_name(L)))))
    ps
end

# the central element z at the top: T_z T_s = T_s T_z, or through a Garside element Δ (G32): T_Δ T_s = T_σ(s) T_Δ
# with σ an involution, and T_Δ² = T_z
function test_z_central(S, T)
    if haskey(S.opts, "garside")
        Δ = parseword(S.opts["garside"]); σ = Vector{Int}(S.opts["garside_perm"])
        Tower.test_garside(T, Δ, σ)
        testing("T_Δ² = T_z", Tower.coords(T, vcat(Δ, Δ)) == Tower.coords(T, S.zword))
    else
        Tower.test_central(T, S.zword, "z")
    end
end

# Bimodule map (Lemma 5.1): E(x_n T_s) = δ_(n,1) T_s for the generators s of P_(i-1), read off the table
function stage_bimodule(S, Ls, i, T)
    stage("Bimodule map$(where_(S, Ls, i)) (Lemma 5.1)")
    Tower.test_T1(T)
end

# Linear form t: symmetry (Proposition 4.11), directly on the basis B = B_P · X of the level: t(b T_s) = t(T_s b) for
# every generator s of the level and every b in B (lib/tower/twostep.jl, test_symmetry).  τ_P(h h') is computed
# through the Gram matrix of H(P) = H(P_(i-1)): by products below rank 2 (the cyclic bottom), otherwise through the
# table Tbelow of the level i-1 (Tower.gram_from_table!).
const SYM_DEPTH = parse(Int, argval("symdepth", "17"))        # the depth L of the rows x_n x (Tower.ECache)
function stage_symmetry(S, Ls, i, T, Tbelow)
    L = Ls[i]; top = i == length(Ls)
    stage("Linear form t: symmetry$(where_(S, Ls, i)) (Proposition 4.11)")
    say("t = τ_P ∘ E, P = $(Ls[i-1].name): the coefficient of 1 on the basis B = B_P · X of $(level_name(L)), $(T.A.d) · $(T.N) elements")
    function gram()                                    # the Gram matrix of H(P), when a test first needs it
        haskey(Tower.GRAM, T.A) && return
        if Tbelow === nothing
            Tower.gram_rows(T.A)
            say("the Gram matrix τ_P(b b') of $(level_name(Ls[i-1])), b, b' in B_P: by products")
        else
            nnz, nodes = Tower.gram_from_table!(Tbelow, T.A; progress = progress_printer("Gram matrix of $(level_name(Ls[i-1])), columns", T.A.d))
            say("the Gram matrix τ_P(b b') of $(level_name(Ls[i-1])), b, b' in B_P: through its table over $(level_name(Ls[i-2])) " *
                "($nodes suffix nodes), $nnz nonzero entries of $(T.A.d)²  $(stamp())")
        end
    end
    C = Tower.ECache{eltype(T.A.acc.buf)}(SYM_DEPTH)
    for s in 1:T.ngens; Tower.test_symmetry(T, s, C; gram = gram); end
    isempty(C.at) || say("E(x_n x) for x in X at the $(length(C.at)) cosets n reached: $(C.rowops) rows x_n x (|x| ≤ $(C.L)), " *
                         "$(length(C.tails)) columns M_u e_1 of the tails u; $(C.entries) nonzero values, $(C.terms) terms")
    if top && T.A.d > 10000                           # not needed by the later stages: memory back (G34)
        delete!(Tower.GRAM, T.A); delete!(Tower.GRAMC, T.A); C = nothing; GC.gc()
    end
end

# Values on B (§5.1 of bmm.pdf: τ_B = τ_P ∘ E_X).  For B = B_P · X this is the definition of t.  For the z-basis
# B = {T_z^(kj)} · B_P · T_A of G31: z^k has order d and P ∩ <z^k> = 1, A ⊂ X (the first words of X in their
# z^k-orbits), and E(T_z^(kj) T_a) = δ_(j,0) δ_(a,1).  Returns the words Y of B = Z^k · B_P · T_Y.
function stage_values(S, Ls, T, W, opt)
    stage("Values on B (§5.1: τ_B = τ_P ∘ E_X)")
    if S.zlevels == 1
        say("B = B_P · X is the basis of the table: t(b x_n) = τ_P(b E(x_n)) = τ_P(b) δ_(n,1)")
        return T.words
    end
    d = S.zlevels; zw = repeat(S.zword, S.zstep); file = tagged(S.basis, opt.otag)
    A, Pz, zp = zbasis_words(S, Ls, W, opt.order)
    read_words(joinpath(S.dir, file)) == A || error("$file is not the tree T_o(P<z^k>\\W), o = $(ordername(S, opt.order))")
    nP = length(Tower.closure(W, W.gens[Ls[end-1].gens]))
    testing("$(zk(S)) has order $d in W and P ∩ <$(zk(S))> = 1 (|P<$(zk(S))>| = $d |P|)", order(zp) == d && length(Pz) == d * nP)
    say("A = T_o(P<$(zk(S))>\\W) ($file): $(length(A)) words, of length at most $(maximum(length, A))")
    σ = [foldl((n, s) -> T.act[n, s], zw; init = n) for n in 1:T.N]           # the permutation of the cosets by z^k
    orbit(n) = (o = [n]; while σ[o[end]] != n; push!(o, σ[o[end]]); end; o)
    firsts = [n for n in 1:T.N if minimum(orbit(n)) == n]
    testing("A ⊂ X: the words of A are the first words of X in their $(zk(S))-orbits (so all blocks are computed along X)",
            Set(A) == Set(T.words[firsts]))
    Tower.test_values_translates(T, zw, [findfirst(==(a), T.words) for a in A], d)
    A
end

# Pairing (Lemma 5.2): a matrix M(Y_1, Y_2) = (E(u_i v_j)) over H(P_(i-1)) that is triangular with units on the
# diagonal is invertible, so det Gram(τ_B) is a unit (Proposition 5.3 (2)).  Below the top: Y_1 = X and Y_2 the
# reversed (order 2) or complementary (order 3) words.  At the top: pairing = "ztree" (G31): Y_1 = T_o'(P\W) with
# the letter z, Y_2 its partners rev(w) T_z^-i, M block triangular by the number of letters z with triangular
# diagonal blocks; pairing = "rev" with a z-basis, M(Z · A, rev(A) · Z^-1) = (F_(j-j')), the blocks of Lemma 4.16
# over H(P); or a file listing the second family (G32).
function stage_pairing(S, Ls, i, T, opt)
    top = i == length(Ls)
    zP = local_word(Ls[i-1], Ls[i-1].zword)                    # units ± b z_P^j of H(P_(i-1)) are recognised
    pairing = get(S.opts, "pairing", "inverse")
    if !top
        stage("Pairing$(where_(S, Ls, i)) (Lemma 5.2)")
        if get(S.levels[i], "pairing", "") == "rev"             # M(X, rev X), its blocks eliminated over H(P) (the G33 level of G34)
            Tower.test_T4_rev(T, zP)
        else
            Tower.test_T4_complementary(T)
        end
    elseif pairing == "ztree"
        o = parseword(S.opts["pairing_bfs"]); file = S.opts["pairing_words"]
        stage("Pairing (Lemma 5.2): M(Y_1, Y_2), Y_1 = T_o'(P\\W) with the letter z, o' = $(ordername(S, o)), Y_2 the partners")
        Y = read_words(joinpath(S.dir, file))
        testing("$file lists Y_1 = T_o'(P\\W), the breadth-first tree with the letter z (one word per coset, closed under prefixes)",
                Y == ztree_words(S, Ls, tower_group(S), o))
        Tower.test_T4_ztree(T, Y, S.zword, zP)
    elseif pairing == "rev" && S.zlevels > 1
        stage("Pairing (Lemma 5.2; Lemma 4.16 over H(P))")
        say("M(Z·A, rev(A)·Z⁻¹) = (F_(j-j')), F_r = (E(T_z^r x_a rev(x_b)))_(a,b): F_r = 0 for r > 0 and F_0 triangular with units on the diagonal")
        Tower.test_T4_translates(T, repeat(S.zword, S.zstep))
    elseif pairing == "natural"                                 # a tree X with the letter z: y = rev(w) T_z^-i for x = w z^i
        stage("Pairing (Lemma 5.2): the natural pairing M(X, Y), y_m = rev(w_m) T_z^-i_m for x_m = w_m z^i_m")
        Tower.test_T4_natural(T, zP)
    elseif pairing == "rev"                                     # G33, G34: M(X, rev X), its blocks eliminated over H(P)
        stage("Pairing (Lemma 5.2, Proposition 5.4): M(X, rev X) = (E(x_n rev(x_m))) over H(P)")
        Tower.test_T4_rev(T, zP)
    elseif endswith(pairing, ".txt")
        fam = opt.family; file = tagged(pairing, opt.tag)
        stage("Pairing (Lemma 5.2): the second family of $file")
        rows = [Tuple(parse.(Int, split(l))) for l in read_steps(joinpath(S.dir, file))]
        Δ, tname = endswith(fam, "Delta") ? (parseword(S.opts["garside"]), "Δ") : (S.zword, "z")
        rev = startswith(fam, "rev")
        say("row x_n, column $(rev ? "rev" : "comp")(x_m) T_$tname^k: $(rev ? "reversed" : "complementary") tree words times powers of $tname")
        if rev
            Tower.test_T4_family(T, rows, Δ, zP; tname = tname)
        else
            Tower.test_T4_family_comp(T, rows, Δ, zP; tname = tname)
        end
    else
        error("$(S.name): unknown pairing \"$pairing\" for the engine tower")
    end
end

# Condition (3) (Proposition 5.3 (3)): by [MalMi, Proposition 2.7] it is (2.4), t(b^-1 T_π) = 0 for b ≠ 1 in B and
# t(T_π) a unit.  Tested directly with T_π (small levels), or through a central ζ with ζ² = π (lib/tower/twostep.jl)
# the pairing in pieces: M(X, rev X) (Tower.test_T4_rev: the top of G33 and G34, and a level with pairing = "rev") as
# its stage line, its columns in NSLICE slices of the words (Tower.partner_columns!), the matrix; any other pairing
# in one piece (stage_pairing)
function is_rev_pairing(S, Ls, i)
    i == length(Ls) && return get(S.opts, "pairing", "inverse") == "rev" && S.zlevels == 1
    get(S.levels[i], "pairing", "") == "rev"
end
function pairing_pieces(S, Ls, i, opt)
    lv = piece_where(Ls, i)
    is_rev_pairing(S, Ls, i) || return Piece[("$lv, pairing", st -> stage_pairing(S, Ls, i, st[:T], opt))]
    title = i == length(Ls) ? "Pairing (Lemma 5.2, Proposition 5.4): M(X, rev X) = (E(x_n rev(x_m))) over H(P)" :
                              "Pairing$(where_(S, Ls, i)) (Lemma 5.2)"
    ps = Piece[("$lv, pairing: the stage", function (st)
        stage(title); T = st[:T]
        T.q.k == 2 || error("test_T4_rev: the reversed word represents the inverse only for reflections of order 2")
        st[:pw] = Tower.partner_order(Set(T.words)); st[:pc] = Dict{Vector{Int},Any}(Int[] => Tower.colunit(scalartype(T), T.N, 1))
    end)]
    for j in 1:NSLICE
        push!(ps, ("$lv, pairing: the columns, slice $j of $NSLICE", st -> Tower.partner_columns!(st[:pc], st[:T], slice(st[:pw], j))))
    end
    push!(ps, ("$lv, pairing: the matrix", function (st)
        Tower.test_T4_rev_tail(st[:T], local_word(Ls[i-1], Ls[i-1].zword), st[:pc]); delete!(st, :pc); delete!(st, :pw)
    end))
    ps
end

stage_condition3(S, Ls, i, T) = run_pieces(condition3_pieces(S, Ls, i), Dict{Symbol,Any}(:T => T))
# the same in pieces: the stage line and the centrality of T_π or ζ; the column ψ = M_π e_1 (or M_ζ e_1) in NSLICE
# slices of letters; then, directly: t(T_π), the walk of the tree from ψ in NSLICE slices, the identities; through ζ
# on one coset c (Tower.test_T3_zeta): the row of T_u and the column M_v e_c (ζ = u v) in slices, t(T_π), the walk from e_c in slices, the
# identities; through ζ on several cosets (Tower.test_T3_general): t(T_π), the walk from ψ in slices, the identities
function condition3_pieces(S, Ls, i)
    L = Ls[i]; lv = piece_where(Ls, i); top = i == length(Ls)
    title = "Condition (3)$(where_(S, Ls, i)) (Proposition 5.3 (3), via (2.4))"
    direct = !isempty(L.pi)
    w = direct ? local_word(L, L.pi) : local_word(L, L.zeta); ls = reverse(w)    # the letters from the right
    unit(T, n) = Tower.colunit(scalartype(T), T.N, n)
    ps = Piece[("$lv, condition (3): the stage", function (st)
        stage(title)
        if direct
            Tower.test_T3_direct_head(st[:T], w, powerword(S, L.pi))
        elseif top
            say("ζ = $(L.zetaname) is central (z is central, stage Relations) and ζ² = π")
        else
            Tower.test_central(st[:T], w, L.zetaname)
        end
        st[:ψ] = unit(st[:T], 1)
    end)]
    for j in 1:NSLICE
        push!(ps, ("$lv, condition (3): the column ψ, slice $j of $NSLICE", st -> (st[:ψ] = Tower.col_letters(st[:T], st[:ψ], slice(ls, j)))))
    end
    function walk_from(st, col)                          # the walk of the tree starts
        st[:walk] = Tower.colwalk_start(st[:T], col); st[:walk_t0] = elapsed()
    end
    walk_pieces = [("$lv, condition (3): the walk of the tree, slice $j of $NSLICE", function (st)
        T = st[:T]; prog = direct ? nothing : progress_printer("columns", T.N; t0 = time() - (elapsed() - st[:walk_t0]))
        Tower.colwalk!(T, st[:walk], j == NSLICE ? 0 : cld(T.N, NSLICE); prog = prog)
    end) for j in 1:NSLICE]
    if direct
        push!(ps, ("$lv, condition (3): t(T_π)", st -> (st[:tπ] = Tower.test_T3_direct_values(st[:T], st[:ψ]); walk_from(st, pop!(st, :ψ)))))
        append!(ps, walk_pieces)
        push!(ps, ("$lv, condition (3): the identities", function (st)
            Tower.test_T3_direct_tail(st[:T], st[:walk], st[:tπ]); foreach(k -> delete!(st, k), (:walk, :walk_t0, :tπ))
        end))
        return ps
    end
    label = L.zetaname
    push!(ps, ("$lv, condition (3): the support of ψ", function (st)
        T = st[:T]; ψ = st[:ψ]
        if length(Tower.support(ψ)) == 1                  # Tower.test_T3_zeta
            st[:c] = Tower.test_T3_zeta_head(T, label, ψ)
            st[:tzr] = Tower.erow(scalartype(T), 1); st[:tzc] = unit(T, st[:c])          # the row of 1, the column e_c
        else                                              # Tower.test_T3_general
            st[:c] = 0; st[:tπ] = Tower.test_T3_general_head(T, w, label, ψ); walk_from(st, ψ)
        end
    end))
    # (T_ζ)_c, the coefficient of x_c in T_ζ, for ζ = u v: (T_ζ)_c = Σ_n (T_u)_n (M_v e_c)_n, the row of T_u (1·T_u)
    # against the column M_v e_c (h -> (h T_v)_c).  At the top ζ = z^j: u = z^(j-1), v = z (G34: the row of T_z² and
    # the column M_z e_c, about 30 s modulo p; the whole column M_ζ e_c did not fit, the whole row of T_ζ grew to
    # 468 539 terms after 6 of the last 42 letters).  Below the top: u = 1, v = ζ.
    nv = top ? length(S.zword) : length(w)
    top && (length(w) % nv == 0 && all(k -> w[k] == S.zword[mod1(k, nv)], eachindex(w)) || error("$(S.name): ζ is not a power of z"))
    u = w[1:end-nv]; lsv = reverse(w[end-nv+1:end])
    for j in 1:NSLICE                                     # the row of T_u, the letters of u from the left
        push!(ps, ("$lv, condition (3): the row of T_u, slice $j of $NSLICE", st ->
            st[:c] > 0 && (st[:tzr] = Tower.row_word(st[:T], st[:tzr], slice(u, j)))))
    end
    for j in 1:NSLICE                                     # the column M_v e_c, the letters of v from the right
        push!(ps, ("$lv, condition (3): the column M_v e_c, slice $j of $NSLICE", st ->
            st[:c] > 0 && (st[:tzc] = Tower.col_letters(st[:T], st[:tzc], slice(lsv, j)))))
    end
    push!(ps, ("$lv, condition (3): t(T_π)", st -> if st[:c] > 0
        r = pop!(st, :tzr); col = pop!(st, :tzc); r === nothing && error("the row of T_u meets an open row")
        st[:tπ] = Tower.test_T3_zeta_values(st[:T], st[:ψ], st[:c], Tower.colval(st[:T], r, col)); walk_from(st, unit(st[:T], st[:c]))
    end))
    append!(ps, walk_pieces)
    push!(ps, ("$lv, condition (3): the identities", function (st)
        T = st[:T]
        st[:c] > 0 ? Tower.test_T3_zeta_tail(T, st[:ψ], st[:c], st[:tπ], st[:walk]) : Tower.test_T3_general_tail(T, st[:ψ], st[:tπ], st[:walk])
        foreach(k -> delete!(st, k), (:walk, :walk_t0, :tπ, :ψ, :c))
    end))
    ps
end

# ==== the levels =============================================================================================

# the tree X of the top level, described; the seeds and the basis file (B = B_P · X) checked against it
function describe_top_tree(S, Ls, T, opt)
    L = Ls[end]
    wrapped("X = T_o$(isempty(L.seeds) ? "" : "^σ")(P\\W), o = $(ordername(S, L.bfs)), P = $(Ls[end-1].name) = <$(letterlist(S, Ls[end-1].gens))>" *
        (isempty(L.seeds) ? "" : ", σ = {" * join([wordstr(S, s) for s in L.seeds], ", ") * "}") *
        ": $(T.N) words, closed under prefixes, one per coset; longest $(maximum(length, T.words))")
    isempty(L.seeds) || testing("the seeds are words of the tree (their prefixes lie in distinct cosets)", all(s -> s in T.words, L.seeds))
end

# Coset table of A at the top: the exact (or modular) execution of the setRow program cosettableNN.txt; every rel
# command is checked to use an identity read off a relator (Proposition 3.8, Theorem 3.11)
function stage_replayed_table(S, Ls, T, rels, opt)
    stage("Coset table of A (Proposition 3.8, Theorem 3.11)")
    describe_top_tree(S, Ls, T, opt)
    if S.zlevels == 1
        file = tagged(S.basis, opt.otag)
        read_words(joinpath(S.dir, file)) == T.words || error("$file is not the tree X of the group file")
        say("$file lists X (checked)")
    end
    file = tagged(S.table, opt.otag); steps = read_steps(joinpath(S.dir, file))
    nset = count(l -> startswith(l, "setRow"), steps)
    say("execution of the setRow program $file: $(count(l -> startswith(l, "makeEdge"), steps)) makeEdge's and $nset setRow's")
    bad = Tower.sr_check_program(steps, level_relators(T, rels))
    testing("every rel command of $file uses an identity σ = w read off a relator (z = zword, z central, the braid relations)",
            isempty(bad); note = isempty(bad) ? "" : "$(length(bad)) commands do not", )
    ok = true; why = ""
    try
        Tower.sr_replay!(T, steps; progress = progress_printer("setRow's executed", nset))
    catch e
        ok = false; why = sprint(showerror, e)
    end
    testing("all $nset setRow's compile, and every column of the table is complete", ok && Tower.sr_open(T) == 0;
            note = ok ? "$(Tower.sr_open(T)) rows open" : why)
    say(Tower.sr_statistics(T))
end

# ==== the plan and the checkpoints ==========================================================================
#
# The steps proof and modular run a fixed list of pieces (the plan): each stage of each level and of the top, the long
# stages cut into pieces (the relations line by line; the columns of the pairing M(X, rev X), of T_π or T_ζ, and the
# walk of the tree in condition (3), in NSLICE slices each).  The state passed from piece to piece is a dictionary st:
# :A (the algebra of the level below), :Tbelow (its table), :T (the table of the level), :AL (its flat algebra), :Y
# (the words of B), and the partial results of a cut stage.
#
# Checkpoints.  After a piece, if CHECKPOINT_SECONDS (environment; default 1800) have passed since the last
# checkpoint, the state is written to GNN/checkpoint/<record>.jls (Serialization; first to a file .part, then
# renamed): st, the caches of the engine (Gram matrices, powers of z_P, the identities not computed modulo p), the
# numbers of tests and of FALSE, the time and the peak memory so far, and the length of the record (flushed to disk).
# A step that finds a checkpoint resumes from it if the checkpoint was made by the same programs (every file .jl of
# lib/ and programs/), the same group file and data files of the group (its files .txt that are not records), the same
# command line and the same step: the record is cut back to its length at the checkpoint, a line
#     # <date>  resumed from the checkpoint written on <date> after: <piece>; ...
# is written, and the pieces after that one are run.  Otherwise the step starts afresh.  The checkpoint is deleted when
# the record is finished.  CHECKPOINT_STOP=k (environment, for tests of the code): exit (code 75) right after writing a
# checkpoint after the piece k.

using Serialization, SHA
const Piece = Tuple                                  # (label, run) or (label, run, rebuild): see the checkpoints
const NSLICE = 24                                       # the slices of a cut stage
const CHECKPOINT_SECONDS = parse(Float64, get(ENV, "CHECKPOINT_SECONDS", "1800"))
const CHECKPOINT_STOP = parse(Int, get(ENV, "CHECKPOINT_STOP", "0"))
const CHECKPOINT_FORMAT = 1
scalartype(::Tower.Table{S}) where {S} = S
slice(v, j) = v[div((j - 1) * length(v), NSLICE)+1:div(j * length(v), NSLICE)]      # the slice j of NSLICE of a list
piece_where(Ls, i) = i == length(Ls) ? "top" : "level $(Ls[i].index) ($(Ls[i].name))"
run_pieces(ps, st) = (for p in ps; p[2](st); end; st)
rebuild_of(p) = length(p) >= 3 ? p[3] : nothing

# the plan of the steps proof and modular: every test at every level, then at the top (each in a function of its
# own, so that the closures of a level keep the data of that level)
function tests_plan(S, Ls, W, opt; exact::Bool)
    P = Piece[]
    for i in 2:length(Ls)-1; level_plan!(P, S, Ls, i, W, opt); end
    top_plan!(P, S, Ls, W, opt; exact = exact)
    P
end
function level_plan!(P, S, Ls, i, W, opt)
    L = Ls[i]; rels = level_relations(L, S.braid); cons = level_relations(L, consequences(S)); lv = piece_where(Ls, i)
    push!(P, ("$lv, coset table", st -> (st[:T] = level_table(Ls, i, st[:A], W); stage_level_table(S, Ls, i, st[:T], rels, W, opt)),
              function (st)                                           # rebuilt: the table by the setRow procedure
                  st[:T] = level_table(Ls, i, st[:A], W)
                  fill_table!(st[:T], rels, opt)[1] || error("rebuilding $(level_name(L)): the table does not close")
              end))
    append!(P, relation_pieces(S, Ls, i, rels, cons, length(L.gens); flat = true))
    push!(P, ("$lv, bimodule map", st -> stage_bimodule(S, Ls, i, st[:T])))
    push!(P, ("$lv, symmetry", st -> stage_symmetry(S, Ls, i, st[:T], st[:Tbelow])))
    append!(P, pairing_pieces(S, Ls, i, opt))
    append!(P, condition3_pieces(S, Ls, i))
    done = st -> (st[:A] = pop!(st, :AL); st[:Tbelow] = pop!(st, :T))       # H(P_i), the coefficients of the next level
    push!(P, ("$lv: done", done, done))
end
function top_plan!(P, S, Ls, W, opt; exact::Bool)
    i = length(Ls); L = Ls[i]; rels = level_relations(L, S.braid); cons = level_relations(L, consequences(S))
    skip = level_relations(L, proof_skip(S))
    length(skip) == length(proof_skip(S)) && all(in(rels), skip) ||
        error("$(S.name): proof_skip_top_relations names a relation that is not in the field braid")
    exact || empty!(skip)                                                       # the step proof only
    push!(P, ("top, coset table", st -> (st[:T] = top_table(S, Ls, st[:A], W, opt); stage_replayed_table(S, Ls, st[:T], rels, opt)),
              function (st)                                           # rebuilt: the program of the table executed again
                  st[:T] = top_table(S, Ls, st[:A], W, opt)
                  Tower.sr_replay!(st[:T], read_steps(joinpath(S.dir, tagged(S.table, opt.otag))))
                  Tower.sr_open(st[:T]) == 0 || error("rebuilding the top table: rows open")
              end))
    append!(P, relation_pieces(S, Ls, i, rels, cons, length(L.gens) + (opt.zcolumns ? 1 : 0); flat = false, skip = skip))
    push!(P, ("top, z central", st -> test_z_central(S, st[:T])))
    push!(P, ("top, bimodule map", st -> stage_bimodule(S, Ls, i, st[:T])))
    push!(P, ("top, symmetry", st -> (stage_symmetry(S, Ls, i, st[:T], st[:Tbelow]); st[:Tbelow] = nothing), st -> (st[:Tbelow] = nothing)))
    push!(P, ("top, values on B", st -> (st[:Y] = stage_values(S, Ls, st[:T], W, opt)),
              st -> (st[:Y] = S.zlevels == 1 ? st[:T].words : zbasis_words(S, Ls, W, opt.order)[1])))
    append!(P, pairing_pieces(S, Ls, i, opt))
    append!(P, condition3_pieces(S, Ls, i))
end

checkpoint_file(S, recname) = joinpath(S.dir, "checkpoint", replace(recname, r"\.txt$" => ".jls"))
fsync_io(io) = ccall(:fsync, Cint, (Cint,), fd(io))
# what a checkpoint must match: the programs, the group file and data files of the group, the command line, the step
function checkpoint_key(S, recname)
    files = String[]
    for d in (joinpath(@__DIR__, ".."), joinpath(@__DIR__, "..", "..", "programs")), (root, _, fs) in walkdir(d), f in fs
        endswith(f, ".jl") && push!(files, joinpath(root, f))
    end
    for f in readdir(S.dir)
        ((startswith(f, "group") && endswith(f, ".toml")) || (endswith(f, ".txt") && !isdigit(f[1]))) && push!(files, joinpath(S.dir, f))
    end
    ctx = SHA.SHA256_CTX()
    for f in sort(map(normpath, files)); SHA.update!(ctx, Vector{UInt8}(basename(f))); SHA.update!(ctx, read(f)); end
    SHA.update!(ctx, Vector{UInt8}(join(vcat(PROGRAM_FILE, ARGS, recname, string(VERSION)), "\0")))
    bytes2hex(SHA.digest!(ctx))
end
const REBUILT = (:A, :AL, :T, :Tbelow, :Y)              # rebuilt on resuming, not written to the checkpoint
function checkpoint_write(S, recname, k, label, st, key)
    t = time(); path = checkpoint_file(S, recname); mkpath(dirname(path)); part = path * ".part"
    flush(RECORD[]); fsync_io(RECORD[])
    partial = Dict{Symbol,Any}(k => v for (k, v) in st if !(k in REBUILT))
    data = (format = CHECKPOINT_FORMAT, key = key, next = k + 1, after = label, date = Dates.format(now(), "yyyy-mm-dd HH:MM:SS"),
            partial = partial, notcomputed = Tower.NOTCOMPUTED, ntests = NTESTS[], nfalse = NFALSE[], elapsed = elapsed(),
            stage = STAGE_T[] > 0 ? time() - STAGE_T[] : -1.0, maxrss = max(Sys.maxrss(), RSS_BEFORE[]), record_bytes = position(RECORD[]))
    open(part, "w") do io; serialize(io, data); flush(io); fsync_io(io); end
    mv(part, path; force = true)
    println("checkpoint after piece $k ($label): $(round(filesize(path) / 2^20, digits = 1)) MB in $(hms(time() - t))  $(stamp())"); flush(stdout)
end
# the state at the checkpoint and the first piece to run, or nothing (the step starts afresh).  The tables and algebras
# of the pieces before the checkpoint are rebuilt (the pieces with a rebuild function: the coset tables by the setRow
# procedure or by the program of the table file, the flat algebras), silently: no line of the record, no test counted;
# the caches of the engine (Gram matrices, powers of z_P) are recomputed when needed
function checkpoint_resume(S, recname, plan, key, q)
    path = checkpoint_file(S, recname); rec = joinpath(S.dir, recname)
    isfile(path) || return nothing
    ck = try
        open(deserialize, path)
    catch e
        println("the checkpoint $path cannot be read ($(first(sprint(showerror, e), 300))): the step starts afresh"); return nothing
    end
    why = ck isa NamedTuple && get(ck, :format, 0) == CHECKPOINT_FORMAT ? "" : "of another format"
    isempty(why) && ck.key != key && (why = "made by other programs, data files or options")
    isempty(why) && !(2 <= ck.next <= length(plan)) && (why = "for another plan")
    isempty(why) && !(isfile(rec) && filesize(rec) >= ck.record_bytes) && (why = "for a longer record than $rec")
    isempty(why) || (println("the checkpoint $path is $why: the step starts afresh"); return nothing)
    t = time(); println("resuming from $path (after piece $(ck.next - 1): $(ck.after)); rebuilding the tables"); flush(stdout)
    st = Dict{Symbol,Any}(:A => Tower.cyclic_alg(q), :Tbelow => nothing)
    SILENT[] = true
    try
        for k in 1:ck.next-1
            r = rebuild_of(plan[k]); r === nothing || r(st)
        end
    finally
        SILENT[] = false
    end
    merge!(st, ck.partial)
    tr = time() - t; println("rebuilt in $(hms(tr))"); flush(stdout)
    io = open(rec, "r+"); truncate(io, ck.record_bytes); seekend(io); RECORD[] = io
    NTESTS[] = ck.ntests; NFALSE[] = ck.nfalse; T_BEFORE[] = ck.elapsed - (t - T0); RSS_BEFORE[] = UInt64(ck.maxrss)
    empty!(Tower.NOTCOMPUTED); append!(Tower.NOTCOMPUTED, ck.notcomputed)
    ck.stage >= 0 && (STAGE_T[] = time() - ck.stage)
    say("# $(Dates.format(now(), "yyyy-mm-dd HH:MM:SS"))  resumed from the checkpoint written on $(ck.date) after: $(ck.after); " *
        "a new process rebuilt the tables in $(hms(tr)) and continues (the times and the peak memory include the processes before)")
    st, ck.next
end

# ==== the steps ==============================================================================================

# the lines after the header: the bases, the files and the ring
function describe(S, Ls, opt; exact)
    P = Ls[end-1]; d = S.zlevels
    wrapped("A = B_P · X, B_P = the basis of $(level_name(P)) built level by level, P = $(P.name) = <$(letterlist(S, P.gens))> (" *
        tagged(S.table, opt.otag) * "); " * (d == 1 ? "B = A (X: $(tagged(S.basis, opt.otag)))" :
        "B = { T_$(zk(S))^j b T_a : j < $d, b in B_P, a in A }, A of $(tagged(S.basis, opt.otag))"))
    r = S.params[1]
    say(exact ? "computed over R' = Z[$(join(r[2:end], ", "))], $(r[1]) = 1" :
        "p = $(opt.p); $(join(r[2:end], ", ")) = $(join(opt.point, ", ")); $(r[1]) = 1")
    say("the coset tables are filled by $METHODNAME" * (opt.zcolumns ? ", with the columns of z and z^-1" : ", without the columns of z"))
end

# the presentation of the group file, checked in W: the orders of the generators, the braid relations, z central
function stage_presentation(S)
    stage("The presentation, in W")
    letters_in_W(S)
end

# the number of w in W with w² = 1 (the identity included), from the conjugacy classes: the elements of G34 cannot be listed
ninvolutions(W) = (ci = classinfo(W); sum(ci[:classes][i] for (i, w) in enumerate(classreps(W)) if isone(w^2)))
# det Gram(τ_B) = ± r_0^E: degree 2 Σ_(b in B) ℓ(b) (the homogeneity argument), the sign at the group-algebra point
function det_gram(S, BP, Y)
    d = S.zlevels; k = S.zstep; e = S.orders[1]
    LP = sum(length, BP.words); LY = sum(length, Y)
    L = d * length(Y) * LP + d * BP.d * LY + BP.d * length(Y) * k * length(S.zword) * (d * (d - 1) ÷ 2)
    I = ninvolutions(crg(S.chevie_group))
    2L % e == 0 || error("the degree 2 Σ ℓ(b) = $(2L) is not divisible by $e")
    2L, 2L ÷ e, iseven((S.order - I) ÷ 2) ? "+" : "-", I
end
# the stage Result: the tests counted and det Gram(τ_B); the end of the program
function tower_result(S, BP, Y; exact)
    D, E, sgn, I = det_gram(S, BP, Y); r0 = S.params[1][1]
    nc = length(Tower.NOTCOMPUTED)
    stage(exact ? "Result" : "Result (mod $(tower_options(S).p))")
    if alltrue()
        say(tests() * (nc == 0 ? "" : "; $nc $(nc == 1 ? "identity" : "identities") not computed " *
                       (exact ? "(the lines \"not computed\" above)" : "modulo p (tested in the exact run)")))
        exact && say("B is an R-basis of H($(S.name)) and τ_B = t satisfies the BMM conjecture (Proposition 5.3, Theorem 5.6)")
        wrapped("degree 2 Σ ℓ(b) = $D, exponent $D/$(S.orders[1]) (the homogeneity argument of bmm.pdf of 3 Nov, Corollary 5.10); " *
            "sign (−1)^(($(S.order) − $I)/2) at the group-algebra point")
        say((exact ? "" : "predicted: ") * "det Gram(τ_B) = $sgn $r0^$E")
    else
        say(tests())
    end
    total()
    finish(alltrue() ? 0 : 1)
end

# step proof (exact) and step modular: every test at every level, the pieces of the plan with checkpoints
function step_tests(S::GroupSpec; exact::Bool)
    opt = tower_options(S); recname = (exact ? "3_bmm_proof" : "2_zbasis_modular") * opt.tag * ".txt"
    q = tower_ring(S, opt; exact = exact); Ls = tower_levels(S, opt); W = tower_group(S)
    plan = tests_plan(S, Ls, W, opt; exact = exact); key = checkpoint_key(S, recname)
    resumed = checkpoint_resume(S, recname, plan, key, q)
    if resumed === nothing
        record(S, recname)
        header(S, exact ? "exact proof of Theorem 5.6 of bmm.pdf (Proposition 5.3 at every level)" :
                          "the tests of Proposition 5.3 modulo p at a point (bmm.pdf, Section 5)",
               exact ? "bmm_proof.jl" : "zbasis_modular.jl")
        describe(S, Ls, opt; exact = exact)
        stage_presentation(S)
        st = Dict{Symbol,Any}(:A => prove_bottom(S, Ls, q), :Tbelow => nothing); k0 = 1
    else
        st, k0 = resumed
    end
    last = time()
    for k in k0:length(plan)
        plan[k][2](st)
        if k < length(plan) && (time() - last >= CHECKPOINT_SECONDS || CHECKPOINT_STOP == k)
            checkpoint_write(S, recname, k, plan[k][1], st, key); last = time()
            CHECKPOINT_STOP == k && (println("CHECKPOINT_STOP = $k: stopped"); exit(75))
        end
    end
    atexit(() -> rm(checkpoint_file(S, recname); force = true))          # the record is finished by tower_result
    tower_result(S, st[:A], st[:Y]; exact = exact)
end

# step bfs: every table by the setRow procedure modulo p at the point; the setRow program of the top level goes to
# the table file, and the words Y of B = Z^k · B_P · T_Y to the basis file
function step_bfs(S::GroupSpec)
    opt = tower_options(S)
    record(S, "1_bfs_basis" * opt.otag * ".txt")
    header(S, "the tower of coset tables by the setRow procedure, mod p (bmm.pdf, Sections 3.3 and 5)", "bfs_basis.jl")
    q = tower_ring(S, opt; exact = false); Ls = tower_levels(S, opt); W = tower_group(S)
    describe(S, Ls, opt; exact = false)
    stage_presentation(S)
    A = Tower.cyclic_alg(q)
    for i in 2:length(Ls)-1
        L = Ls[i]; rels = level_relations(L, S.braid)
        T = level_table(Ls, i, A, W)
        stage_level_table(S, Ls, i, T, rels, W, opt)
        A = stage_relations(S, Ls, i, T, rels, level_relations(L, consequences(S)))
    end
    i = length(Ls); L = Ls[i]; rels = level_relations(L, S.braid)
    T = top_table(S, Ls, A, W, opt)
    stage("Coset table of A by $METHODNAME mod p (Proposition 3.8)")
    describe_top_tree(S, Ls, T, opt)
    say("columns: the generators" * (T.nletters > T.ngens ? ", z" : "") * " and their inverses ($(2 * T.nletters)); " *
                         "identities σ = w: $(sum(length, values(Tower.sr_relation_words(level_relators(T, rels)))))")
    ok, steps, note = fill_table!(T, rels, opt; report = sweepline)
    testing("the table closes by setRow sweeps from the relations of W", ok; note = note)
    say(Tower.sr_statistics(T))
    if !ok
        say("open rows per column: " * join(["$l => $o" for (l, o) in sort(collect(Tower.sr_open_by_column(T))) if o > 0], ", "))
        stage("Result (mod $(opt.p))"); say(tests()); total(); finish(2)
    end
    file = tagged(S.table, opt.otag)
    write_program(S, Ls, T, steps, file, opt, note)
    say("the setRow program written to $file ($note)")
    Y = S.zlevels == 1 ? T.words : zbasis_words(S, Ls, W, opt.order)[1]
    bfile = tagged(S.basis, opt.otag)
    write_words(joinpath(S.dir, bfile), Y, basis_comment(S, Ls, opt))
    say("$(length(Y)) words written to $bfile")
    if get(S.opts, "pairing", "") == "ztree"                          # Y_1 of the pairing (Proposition 5.3)
        o = parseword(S.opts["pairing_bfs"]); pfile = S.opts["pairing_words"]; Y1 = ztree_words(S, Ls, W, o)
        write_words(joinpath(S.dir, pfile), Y1,
            ["H($(S.name)): the words Y_1 of the pairing M(Y_1, Y_2) (bmm.pdf, Proposition 5.3): the breadth-first tree " *
             "T_o'(P\\W), P = $(Ls[end-1].name) = <$(letterlist(S, Ls[end-1].gens))>, o' = $(ordername(S, o)), with z as a letter " *
             "(written by programs/bfs_basis.jl $(S.name)); Y_2 = { rev(w) T_z^-i : y = w z^i in Y_1 }",
             "one word per line, letters separated by commas (1..$(ngens(S)) = $(letterlist(S, 1:ngens(S))), $(zletter(S)) = z), e = the empty word"])
        say("$(length(Y1)) words of Y_1 written to $pfile ($(count(w -> zletter(S) in w, Y1)) with z)")
    end
    stage_relations(S, Ls, i, T, rels, level_relations(L, consequences(S)); flat = false)
    stage("Result (mod $(opt.p))")
    say(tests() * "; written $file (replayed exactly by bmm_proof.jl) and $bfile" *
        (get(S.opts, "pairing", "") == "ztree" ? ", $(S.opts["pairing_words"])" : ""))
    total()
    finish(alltrue() ? 0 : 1)
end
# the setRow program of the top table: the format of the engine cyclic (lib/hecke.jl, bmm.pdf Remark 3.10), after
# a header
function write_program(S, Ls, T, lines, file, opt, note)
    P = Ls[end-1]; L = Ls[end]; r = S.params[1]
    open(joinpath(S.dir, file), "w") do io
        println(io, "# The coset table of the basis A = B_P · T_X of H($(S.name)), P = $(P.name) = <$(letterlist(S, P.gens))>: the setRow program " *
                    "(written by programs/bfs_basis.jl)")
        println(io, "# $(T.N) cosets P x_n, X = T_o$(isempty(L.seeds) ? "" : "^σ")(P\\W), o = ($(join(L.bfs, ","))), z = letter $(zletter(S))" *
                    (T.nletters > T.ngens ? " (its columns are part of the table)" : " (no columns of z)"))
        println(io, "# complete: true; $note (found modulo p = $(opt.p) at $(join(r[2:end], ", ")) = $(join(opt.point, ", ")); " *
                    "executed exactly by programs/bmm_proof.jl $(S.name))")
        println(io, "# makeEdge(n, m, g): x_m = x_n g, so x_n T_g = x_m and x_m T_g^-1 = x_n;  setRow(n, g, 0, gen|inv): row (n, g) from the Hecke relation of |g|;")
        println(io, "# setRow(n, g, [w], rel): row (n, g) = x_n T_w for the braid-group identity g = w (a rotation of a relator);")
        println(io, "# the rows x_1 T_s^±1 = T_s^±1 x_1 (s in P) are set at the construction of the table.  Coefficients are in H(P), on the left.")
        for l in lines; println(io, l); end
    end
end
# the comment lines of the basis file
function basis_comment(S, Ls, opt)
    P = Ls[end-1]; Pname = "P = $(P.name) = <$(letterlist(S, P.gens))>"
    o = "o = $(ordername(S, opt.order)) (written by programs/bfs_basis.jl $(S.name))"
    if S.zlevels == 1
        what = "the words X of the basis B = B_P · T_X, $Pname: the tree T_o$(isempty(Ls[end].seeds) ? "" : "^σ")(P\\W), $o"
    else
        what = "the words A of the $(basisname(S)) B = {T_$(zk(S))^j} · B_P · T_A (j < $(S.zlevels)), $Pname: " *
               "the tree T_o(P<$(zk(S))>\\W), $o"
    end
    ["H($(S.name)): " * what,
     "one word per line, letters separated by commas (1..$(ngens(S)) = $(letterlist(S, 1:ngens(S)))), e = the empty word"]
end

# the canonical trace: the tower built exactly (the levels by setRow sweeps, the top by the program of the table file),
# τ(T_w) = τ_P(E(T_w)), the coefficient of 1 on B (B is quasi-symmetric: the record 3_bmm_proof.txt).  Returns a
# CanTrace (lib/cantrace.jl), so that can_trace(T, w) gives τ(T_w) in R(W); load_trace("G31") calls this.
function build_trace(S::GroupSpec; verbose::Bool = false)
    opt = tower_options(S); q = tower_ring(S, opt; exact = true); Ls = tower_levels(S, opt); W = tower_group(S)
    A = Tower.cyclic_alg(q)
    for i in 2:length(Ls)-1
        T = level_table(Ls, i, A, W)
        fill_table!(T, level_relations(Ls[i], S.braid), opt)[1] || error("the table of $(level_name(Ls[i])) does not close")
        A = Tower.FlatAlg(T, level_name(Ls[i]))
        verbose && say("$(level_name(Ls[i])) = ⊕ $(level_name(Ls[i-1])) x_n: $(T.N) cosets, the table closes by $METHODNAME; rank $(A.d)")
    end
    T = top_table(S, Ls, A, W, opt); file = tagged(S.table, opt.otag); steps = read_steps(joinpath(S.dir, file))
    Tower.sr_replay!(T, steps); Tower.sr_open(T) == 0 || error("the program $file does not complete the table")
    if verbose
        say("H($(S.name)) = ⊕ H(P) x_n: $(T.N) cosets, the table completed by the exact execution of the $(length(steps)) lines of $file  $(stamp())")
        testing("T_z is central: T_z T_s = T_s T_z for s = $(letterlist(S, 1:ngens(S)))",
                all(s -> Tower.coords(T, vcat(S.zword, s)) == Tower.coords(T, vcat(s, S.zword)), 1:ngens(S)))
    end
    coef1(w) = Tower.tau(A, Tower.rcoef(Tower.coords(T, w), 1))       # τ_P(E(T_w)): the coefficient of 1
    CanTrace(S.name, ngens(S), S.orders[1], S.zword, S.orders[1] == 2 ? :e : :c, coef1)
end

# τ(T_w) in R(W) from its value in R' (a polynomial of the engine; lib/cantrace.jl reads the packing of
# lib/poly.jl): R(W) is graded with deg r_j = k - j, τ(T_w) is homogeneous of degree ℓ(w) (the homogeneity argument
# of bmm.pdf of 3 Nov, Lemmas 5.6, 5.7), so the term Π r_j^(a_j) of the value is the image of Π r_j^(a_j) r_0^m,
# k m = ℓ(w) - Σ_j (k - j) a_j
function lift_to_R(T::CanTrace, p::Tower.Poly, D::Int)
    k = T.k; r0 = Mvp(Tower.R0NAME[]); out = zero(r0)
    for (key, c) in p.t
        a = Tower.exponents(key); deg = sum((k - j) * a[j] for j in eachindex(a); init = 0)
        m, rest = fldmod(D - deg, k)
        rest == 0 || error("lift_to_R: a term of degree $deg in a value of degree $D")
        out += c * prod((Mvp(Tower.PVARS[j])^a[j] for j in eachindex(a)); init = one(r0)) * r0^m
    end
    out
end

# step traces: τ(T_w) for the words of the command line (--words="1,-2;2,2,1;z"), or for a default list, which
# is then written to the record
function step_traces(S::GroupSpec)
    n = ngens(S); ws = argval("words", "")
    tparse(x) = [l == "z" ? n + 1 : l == "-z" ? -(n + 1) : parse(Int, l) for l in split(strip(x), ",")]
    words = isempty(ws) ? vcat(default_words(n, S.orders[1]), [[1, 2, -1]]) : [tparse(x) for x in split(ws, ";")]
    isempty(ws) && record(S, "4_trace_values.txt")
    header(S, "values of the canonical trace τ (can_trace)", "trace_values.jl")
    stage("Coset table of A")
    T = build_trace(S; verbose = true)
    stage("Values of τ")
    r = S.params[1]
    say("exact values in R = Z[$(join(r[2:end], ", "))][$(r[1])^±1] (computed with $(r[1]) = 1, lifted by degree)")
    for w in words
        wrapped("τ($(replace(Tword(S, w), " " => "~"))) = " * pretty(can_trace(T, w)))
    end
    total()
    finish(alltrue() ? 0 : 1)
end

# ==== the entry points ========================================================================================

# programs/<step>.jl GNN hands a group of the engine tower to run_step
function run_step(S::GroupSpec, step::Symbol)
    step == :bfs     && step_bfs(S)
    step == :modular && step_tests(S; exact = false)
    step == :proof   && step_tests(S; exact = true)
    step == :traces  && step_traces(S)
    step == :orders  && (say("the step orders is not available for the engine tower ($(S.name))"); exit(3))
    error("the engine tower has no step $step")
end
