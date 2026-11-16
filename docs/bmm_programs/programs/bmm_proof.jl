#############################################################################
##
##  bmm_proof.jl — the exact proof of Proposition 4.17 (B is a z^k-basis) and
##                 Theorem 4.18 of bmm.pdf for one group: τ_B satisfies the
##                 BMM symmetrising trace conjecture
##
##  Everything is exact, over R' = R/(invertible parameters - 1): packed
##  polynomials with overflow-checked Int64 coefficients, Int128 if the group
##  file says  coefficients = "Int128"  (lib/poly.jl).  The
##  tested identities are images of identities between homogeneous elements
##  of R of the same degree (the homogeneity argument of bmm.pdf of 3 Nov,
##  Lemmas 5.6, 5.7), and R_D -> R' is injective for every degree D
##  (lib/poly.jl, lift_to_R), so each holds in R.
##
##  The stages of the record and the statements they prove:
##    Coset table of A     cosettableNN.txt is executed: every setRow
##                         compiles, so A is a basis (Proposition 3.8, the
##                         spanning criterion; Theorem 3.11, BFS_o is a
##                         basis, for the order of the group file);
##    Relations            the defining relations of H tested on the table
##                         (a check of the implementation, not needed for
##                         the theorem);
##    Linear form t        t = can_trace (E_j of bmm.pdf §4.3), defined through the basis A: it is
##                         symmetric (the criterion of Proposition 4.11 on A)
##                         and t(b) = δ_{b,1} on B (Proposition 4.17,
##                         Theorem 4.18);
##    Gram_t(B, B^-1)      its blocks F_r, r > 0, vanish (Lemma 4.16);
##    Block F_0, det F_0   det F_0 = ±1 (Proposition 4.17), so the Pairing
##                         Lemma 4.13 applies: B is a basis and t = τ_B is a
##                         symmetrising trace;
##    Condition (3)        t(b^-1 π) = 0 for b ≠ 1, t(π) = 1 (Theorem 4.18,
##                         in the form (2.4));
##    Result               det Gram(τ_B): the exponents by the homogeneity
##                         argument of bmm.pdf of 3 Nov (Lemma 5.9 and
##                         Corollary 5.10), the sign at the group-algebra
##                         point (Table 2).
##
##  usage:  julia programs/bmm_proof.jl GNN        (record: GNN/3_bmm_proof.txt)
##
#############################################################################

using Chevie
include("../lib/report.jl")
include("../lib/spec.jl")
const SPEC = read_spec(ARGS[1])                        # the group file
if SPEC.engine != "cyclic"                             # G31 .. G34: the driver of the engine writes the record
    include("../lib/$(SPEC.engine)/driver.jl")
    run_step(SPEC, :proof)
    exit()
end
include("../lib/hecke.jl")
include("../lib/determinants.jl")
const KP = PP                                    # the coefficients of the table: packed, checked polynomials

pretty(p::PP) = pretty(mvp(p))                   # a polynomial of R' as text
# x = ±1, for a packed polynomial or a Chevie Mvp
isunit(x::PP) = length(x.t) == 1 && x.t[1][1] == 0 && abs(x.t[1][2]) == 1
function isunit(x)
    length(x.d) == 1 || return false
    mon, c = first(pairs(x.d))
    isempty(mon.d) && abs(Int(c)) == 1
end

# the block factors of F_r, and the table of trace values of the words of X against factors, with progress lines
factors_of(T, X, r) = block_factors(T, X, r; progress = progress_printer("functionals of level $r", length(X)))
table_of(T, X, factors, what; start = basic_vec(T.H, 1)) =
    trace_table(T, X, factors; start = start, progress = progress_printer(what, length(X)))

# det F_0 = ±1, by Bareiss elimination on the strongly connected blocks of its support.  Returns (ok, text).
function det_F0(F0)
    comps = strongly_connected_components(F0); big = filter(c -> length(c) > 1, comps); nsing = count(c -> length(c) == 1, comps)
    d = one(RB)
    for c in comps; length(c) == 1 && (d *= mvp(F0[c[1], c[1]], BigInt)); end
    for c in big
        d *= det_bareiss(mvp.(F0[c, c], BigInt); verbose = length(c) >= 200)
    end
    blocks = vcat(string.(sort(length.(big), rev = true)), nsing > 0 ? ["1 (x $nsing)"] : String[])
    isunit(d), "det F_0 = $(pretty(d)); diagonal blocks " * join(blocks, ", ")
end

function main()
    S = SPEC; record(S, "3_bmm_proof.txt")
    X = read_basis(S); nUX = length(X) * paradeg(S); d = S.zlevels; E = paradeg(S); n = ngens(S); nX = length(X)
    N = ncosets(S); invs = invertibles(S); k = S.zstep; j0 = S.split; Z = zletter(S)

    header(S, "exact proof of Proposition 4.17 and Theorem 4.18 of bmm.pdf", "bmm_proof.jl")
    say("A = BFS_$(ordername(S)) ($(S.table)); " * basisline(S, nX))
    say("computed over R' = Z[$(join(others(S), ", "))], $(join(invs, " = ")) = 1" *
        (PCOEFF == Int64 ? "" : "; checked $PCOEFF coefficients (the group file)"))

    # ---- the coset table of A, and the relations of H on it
    stage("Coset table of A (Section 3.3, Proposition 3.8)")
    H = HeckeCRG(S, exact_parameters(S))
    nlines = count(l -> startswith(l, "setRow"), eachline(joinpath(S.dir, S.table)))
    nset, edges = run_program(H, joinpath(S.dir, S.table); progress = progress_printer("setRow's executed", nlines))
    testing("all $nset setRow's compile", true; note = "$(2 * (n + 1) * N) rows, $(nonzeros(H)) nonzero entries")
    stage("Relations of H on the table")
    test_relations(H; progress = progress_printer("rows tested", N))

    # ---- the linear form t = can_trace
    isempty(S.trace) && error("no trace in the group file (programs/zbasis_modular.jl proposes one)")
    J, i, m = parse_trace(S.trace)
    stage("Linear form t (can_trace): symmetry (Proposition 4.11) and values on B")
    say("t(h) = [$(aname(S, i, m))]" * (J == 0 ? " h" : " ($(Tword(S, fill(-Z, k * J))) h)") * (S.trace == "0,1,0" ? " = τ_A(h)" : "") *
        ", [a] = coefficient of a in A")
    T = MakeTrace(H)

    # Proposition 4.11 on the basis A
    test_symmetry(T, edges)
    # the values t(b), b in B
    V = table_of(T, X, [shifted(f) for f in T.φ], "rows e_1 ρ(T_x)")
    w4 = wrong_basis_values(V, KP); V = nothing
    testing("t(b) = δ_(b,1) for all b in B", w4 == 0; note = w4 == 0 ? "" : "$w4 wrong values")

    # ---- the blocks of Gram_t(B, B^-1)
    stage("Gram_t(B, B⁻¹): blocks F_r = ( t(T_z^$(k == 1 ? "r" : "($(k)r)") b b'⁻¹) ), b, b' in UX, r > 0 (Lemma 4.16)")
    factors = Dict{Int,Any}()
    for r in sort(unique(vcat(1:d-1, [j0]))); factors[r] = factors_of(T, X, r); end
    if d > 1
        V = table_of(T, X, reduce(vcat, [factors[r] for r in 1:d-1]), "rows for F_1, ..., F_$(d-1)")
        for r in 1:d-1
            nz = sum(count(!iszero, v[(r-1)*nX+1:r*nX, :]) for v in values(V))
            testing("F_$r = 0", nz == 0; note = nz == 0 ? "" : "$nz nonzero values")
        end
        V = nothing
    end
    # F_0, computed as t(z^(-k j0) b · b'^-1 z^(k j0))
    stage("Block F_0")
    v = j0 == 0 ? basic_vec(H, 1) : vec_under_word(H, basic_vec(H, 1), fill(-Z, k * j0))
    V = table_of(T, X, factors[j0], "rows for F_0"; start = v)
    F0 = FView(block_array(V, nX, E, KP), copy(LAMRED[]::Vector{KP}))
    V = nothing; factors = nothing
    terms = 0; maxc = 0; nz = 0
    for q in 1:nUX, pp in 1:nUX
        x = F0[pp, q]; iszero(x) && continue
        nz += 1; terms += nterms(x)
        for tm in x.t; maxc = max(maxc, abs(tm[2])); end
    end
    f0note = ""
    if terms <= 40000                             # small enough to be written out
        open(joinpath(S.dir, "3_F0.txt"), "w") do io
            println(io, "# H($(S.name)): the block F_0 = ( t(b b'^-1) ), b, b' in UX, of Gram_t(B, B^-1); $(join(invs, " = ")) = 1")
            println(io, "# rows and columns: u^m x in the order x_1, u x_1, ..., u^$(E-1) x_1, x_2, ... (x_i the words of $(S.basis)); written by programs/bmm_proof.jl")
            for i in 1:nUX; println(io, "[" * join([replace(pretty(F0[i, j]), " " => "") for j in 1:nUX], ",") * "],"); end
        end
        f0note = " (written to 3_F0.txt)"
    end
    say("F_0: $nUX x $nUX, $nz nonzero entries, $terms terms, largest coefficient $maxc$f0note")
    stage("det F_0 (Lemma 4.13)")
    ok6, det6 = det_F0(F0); F0 = nothing; GC.gc()
    testing("det F_0 = ±1", ok6; note = det6)

    # ---- condition (3) of the conjecture, in the form of Malle–Michel
    stage("Condition (3) of the conjecture")
    taupi, nz7 = condition3(T, X)
    testing("t(b⁻¹ T_π) = 0 for all b ≠ 1 in B", nz7 == 0; note = nz7 == 0 ? "" : "$nz7 nonzero values")
    testing("t(T_π) = 1", isone(taupi); note = isone(taupi) ? "" : "t(T_π) = $(pretty(taupi))")

    # ---- the determinant of Gram(τ_B): degree (the homogeneity argument of bmm.pdf of 3 Nov, Lemma 5.9) and sign
    # (group-algebra point)
    H = nothing; T = nothing
    D, α = det_exponents(S, X)
    I = count(w -> isone(w^2), elements(crg(S.chevie_group)))
    sgn = iseven((S.order - I) ÷ 2) ? "+" : "-"
    kc = [classorder(S, c) for c in 1:nclasses(S)]
    ours = "$sgn$(monomial_string(S, α))"
    ok = alltrue()
    stage("Result")
    if ok
        say("$(tests()); B is an R-basis and τ_B = t satisfies the BMM conjecture (Proposition 4.17, Theorem 4.18)")
        say("degree 2 Σ w(b) = ($(join(D, ", "))), exponents " * join(["$(D[c])/$(kc[c])" for c in eachindex(α)], ", ") *
            "; sign (−1)^(($(S.order) − $I)/2)")
        table2 = ""                               # the comparison with Table 2 of bmm.pdf (not for G4, G6)
        if !(S.name in ("G4", "G6") || isempty(S.bmm_table))
            same = replace(S.bmm_table, " " => "") == replace(ours, " " => "")
            table2 = "   (bmm.pdf, Table 2: " * (same ? "the same)" : "DIFFERENT, $(S.bmm_table))")
        end
        say("det Gram(τ_B) = $sgn $(monomial_string(S, α))" * table2)
    else
        say(tests())
    end
    total()
    finish(ok ? 0 : 1)
end

main()
