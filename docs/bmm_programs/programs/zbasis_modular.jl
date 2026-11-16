#############################################################################
##
##  zbasis_modular.jl — the modular test of a z^k-basis candidate B
##                      (bmm.pdf, §4, Lemma 2.6, Modular test 1)
##
##  Everything is computed in the specialised algebra H_θ, θ : R -> F_p
##  (invertible parameters 1, the others the values of --point), with the
##  coset table of the BFS basis A:
##    * C = CBM^θ(A, B), the coordinates of the elements of B in the basis A;
##      det C = ±1 is the necessary condition of Lemma 2.6;
##    * φ, the solution of C φ = e_1: the coefficient-of-one form τ_B in
##      A-coordinates, and the level J at which z^(kJ) moves it to a single
##      coordinate — the `trace` of the group file, from which can_trace
##      starts;
##    * the assertions of Proposition 4.17 (B is a z^k-basis) and Theorem 4.18
##      (τ_B satisfies the conjecture) at the point: τ_B symmetric, the
##      blocks F_r of Gram(B, B^-1), det F_0, condition (3);
##    * for |W| <= DENSE_MAX = 2500: the Gram matrices Gram(B, B) and
##      Gram(B, B^-1) themselves, their determinants and the sign.
##  A candidate with det C ≠ ±1 is not a basis (a proof); the other outputs
##  are evidence at one point, the proof being programs/bmm_proof.jl.
##
##  usage:  julia programs/zbasis_modular.jl GNN [--p=15013] [--point=v1,v2,...]        (record: GNN/2_zbasis_modular.txt)
##  --point lists the non-invertible parameters class by class (default: 11, 13, 17, 19, ... in order).
##
#############################################################################

include("../lib/report.jl")
include("../lib/spec.jl")
const SPEC = read_spec(ARGS[1])                        # the group file
if SPEC.engine != "cyclic"                             # G31 .. G34: the driver of the engine writes the record
    include("../lib/$(SPEC.engine)/driver.jl")
    run_step(SPEC, :modular)
    exit()
end
include("../lib/hecke.jl")

# a functional on Λ^N as a dense vector (coset j, u^n) <-> (j-1) e + n, and back
function functional_to_vector(f::Functional{E,Fp}, N) where E
    o = zeros(Float64, N * E)
    for (j, t) in f, n in 1:E; o[(j-1)*E + n] = t[n].v; end
    o
end
vector_to_functional(x::Vector{Int}, E) = Functional{E,Fp}(Int32(j) => ntuple(n -> Fp(x[(j-1)*E + n]), E)
                                                           for j in 1:length(x)÷E if any(!iszero, x[(j-1)*E+1:j*E]))

function main()
    S = SPEC; record(S, "2_zbasis_modular.txt")
    p = parse(Int, argval("p", "15013")); PMOD[] = p
    p < 32768 || error("p must be < 2^15 (the determinants use Float64 arithmetic)")
    cp = modular_parameters(S, p, argval("point", ""))
    X = read_basis(S); UX = level0(S, X); nUX = length(UX); d = S.zlevels; E = paradeg(S); n = ngens(S)
    N = ncosets(S); NR = N * E; Z = zletter(S); nX = length(X); k = S.zstep
    wantgram = S.order <= DENSE_MAX                 # the full Gram matrices only for the smaller groups

    header(S, "the $(basisname(S)) B tested modulo p (bmm.pdf, Section 4)", "zbasis_modular.jl")
    say("A = BFS_$(ordername(S)) ($(S.table)); " * basisline(S, nX))
    say("p = $p; " * pointline(S, cp))

    stage("Coset table of A and CBM(A, B) (Lemma 2.6)")
    H = HeckeCRG(S, cp)
    nset, edges = run_program(H, joinpath(S.dir, S.table))
    labels, fails = check_relations(H)
    testing("the $nset setRow's of $(S.table) compile and the relations of H hold", all(==(0), fails)) || finish(1)

    # C = CBM^θ(A, B): row b = the coordinates e_1 ρ(b) of b in the basis A, level by level
    rows0 = coordinates(H, UX)
    A = zeros(Float64, NR, NR + 1); A[1, NR+1] = 1.0                  # [C | e_1]: the system C φ = e_1
    for (b, v) in enumerate(rows0)
        for j in 0:d-1
            putrow!(A, j * nUX + b, v)
            j < d - 1 && (v = vec_under_word(H, v, fill(Z, k)))
        end
    end
    Cfull = wantgram ? A[:, 1:NR] : nothing
    dC, phiflat = det_solve!(A); A = nothing; GC.gc()
    testing("det CBM(A, B) = ±1", abs(sym(dC)) == 1; note = "det = $(sym(dC))" * (abs(sym(dC)) == 1 ? "" : ": B is not a basis"))
    if phiflat === nothing
        stage("Result (mod $p)"); say(tests()); total(); finish(1)
    end

    # τ_B in A-coordinates: φ with C φ = e_1 (τ_B(b) = δ_{b,1}), and its translates φ_j : h ↦ τ_B(T_z^(kj) h)
    stage("τ_B in the basis A: φ_j(h) = τ_B(T_z^$(k == 1 ? "j" : "($(k)j)") h), [a] = coefficient of a in A")
    T = MakeTrace(H, 0, vector_to_functional(phiflat, E))
    # the trace: the first level whose functional is a single coordinate with value 1
    trace = nothing
    for j in 0:d-1
        nz = sort([(Int(c), m - 1, symm(tp[m])) for (c, tp) in T.φ[j+1] for m in 1:E if !iszero(tp[m])])
        terms = length(nz) > 6 ? "" : " = " * join([(v == 1 ? "" : "($v)") * "[" * aname(S, c, m) * "]" for (c, m, v) in nz], " + ")
        say("φ_$j: $(length(nz)) coordinate" * (length(nz) == 1 ? "" : "s") * terms)
        trace === nothing && length(nz) == 1 && nz[1][3] == 1 && (trace = "$j,$(nz[1][1]),$(nz[1][2])")
    end
    say(trace === nothing ? "trace: none (no level is a single coordinate)" : "trace = \"$trace\"")
    !isempty(S.trace) && testing("the trace \"$(S.trace)\" of the group file gives τ_B", MakeTrace(H).φ[1] == T.φ[1])
    # τ_B(u^m w_i) is the coordinate (i, m) of φ_0: is A itself quasi-symmetric?
    badA = count(!iszero(tp[m]) && !(c == 1 && m == 1) for (c, tp) in T.φ[1] for m in 1:E)
    say("τ_B(a) = δ_(a,1) on A: " * (badA == 0 ? "yes (τ_B = τ_A)" : "no ($badA of $(S.order - 1) values nonzero)"))

    stage("Proposition 4.17 and Theorem 4.18 at the point (t = can_trace)")
    test_symmetry(T, edges)
    w3 = wrong_basis_values(basis_values(T, X), Fp)
    testing("t(b) = δ_(b,1) for all b in B", w3 == 0; note = w3 == 0 ? "" : "$w3 wrong values")
    F0 = nothing
    for r in vcat(1:d-1, 0)
        P = block_array(trace_table(T, X, block_factors(T, X, r)), nX, E, Fp)
        if r == 0
            F0 = FView(P, copy(LAMRED[]::Vector{Fp}))
        else
            testing("F_$r = 0", all(iszero, P))
        end
    end
    dF = detmod([x.v for x in F0])
    testing("det F_0 = ±1", abs(sym(dF)) == 1; note = "det = $(sym(dF)); F_0 is $nUX x $nUX")
    taupi, nz3 = condition3(T, X)
    testing("t(b⁻¹ T_π) = 0 for all b ≠ 1 in B", nz3 == 0; note = nz3 == 0 ? "" : "$nz3 nonzero values")
    testing("t(T_π) = 1", isone(taupi))

    D, α = det_exponents(S, X); sgn = "±"
    if wantgram
        stage("Gram matrices at the point")
        words = [vcat(fill(S.parabolic, m), fill(Z, k * j), x) for j in 0:d-1 for x in X for m in 0:E-1]
        nB = length(words)
        KA = zeros(Float64, NR, nB); KE = zeros(Float64, NR, nB)
        fs = functional(T, words)                                   # the functionals h ↦ t(h b')
        for b in 1:nB; KA[:, b] = functional_to_vector(fs[b], N); end
        fs = functional(T, [-reverse(w) for w in words])            # the functionals h ↦ t(h b'^-1)
        for b in 1:nB; KE[:, b] = functional_to_vector(fs[b], N); end; fs = nothing
        G = mod.(Cfull * KA, Float64(p)); Ei = mod.(Cfull * KE, Float64(p))
        testing("Gram_t(B, B) is symmetric", G == permutedims(G))
        dG = detmod(G); dE = detmod(Ei)
        testing("det Gram_t(B, B⁻¹) = ±1", abs(sym(dE)) == 1; note = "det = $(sym(dE))")
        testing("det Gram_t(B, B) = ±1", abs(sym(dG)) == 1; note = "det = $(sym(dG))")
        abs(sym(dG)) == 1 && (sgn = sym(dG) == 1 ? "+" : "-")
    end
    stage("Result (mod $p)")
    say(tests())
    alltrue() && say("predicted: det Gram(τ_B) = $sgn $(monomial_string(S, α))")
    total()
    finish(alltrue() ? 0 : 1)
end

main()
