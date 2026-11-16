#############################################################################
##
##  bfs_orders.jl — the tree candidates BFS_o for the orders o of the three generating sets of Figure 2
##                  of bmm.pdf, §3.3 (Theorem 3.11, BFS_o is a basis;
##                  Conjecture 2.5, the lifting conjecture)
##
##  The families are the orders of (1) the generators S, (2) S ∪ {z}, and
##  (3) S ∪ {z} without one generator (when the tree still reaches every
##  coset).  For each o, modulo a prime at a point of R':
##    * do the sweeps of setRow's complete the coset table of BFS_o?  (then
##      BFS_o is a basis, as for the order of the group file)
##    * det CBM^θ(A, BFS_o), A the BFS basis of the group file: ±1 is
##      necessary for BFS_o to be a basis (Lemma 2.6, Modular test 1);
##      computed for |W| <= DENSE_MAX = 2500;
##    * is BFS_o a quasi-symmetric section (as in Conjecture 2.5):
##      τ(a) = δ_{a,1} for all a in BFS_o, with τ = can_trace?  A nonzero
##      value is a proof that it is not.
##
##  usage:  julia programs/bfs_orders.jl GNN [--p=15013] [--point=...]        (record: GNN/5_bfs_orders.txt)
##
#############################################################################

include("../lib/report.jl")
include("../lib/spec.jl")
const SPEC = read_spec(ARGS[1])                        # the group file
if SPEC.engine != "cyclic"                             # G31 .. G34: the driver of the engine writes the record
    include("../lib/$(SPEC.engine)/driver.jl")
    run_step(SPEC, :orders)
    exit()
end
include("../lib/hecke.jl")

# all orderings of v
permutations(v) = length(v) <= 1 ? [copy(v)] : [vcat([v[i]], q) for i in eachindex(v) for q in permutations(vcat(v[1:i-1], v[i+1:end]))]

function main()
    S = SPEC; record(S, "5_bfs_orders.txt")
    p = parse(Int, argval("p", "15013")); point = argval("point", "")
    p < 32768 || error("p must be < 2^15 (the determinants use Float64 arithmetic)")
    wantdet = S.order <= DENSE_MAX                     # the determinants only for the smaller groups
    n = ngens(S); Z = zletter(S); N = ncosets(S); E = paradeg(S); NR = N * E

    header(S, "the tree candidates BFS_o, o in the families of Figure 2, mod p (bmm.pdf, Section 3.3)", "bfs_orders.jl")
    cp = modular_parameters(S, p, point)
    say("p = $p; " * pointline(S, cp) * "; A = BFS_$(ordername(S)); τ = can_trace")
    say("table: do the sweeps of setRow's complete the coset table of BFS_o;  det: det CBM(A, BFS_o)" * (wantdet ? "" : " (not computed: |W| > $DENSE_MAX)") *
        ";  quasi-symmetric: τ(a) = δ_(a,1) on BFS_o (else: number of nonzero values)")
    stage("W and the trace")
    P = letters_in_W(S)
    H = HeckeCRG(S, cp); run_program(H, joinpath(S.dir, S.table)); T = MakeTrace(H)

    families = [(1, "orders of S", permutations(collect(1:n))),
                (2, "orders of S ∪ {z}", permutations(collect(1:n+1))),
                (3, "orders of S ∪ {z} without one generator", [o for g in 1:n for o in permutations(vcat(setdiff(1:n, g), [Z]))])]
    counts = String[]
    for (no, name, orders) in families
        stage("Family ($no): $name ($(length(orders)) orders)")
        nreach = ntable = ndet = nsuit = 0
        for o in orders
            words, edges = bfs_tree(S, P, o)
            length(words) < N && continue                             # the tree does not reach all cosets
            nreach += 1
            # the sweeps of setRow's on the tree of o
            _, complete, passes = vector_enumeration(HeckeCRG(S, cp), edges)
            ntable += complete
            # the elements u^m w of BFS_o in the basis A: trace values and determinant
            vals = trace_table(T, words, [shifted(T.φ[1])])                     # vals[i][1, m+1] = τ(T_u^m T_(w_i))
            bad = sum(count(!iszero, v) for v in values(vals)) - 1
            suit = bad == 0 && isone(vals[1][1, 1]); nsuit += suit
            dtxt = ""
            if wantdet
                rows = coordinates(H, words); A = zeros(Float64, NR, NR); L = Lam{E,Fp}
                for (i, v) in enumerate(rows)
                    um = one(L)
                    for m in 0:E-1
                        putrow!(A, (i - 1) * E + m + 1, SV(v.idx, [um * x for x in v.val])); um = um * lu(L)
                    end
                end
                d = sym(detmod(A)); ndet += abs(d) == 1
                dtxt = @sprintf("  det %6d", d)
            end
            say(@sprintf("o = %-18s table %-21s%s  quasi-symmetric %s", ordername(S, o),
                         complete ? "complete ($(length(passes)) sweeps)" : "open ($(passes[end][5]) rows)", dtxt, suit ? "yes" : "no ($bad)"))
        end
        nreach < length(orders) && say("$(length(orders) - nreach) orders do not reach all cosets")
        push!(counts, "family ($no), $nreach orders: table complete $ntable" * (wantdet ? ", det = ±1 $ndet" : "") * ", quasi-symmetric $nsuit")
    end
    stage("Result (mod $p)")
    foreach(say, counts)
    total()
    finish()
end

main()
