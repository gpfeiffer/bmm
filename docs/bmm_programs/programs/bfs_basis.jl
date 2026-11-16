#############################################################################
##
##  bfs_basis.jl — the BFS basis A = BFS_o and its coset table  (bmm.pdf, §3)
##
##  1. The tree BFS_o (Section 3.2) is built in W: Chevie's crg(n) gives
##     the right cosets U w of U = <u>; the letters are taken in the order
##     o = `bfs` of the group file (z may be one of them).
##  2. The coset table CT_A is completed by sweeps of setRow's (§3.3), run
##     modulo a prime at a random point of R'.  The sequence of setRow's
##     found is written to cosettableNN.txt.  Which entries a sweep can set
##     does not depend on the point (up to an accidental zero mod p, which
##     the exact run of bmm_proof.jl would report as a setRow that fails).
##  3. The defining relations of H are tested on the completed table.
##  The proof that A is a basis is the exact execution of cosettableNN.txt
##  by bmm_proof.jl (Theorem 3.11, BFS_o is a basis); this program finds
##  that file.
##
##  usage:  julia programs/bfs_basis.jl GNN [--p=15013]        (record: GNN/1_bfs_basis.txt)
##
#############################################################################

include("../lib/report.jl")
include("../lib/spec.jl")
const SPEC = read_spec(ARGS[1])                        # the group file
if SPEC.engine != "cyclic"                             # G31 .. G34: the driver of the engine writes the record
    include("../lib/$(SPEC.engine)/driver.jl")
    run_step(SPEC, :bfs)
    exit()
end
include("../lib/hecke.jl")
using Random

function main()
    S = SPEC; record(S, "1_bfs_basis.txt")
    p = parse(Int, argval("p", "15013")); PMOD[] = p
    rng = MersenneTwister(1)                        # the random point of R'
    o = S.bfs
    N = ncosets(S)

    header(S, "the BFS basis A = BFS_o and its coset table, mod p (bmm.pdf, Section 3)", "bfs_basis.jl")
    say("o = $(ordername(S, o))")

    stage("Tree BFS_o (Section 3.2), in W")
    P = letters_in_W(S)
    words, edges = bfs_tree(S, P, o)
    depth = maximum(length, words)
    say("nodes per level: " * join([count(w -> length(w) == d, words) for d in 0:depth], ", "))
    N <= 16 && wrapped("w_1, ..., w_$N = " * join([replace(wordstr(S, w), " " => "~") for w in words], ", "))
    if !testing("the tree reaches all $N cosets of U", length(words) == N)
        stage("Result"); say(tests()); total(); finish(2)
    end

    cp = [vcat([Fp(1)], [Fp(rand(rng, 2:p-1)) for _ in 2:classorder(S, c)]) for c in 1:nclasses(S)]
    stage("Coset table CT_A by sweeps of setRow's (Section 3.3)")
    say("p = $p; " * pointline(S, cp))
    H = HeckeCRG(S, cp)
    lines, complete, passes = vector_enumeration(H, edges; report = (i, (found, ngen, ninv, nrel, op)) ->
        say(@sprintf("sweep %d: %d setRow's (gen %d, inv %d, rel %d), %d rows open", i, found, ngen, ninv, nrel, op)))
    nset = count(l -> startswith(l, "setRow"), lines)
    testing("the table is complete", complete; note = "$(length(edges)) tree edges, $nset setRow's, $(length(passes)) sweeps")

    if complete
        stage("Relations of H on the table")
        test_relations(H; progress = progress_printer("rows tested", N))
    end

    # the setRow program found
    out = joinpath(S.dir, S.table * (complete ? "" : ".open"))
    open(out, "w") do io
        println(io, "# The coset table of the BFS basis A = BFS_o of H($(S.name)): the setRow program (written by programs/bfs_basis.jl)")
        println(io, "# $N cosets U w_i of U = <u> (u = letter $(S.parabolic)), o = ($(join(o, ","))), z = letter $(zletter(S))")
        println(io, "# complete: $complete; $(length(passes)) sweeps, $(length(edges)) tree edges, $nset setRow's (found at a random point mod $p)")
        println(io, "# makeEdge(i, k, g): w_k = w_i g, so e_i T_g = e_k;  setRow(i, g, 0, gen|inv): row (i, g) from the Hecke relation of |g|;")
        println(io, "# setRow(i, g, [w], rel): row (i, g) = e_i T_w for the braid-group identity g = w")
        foreach(l -> println(io, l), lines)
    end
    ok = complete && alltrue()
    stage("Result (mod $p)")
    say(tests() * (ok ? "; written $(S.table) (executed exactly by bmm_proof.jl)" : ""))
    total()
    finish(ok ? 0 : 2)
end

main()
