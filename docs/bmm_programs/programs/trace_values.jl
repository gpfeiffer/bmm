#############################################################################
##
##  trace_values.jl — values of the canonical trace τ on braid words
##                    (an example of the use of can_trace in other problems)
##
##  The coset table of the BFS basis A is set (cosettableNN.txt is executed)
##  and τ(T_w) = can_trace(T, w) is printed for a list of words w: by
##  default the powers of the generators, some products of two generators
##  and the central element; or the words given by --words.  The values are
##  exact, in R (computed over R', the invertible parameters restored by
##  homogeneity), or, with --p, modulo a prime at a point of R'.
##
##  usage:  julia programs/trace_values.jl GNN [--words="1,-2;2,2,1"] [--p=15013 [--point=v1,v2,...]]
##  (record: GNN/4_trace_values.txt, written only for the default list of words)
##  A word is a list of letters separated by commas (1..n the generators in the order of the group file,
##  n+1 = z, negative = inverse); words are separated by semicolons.
##
#############################################################################

using Chevie
include("../lib/report.jl")
include("../lib/spec.jl")
const SPEC = read_spec(ARGS[1])                        # the group file
if SPEC.engine != "cyclic"                             # G31 .. G34: the driver of the engine writes the record
    include("../lib/$(SPEC.engine)/driver.jl")
    run_step(SPEC, :traces)
    exit()
end
include("../lib/hecke.jl")

# the default list: T_g^j (-2 <= j <= order of g) for one generator of each class, T_g T_h, T_g T_h^-1 and
# T_g^-1 T_h^-1 for the first two generators, T_z and T_z^-1
function default_words(S::GroupSpec)
    n = ngens(S); Z = zletter(S); ws = Vector{Int}[]
    for g in 1:n
        any(h -> S.classes[h] == S.classes[g], 1:g-1) && continue
        for j in vcat(-2:-1, 1:S.orders[g]); push!(ws, fill(sign(j) * g, abs(j))); end
    end
    n >= 2 && append!(ws, [[1, 2], [1, -2], [-1, -2]])
    append!(ws, [[Z], [-Z]])
    ws
end

function main()
    S = SPEC
    p = parse(Int, argval("p", "0")); point = argval("point", "")
    ws = argval("words", ""); words = isempty(ws) ? default_words(S) : [parseword(w) for w in split(ws, ";")]
    isempty(ws) && record(S, "4_trace_values.txt")
    header(S, "values of the canonical trace τ (can_trace)", "trace_values.jl")
    stage("Coset table of A")
    nlines = count(l -> startswith(l, "setRow"), eachline(joinpath(S.dir, S.table)))
    T = load_trace(ARGS[1]; p = p, point = point, progress = progress_printer("setRow's executed", nlines))
    say("$nlines setRow's executed")
    stage("Values of τ")
    if p == 0
        say("exact values in R (computed with $(join(invertibles(S), " = ")) = 1, lifted by degree)")
    else
        cp = [T.H.par[findfirst(==(c), S.classes)] for c in 1:nclasses(S)]      # the parameters of each class
        say("values modulo p = $p at " * pointline(S, cp))
    end
    vals = can_trace(T, words)                     # all words at once, common prefixes computed once
    for (w, x) in zip(words, vals)
        wrapped("τ($(replace(Tword(S, w), " " => "~"))) = " * (p == 0 ? pretty(x) : string(symm(x))))
    end
    total()
    finish()
end

main()
