#############################################################################
##
##  spec.jl — the data of one group, read from GNN/groupNN.toml
##
##  The notation of bmm.pdf and its names here (one line per object):
##    W, S = {s_1, ..., s_n}      letters 1..n (`letters`), their orders and conjugacy classes
##                                (`orders`, `classes`); W as a permutation group: Chevie's
##                                crg(`chevie_group`), letter g = generator `chevie`[g] (letters_in_W)
##    T^k = r_{k-1} T^{k-1} + ... + r_0  (relation (2.2))      `params`[c] = [r_0, ..., r_{k-1}] of the
##                                class c, r_0 invertible; R = Z[r_j][r_0^±1], R' = R/(r_0 - 1) (poly.jl)
##    the braid relations        `braid`;  the relators: relators(S)
##    z, letter n+1              `zword`;  T_π = T_z^`pipower` (condition (3) of the conjecture)
##    W_0 = U = <u>, e = |U|     `parabolic` (the letter u), paradeg(S); N = |W|/e cosets U w
##    o, T_o, A = BFS_o          `bfs` (the order o), bfs_tree; A = { u^m w_i }, u^m w_i at index
##                                (i-1) e + m + 1; its coset table: the setRow program `table`
##    B = Z^k U X, a z^k-basis   k = `zstep`, d = l/k = `zlevels` (l the order of z), X = the words
##        (Definition 4.3)        of the file `basis`;  B = { z^(k j) u^m x : j < d, m < e, x in X }
##    E_j(h) = λ_a(T_z^(-kJ) h), a = T_u^m T_(w_i)  (§4.3, Table 1)      `trace` = "J,i,m"
##    det Gram(τ_B)  (Table 2)   `bmm_table`, for the comparison printed by bmm_proof.jl
##    the coefficients of R'     `coefficients` = "Int64" (default) or "Int128" (poly.jl; G17)
##  Words are vectors of letters, negative letters are inverses.  The columns of the coset table are
##  indexed by Σ = S ∪ S^-1 ∪ {z, z^-1}: column(S, g) is the block of letter g.
##
##  The engine.  The fields above describe the groups G4, ..., G29, whose coset tables are filled over the
##  cyclic parabolic U = <u> (engine "cyclic", the default, lib/hecke.jl).  The four largest groups have a
##  non-cyclic parabolic P and a tower of parabolics (bmm.pdf, Section 5); their group files say
##    engine = "tower"       G31, G32, G33, G34: lib/tower/   (coefficients in H(P), P built level by level)
##  Both engines fill every coset table by the setRow procedure of bmm.pdf §3.3, and give the tower:
##    [[level]]              one table per level of the tower, bottom first, one key per line (the top level is W
##                           itself and is described by the fields below): name, gens (the letters of the level),
##                           over (the letters of the level below), order, bfs (the ordering of its coset tree),
##                           pi or zeta (the form of condition (3) at that level), zword (a central element of the
##                           level)
##    pairing                the second family of the pairing: "inverse" (B^-1, the default of G4..G29), "rev"
##                           (the reversed words), "ztree" (G31: a second breadth-first tree Y_1 with the letter z,
##                           its ordering `pairing_bfs`, its words in the file `pairing_words`, paired with the
##                           reversed words) or a file (G32: family32.txt, with `family` naming its kind)
##    zeta, condition3       the form of the test of condition (3): a central word ζ with ζ² = π, or
##                           condition3 = "basis" (every element of B) or "classes" (one element per conjugacy class)
##    consequences           relations checked on the tables but never used by the enumeration
##    proof_skip_top_relations  relations of braid that the step proof does not test on the cosets of the top (G34:
##                           a check of the code, exactly too large; the step bfs tests them modulo p)
##    setrow_z               false: the setRow tables have no columns of z and z^-1 (G32, G33, G34)
##    seeds                  words that seed the top tree (G32, Definition 5.5)
##    garside, garside_perm  the Garside element Δ and its permutation of the generators (G32)
##    steps                  the steps of ./run.sh GNN all, in order (default: bfs modular proof traces orders)
##    threads, memory        what ./run.sh gives the group (default 1 thread, 6G)
##  Every field not listed in the struct below is kept in `opts`, for the engine to read.  The headers of
##  lib/tower/driver.jl says how the engine tower uses them.
##
#############################################################################

using TOML

# a word "1,-2,3" as [1, -2, 3]; "" and "e" are the empty word
function parseword(s::AbstractString)
    s = strip(s)
    (s == "" || s == "e") ? Int[] : parse.(Int, split(s, ","))
end

struct GroupSpec
    name::String
    dir::String                          # folder of the toml file
    order::Int                           # |W|
    letters::Vector{String}
    orders::Vector{Int}                  # order of each generator
    classes::Vector{Int}                 # class of each generator
    params::Vector{Vector{String}}       # per class: names of r_0, ..., r_{k-1}
    chevie::Vector{Int}                  # Chevie generator of crg(n) for each letter
    chevie_group::Int
    braid::Vector{Tuple{Vector{Int},Vector{Int}}}
    parabolic::Int
    zword::Vector{Int}
    zstep::Int
    zlevels::Int
    pipower::Int
    bfs::Vector{Int}                     # letter order of the breadth-first tree
    extra::Vector{Vector{Int}}           # extra relators, used only to derive rows
    basis::String
    table::String                        # the file of the coset table of A (the setRow program)
    trace::String                        # "J,i,m" (empty until zbasis_modular.jl found it)
    bmm_table::String                    # det Gram(tau_B) as in Table 2 of bmm.pdf
    split::Int                           # F_0 computed as t(z^(-k j) b · b'^-1 z^(k j)): this j (default 0)
    engine::String                       # "cyclic" (default) or "tower": the library that fills the tables
    levels::Vector{Dict{String,Any}}     # the tower, one entry per [[level]] of the group file (engine tower)
    threads::Int                         # threads and memory for ./run.sh (default 1, "6G")
    memory::String
    steps::Vector{String}                # the steps of ./run.sh GNN all, in order
    opts::Dict{String,Any}               # every other optional field of the group file, read by the engine
end
const KNOWN_FIELDS = ["name", "order", "letters", "orders", "classes", "params", "chevie", "chevie_group", "braid", "coefficients",
    "parabolic", "zword", "zstep", "zlevels", "pipower", "bfs", "extra_relators", "basis", "table", "trace",
    "bmm_table", "split", "engine", "level", "threads", "memory", "steps"]

# read_spec("G20") or read_spec("G20/group20.toml")
# the field `coefficients` of the group file named first on the command line (GNN or a toml file): Int64 or Int128.
# poly.jl calls it when it is loaded, before the group file is read, since all polynomials share one coefficient type.
function coefficient_type(args = ARGS)
    isempty(args) && return Int64
    file = args[1]
    m = match(r"^G(\d+)$", file)
    m === nothing || (file = joinpath(dirname(@__DIR__), file, "group" * lpad(m[1], 2, '0') * ".toml"))
    (endswith(file, ".toml") && isfile(file)) || return Int64
    c = get(TOML.parsefile(file), "coefficients", "Int64")
    c == "Int64" ? Int64 : c == "Int128" ? Int128 : error("$file: coefficients must be \"Int64\" or \"Int128\"")
end

function read_spec(file::AbstractString)
    if (m = match(r"^G(\d+)$", file)) !== nothing         # GNN: the folder GNN next to lib/ (found at run time)
        file = joinpath(dirname(@__DIR__), file, "group" * lpad(m[1], 2, '0') * ".toml")
    end
    d = TOML.parsefile(file)
    br = Tuple{Vector{Int},Vector{Int}}[]
    for s in d["braid"]
        l, r = split(s, "=")
        push!(br, (parseword(l), parseword(r)))
    end
    n = length(d["letters"])
    engine = get(d, "engine", "cyclic")
    engine in ("cyclic", "tower") || error("$file: unknown engine \"$engine\" (cyclic or tower)")
    S = GroupSpec(d["name"], dirname(abspath(file)), d["order"], d["letters"], d["orders"], d["classes"],
              d["params"], get(d, "chevie", collect(1:n)), get(d, "chevie_group", 0), br, get(d, "parabolic", 0),
              parseword(d["zword"]), get(d, "zstep", 1), get(d, "zlevels", 1), d["pipower"],
              parseword(get(d, "bfs", join(1:n, ","))), parseword.(get(d, "extra_relators", String[])),
              get(d, "basis", ""), get(d, "table", ""), get(d, "trace", ""), get(d, "bmm_table", ""),
              get(d, "split", 0), engine, get(d, "level", Dict{String,Any}[]),
              get(d, "threads", 1), get(d, "memory", "6G"),
              get(d, "steps", ["bfs", "modular", "proof", "traces", "orders"]),
              Dict{String,Any}(k => v for (k, v) in d if !(k in KNOWN_FIELDS)))
    S.pipower >= S.zstep * (S.zlevels - 1) || error("$file: pipower must be at least zstep (zlevels - 1)")
    if engine == "cyclic"
        S.parabolic > 0 || error("$file: the engine cyclic needs the field parabolic (the letter u)")
        isempty(S.basis) && error("$file: the engine cyclic needs the field basis")
        isempty(S.table) && error("$file: the engine cyclic needs the field table")
    end
    S
end

ngens(S::GroupSpec) = length(S.letters)
zletter(S::GroupSpec) = ngens(S) + 1
ncolumns(S::GroupSpec) = 2 * (ngens(S) + 1)                      # |Σ|, Σ = S ∪ S^-1 ∪ {z, z^-1}
column(S::GroupSpec, g::Int) = g > 0 ? g : ncolumns(S) + 1 + g   # the column of letter g: 1..n+1, then the inverses
paradeg(S::GroupSpec) = S.orders[S.parabolic]            # e = |U|
ncosets(S::GroupSpec) = S.order ÷ paradeg(S)             # N = number of cosets U w = rank of the coset table over Λ
nclasses(S::GroupSpec) = length(S.params)
classorder(S::GroupSpec, c) = S.orders[findfirst(==(c), S.classes)]     # the order of the letters of class c
invertibles(S::GroupSpec) = [S.params[c][1] for c in 1:nclasses(S)]                      # the constant terms r_0
others(S::GroupSpec) = [nm for c in 1:nclasses(S) for nm in S.params[c][2:end]]          # the generators of R'

# the words X of the basis file: one word per line, letters separated by commas ("e" = empty word);
# '#' starts a comment
function read_basis(S::GroupSpec)
    X = Vector{Int}[]
    for ln in eachline(joinpath(S.dir, S.basis))
        t = strip(split(ln, "#")[1]); isempty(t) && continue
        push!(X, parseword(t))
    end
    length(X) * paradeg(S) * S.zlevels == S.order ||
        error("$(S.basis): |X| = $(length(X)), e = $(paradeg(S)), zlevels = $(S.zlevels) do not give |W| = $(S.order)")
    isempty(X[1]) || error("$(S.basis): the first word must be e (the identity is the first element of B)")
    X
end

# the words u^m x of UX, index (i-1)*e + m + 1
level0(S::GroupSpec, X) = [vcat(fill(S.parabolic, m), X[i]) for i in eachindex(X) for m in 0:paradeg(S)-1]
# all words of B = { z^(k j) u^m x }, level by level
basiswords(S::GroupSpec, X) = [vcat(fill(zletter(S), S.zstep * j), b) for j in 0:S.zlevels-1 for b in level0(S, X)]

# the relators of the presentation as words (braid relators l r^-1, z^-1 zword, [z, g]) plus the extra ones
function relators(S::GroupSpec)
    n = ngens(S); Z = zletter(S)
    rels = [vcat(l, -reverse(r)) for (l, r) in S.braid]
    push!(rels, vcat([-Z], S.zword))
    for g in 1:n; push!(rels, [Z, g, -Z, -g]); end
    append!(rels, S.extra)
    rels
end

# the degree w(b) in Z^(classes) (the homogeneity argument of bmm.pdf of 3 Nov, Lemma 5.6): each letter counts
# +-1 in its class, z counts w(zword)
function degree(S::GroupSpec, w::Vector{Int})
    d = zeros(Int, nclasses(S)); zd = zeros(Int, nclasses(S))
    for g in S.zword; zd[S.classes[abs(g)]] += sign(g); end
    for g in w
        if abs(g) == zletter(S)
            d .+= sign(g) .* zd
        else
            d[S.classes[abs(g)]] += sign(g)
        end
    end
    d
end

# det Gram(tau_B) = ± Π_c x_c^(D_c / k_c), D = 2 Σ_b w(b) (the homogeneity argument of bmm.pdf of 3 Nov,
# Lemma 5.9 and Corollary 5.10)
function det_exponents(S::GroupSpec, X)
    D = zeros(Int, nclasses(S)); Zs = fill(zletter(S), S.zstep)
    for x in X, m in 0:paradeg(S)-1, κ in 0:S.zlevels-1
        D .+= 2 .* degree(S, vcat(fill(S.parabolic, m), repeat(Zs, κ), x))
    end
    k = [classorder(S, c) for c in 1:nclasses(S)]
    all(D .% k .== 0) || error("degree $(D) not divisible by the orders $(k)")
    D, D .÷ k
end
# the trace "J,i,m": τ(T_z^(kJ) h) is the coefficient of T_u^m T_(w_i) in h
function parse_trace(s::AbstractString)
    f = parse.(Int, split(s, ","))
    length(f) == 3 || error("trace \"$s\": expected \"J,i,m\"")
    f[1], f[2], f[3]
end

# x_1^α_1 x_2^α_2 ..., the invertible parameters in alphabetical order (as in Table 2 of bmm.pdf)
monomial_string(S::GroupSpec, α) =
    join(sort(["$(S.params[c][1])^$(α[c])" for c in eachindex(α) if α[c] != 0]), " ")

# ---- the tree BFS_o in W (bmm.pdf, Section 3.2) -----------------------------------------------------------
# W as a permutation group (Chevie's crg); the checks on the presentation are printed as tests
function letters_in_W(S::GroupSpec)
    W = crg(S.chevie_group); n = ngens(S); Z = zletter(S)
    length(W) == S.order || error("crg($(S.chevie_group)) has order $(length(W)), the group file says $(S.order)")
    P = Dict{Int,Any}(g => W(S.chevie[g]) for g in 1:n)
    for g in 1:n; P[-g] = inv(P[g]); end
    wordperm(w) = isempty(w) ? one(P[1]) : prod(P[g] for g in w)
    P[Z] = wordperm(S.zword); P[-Z] = inv(P[Z])
    testing("in W: " * join(S.letters, ", ") * " have order" * (n > 1 ? "s " : " ") * join(S.orders, ", "),
            all(order(P[g]) == S.orders[g] for g in 1:n))
    for (l, r) in S.braid; testing("in W: $(wordstr(S, l)) = $(wordstr(S, r))", wordperm(l) == wordperm(r)); end
    testing("in W: z = $(wordstr(S, S.zword)) is central", all(P[Z] * P[g] == P[g] * P[Z] for g in 1:n);
            note = "z has order $(order(P[Z])) in W")
    order(P[Z]) == S.zstep * S.zlevels || error("z has order $(order(P[Z])) in W, but zstep * zlevels = $(S.zstep * S.zlevels)")
    P
end
# the nodes of each level, left to right, times the letters of o in order; a product in a coset already
# reached is discarded.  Returns the words w_i and the tree edges (i, k, g).
function bfs_tree(S::GroupSpec, P, o::Vector{Int})
    deg = maximum(length(P[g].d) for g in 1:ngens(S))
    Up = [P[S.parabolic]^m for m in 0:paradeg(S)-1]
    images(q) = Int16[i^q for i in 1:deg]
    key(p) = minimum(images(u * p) for u in Up)                             # a name of the coset U p
    reps = Any[one(P[1])]; words = [Int[]]; index = Dict(key(reps[1]) => 1); edges = Tuple{Int,Int,Int}[]
    q = 1
    while q <= length(reps)
        for g in o
            p = reps[q] * P[g]; k = key(p); haskey(index, k) && continue
            push!(reps, p); push!(words, vcat(words[q], g)); index[k] = length(reps); push!(edges, (q, length(reps), g))
        end
        q += 1
    end
    words, edges
end
