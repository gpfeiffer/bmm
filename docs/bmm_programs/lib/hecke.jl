#############################################################################
##
##  hecke.jl — the Hecke algebra H(W) through the coset table of a BFS basis
##             (bmm.pdf, Section 3); it loads the whole library
##
##  Conventions, used everywhere:
##    * a word is a vector of letters: 1..n the generators, n+1 = z, a
##      negative letter an inverse;
##    * the coset table of A = { u^m w_i } lives in Λ^N, Λ = R'[u]/(Hecke
##      relation of u) (lambda.jl): the vector c(u) e_i stands for
##      c(T_u) T_(w_i), coefficients on the left as h_{w,σ,w'} in H(W_0) in
##      §3.3; row (i, g) is e_i T_g in the basis A, for g in
##      Σ = S ∪ S^-1 ∪ {z, z^-1}, stored in the block column(S, g);
##    * a functional on Λ^N is a dictionary coset j => (f(e_j), f(u e_j), ...,
##      f(u^(e-1) e_j)) (trace.jl);
##    * the coefficient ring K of a table is PP (exact, R') or Fp (modulo a
##      prime, at a point of R');
##    * the library is set up for one group per process: PMOD, LAMRED and
##      PVARS are set once per run.
##
##  H = HeckeCRG(S, params) builds the empty coset table (a CosetTable);
##  setRow(H, i, g, w, fun) sets row (i, g) to the vector given by the rule
##  fun (Remark 3.10, the setRow commands), one of
##      :img   the vector w itself   (the tree edges, through makeEdge(H, i, k, g))
##      :gen   T_g = r_{k-1} + r_{k-2} T_g^-1 + ... + r_0 T_g^-(k-1)
##      :inv   T_g^-1 = T_g^{k-1} - r_{k-1} T_g^{k-2} - ... - r_1    (r_0 = 1)
##      :rel   e_i T_w, for a braid-group identity g = w
##  and returns false, setting nothing, while a row it reads is open.
##  run_program(H, file) executes a setRow program (cosettableNN.txt);
##  findRows(H) finds the setRow's that can be applied now (one sweep of the
##  vector enumeration, a sweep of §3.3); check_relations(H) tests the
##  defining relations on the complete table.
##
#############################################################################

using Chevie
isdefined(@__MODULE__, :GroupSpec) || include("spec.jl")      # the group file; W and the tree BFS_o
include("lambda.jl")          # Λ, the coefficients of the table
include("poly.jl")            # PP, the polynomials of R'; lift_to_R

# a sparse vector of Λ^N: coset indices and coefficients
struct SV{L}
    idx::Vector{Int32}
    val::Vector{L}
end
Base.:(==)(a::SV, b::SV) = a.idx == b.idx && a.val == b.val
nnz(v::SV) = length(v.idx)

# the coset table of A: rows[column(S, g)][i] = e_i T_g, nothing while the row is open
struct CosetTable{E,K}
    S::GroupSpec
    N::Int                                            # the number of cosets U w_i
    E::Int                                            # e = |U|
    par::Vector{Vector{K}}                            # the Hecke relation r_0, ..., r_{k-1} of each letter
    rows::Vector{Vector{Union{Nothing,SV{Lam{E,K}}}}}
    acc::Vector{Lam{E,K}}                             # a sparse accumulator for the vector being computed
    mark::BitVector
    touched::Vector{Int32}
end
coeftype(::CosetTable{E,K}) where {E,K} = K
include("modp.jl")            # Fp, the integers modulo p; determinants modulo p
include("trace.jl")           # the canonical trace: MakeTrace, can_trace
include("tests.jl")           # the tests of bmm.pdf, Section 4

# the parameters of each class: exact (the packed polynomials of R', invertible parameters 1) ...
function exact_parameters(S::GroupSpec)
    set_pvars!(Symbol.(others(S)))
    [vcat([one(PP)], [pvar(Symbol(nm)) for nm in S.params[c][2:end]]) for c in 1:nclasses(S)]
end
# ... or modulo p at a point ("v1,v2,...": the non-invertible parameters class by class; default 11, 13, 17, ...)
function modular_parameters(S::GroupSpec, p::Int, point::AbstractString = "")
    PMOD[] = p
    [Fp.(v) for v in point_values(S, point)]
end

# ---- the coset table and the setRow command ----------------------------------------------------------------
# the empty coset table over the parameters classpar (exact or modulo p), with the rows e_1 T_u^±1 = u^±1 e_1
function HeckeCRG(S::GroupSpec, classpar::Vector{Vector{K}}) where K
    E = paradeg(S); L = Lam{E,K}; N = ncosets(S); n = ngens(S)
    par = [classpar[S.classes[g]] for g in 1:n]
    set_lambda!(par[S.parabolic])
    rows = [Vector{Union{Nothing,SV{L}}}(nothing, N) for _ in 1:ncolumns(S)]
    H = CosetTable{E,K}(S, N, E, par, rows, fill(zero(L), N), falses(N), Int32[])
    setRow(H, 1, S.parabolic, basic_vec(H, 1, lu(L)), :img)          # e_1 T_u = u e_1
    setRow(H, 1, -S.parabolic, basic_vec(H, 1, luinv(L)), :img)      # e_1 T_u^-1 = u^-1 e_1
    H
end
# the complete table of a group file (its setRow program executed), exact (p = 0) or modulo p at a point
function HeckeCRG(file::AbstractString; p::Int = 0, point::AbstractString = "", progress = nothing)
    S = read_spec(file)
    H = HeckeCRG(S, p == 0 ? exact_parameters(S) : modular_parameters(S, p, point))
    run_program(H, joinpath(S.dir, S.table); progress = progress)
    H
end

row(H::CosetTable, g, i) = H.rows[column(H.S, g)][i]                             # e_i T_g, nothing while open
basic_vec(H::CosetTable{E,K}, i, x = one(Lam{E,K})) where {E,K} = SV(Int32[i], Lam{E,K}[x])   # x e_i

# the accumulator: add!(H, j, x) adds x to the coordinate j, result!(H) returns the sparse vector and clears
function add!(H::CosetTable, j, x)
    if H.mark[j]
        H.acc[j] += x
    else
        H.mark[j] = true; push!(H.touched, j); H.acc[j] = x
    end
end
function result!(H::CosetTable{E,K}) where {E,K}
    sort!(H.touched); idx = Int32[]; val = Lam{E,K}[]
    for j in H.touched
        H.mark[j] = false
        iszero(H.acc[j]) || (push!(idx, j); push!(val, H.acc[j]))
    end
    empty!(H.touched)
    SV(idx, val)
end
# v T_g, or nothing while a row it needs is open; v T_w for a word w; a linear combination Σ s_t v_t
function vec_under_mat(H::CosetTable, v, g)
    R = H.rows[column(H.S, g)]
    for k in v.idx; R[k] === nothing && return nothing; end
    for (k, c) in zip(v.idx, v.val), (j, x) in zip(R[k].idx, R[k].val); add!(H, j, c * x); end
    result!(H)
end
function vec_under_word(H::CosetTable, v, w)
    for g in w; v = vec_under_mat(H, v, g); v === nothing && return nothing; end
    v
end
function lincomb(H::CosetTable, terms)
    for (s, v) in terms
        iszero(s) && continue
        for (j, x) in zip(v.idx, v.val); add!(H, j, s * x); end
    end
    result!(H)
end

# the rules gen and inv of setRow
function gen_rule(H::CosetTable, i, g)             # e_i T_g = r_{k-1} e_i + r_{k-2} e_i T_g^-1 + ... + r_0 e_i T_g^-(k-1)
    r = H.par[g]; k = length(r); v = basic_vec(H, i); terms = [(r[k], v)]
    for j in k-1:-1:1
        v = vec_under_mat(H, v, -g); v === nothing && return nothing
        push!(terms, (r[j], v))
    end
    lincomb(H, terms)
end
function inv_rule(H::CosetTable{E,K}, i, g) where {E,K}   # e_i T_s^-1 = e_i T_s^{k-1} - r_{k-1} e_i T_s^{k-2} - ... - r_1 e_i, s = -g
    r = H.par[-g]; k = length(r); v = basic_vec(H, i); terms = [(-r[2], v)]
    for j in 3:k
        v = vec_under_mat(H, v, -g); v === nothing && return nothing
        push!(terms, (-r[j], v))
    end
    v = vec_under_mat(H, v, -g); v === nothing && return nothing
    push!(terms, (one(K), v))
    lincomb(H, terms)
end
# setRow(H, i, g, w, fun): row (i, g) := fun(i, g, w); false, setting nothing, if a row it needs is open
function setRow(H::CosetTable, i, g, w, fun::Symbol)
    if fun == :img
        v = w
    elseif fun == :rel
        v = vec_under_word(H, basic_vec(H, i), w)
    elseif fun == :gen
        v = gen_rule(H, i, g)
    elseif fun == :inv
        v = inv_rule(H, i, g)
    else
        error("setRow: unknown rule $fun")
    end
    v === nothing && return false
    R = H.rows[column(H.S, g)]
    R[i] === nothing || error("row ($i, $g) set twice")
    R[i] = v
    true
end
# the tree edge w_k = w_i g: e_i T_g = e_k and e_k T_g^-1 = e_i
function makeEdge(H::CosetTable, i, k, g)
    setRow(H, i, g, basic_vec(H, k), :img)
    setRow(H, k, -g, basic_vec(H, i), :img)
    nothing
end

open_rows(H) = sum(count(isnothing, R) for R in H.rows)
nonzeros(H) = sum(nnz(r) for R in H.rows for r in R if r !== nothing; init = 0)      # the nonzero entries of the table
coordinates(H, w::Vector{Int}) = vec_under_word(H, basic_vec(H, 1), w)        # e_1 ρ(T_w): T_w in the basis A

# ---- vector enumeration -------------------------------------------------------------------------------------
# the setRow program of a file (makeEdge / setRow lines); returns the number of setRow's and the tree edges
function run_program(H, file::AbstractString; progress = nothing)
    n = 0; edges = Tuple{Int,Int,Int}[]
    for ln in eachline(file)
        if (m = match(r"^makeEdge\((\d+), (\d+), (-?\d+)\)", ln)) !== nothing
            i, k, g = parse.(Int, m.captures); makeEdge(H, i, k, g); push!(edges, (i, k, g))
        elseif (m = match(r"^setRow\((\d+), (-?\d+), \[([-0-9, ]*)\], rel\)", ln)) !== nothing
            i, g = parse.(Int, m.captures[1:2]); w = parseword(m[3])
            setRow(H, i, g, w, :rel) || error("$ln: a row it needs is open"); n += 1
        elseif (m = match(r"^setRow\((\d+), (-?\d+), 0, (gen|inv)\)", ln)) !== nothing
            i, g = parse.(Int, m.captures[1:2])
            setRow(H, i, g, 0, Symbol(m[3])) || error("$ln: a row it needs is open"); n += 1
        end
        progress === nothing || progress(n)
    end
    open_rows(H) == 0 || error("the coset table is not complete after $file ($(open_rows(H)) rows open)")
    n, edges
end

# the identities g = w of the braid group used by the rule rel: every rotation of a relator, solved for its
# first letter (the braid relations, z = zword, z s = s z); shortest first
function relation_words(S::GroupSpec)
    D = Dict{Int,Vector{Vector{Int}}}()
    for r0 in relators(S), r in (r0, -reverse(r0)), j in eachindex(r)
        ρ = vcat(r[j:end], r[1:j-1]); w = Int[]
        for g in -reverse(ρ[2:end]); (!isempty(w) && w[end] == -g) ? pop!(w) : push!(w, g); end   # freely reduced
        isempty(w) || w in get!(D, ρ[1], Vector{Int}[]) || push!(D[ρ[1]], w)
    end
    foreach(L -> sort!(L, by = length), values(D))
    D
end
# one sweep of the vector enumeration (§3.3): on every open row (i, g) try gen or inv, then the
# identities g = w; returns the setRow lines applied
function findRows(H, RW = relation_words(H.S))
    n = ngens(H.S); lines = String[]
    for g in vcat(1:n+1, -(n+1):-1), i in 1:H.N
        row(H, g, i) === nothing || continue
        if 0 < g <= n && setRow(H, i, g, 0, :gen)
            push!(lines, "setRow($i, $g, 0, gen)")
        elseif -n <= g < 0 && setRow(H, i, g, 0, :inv)
            push!(lines, "setRow($i, $g, 0, inv)")
        else
            for w in get(RW, g, Vector{Int}[])
                setRow(H, i, g, w, :rel) && (push!(lines, "setRow($i, $g, [$(join(w, ", "))], rel)"); break)
            end
        end
    end
    lines
end
# the vector enumeration procedure (§3.3): the tree edges, then sweeps of findRows until the table is complete
# or a sweep finds nothing.  Returns the lines of the setRow program, whether the table is complete, and per
# sweep (setRow's found, by gen, by inv, by rel, rows still open).
function vector_enumeration(H, edges; maxpasses = 200, report = nothing)
    RW = relation_words(H.S); lines = ["makeEdge($i, $k, $g)" for (i, k, g) in edges]
    for (i, k, g) in edges; makeEdge(H, i, k, g); end
    passes = NTuple{5,Int}[]
    for pass in 1:maxpasses
        push!(lines, "# sweep $pass"); new = findRows(H, RW); append!(lines, new)
        c(s) = count(endswith(s), new)
        push!(passes, (length(new), c("gen)"), c("inv)"), c("rel)"), open_rows(H)))
        report === nothing || report(pass, passes[end])
        (open_rows(H) == 0 || isempty(new)) && return lines, open_rows(H) == 0, passes
    end
    lines, false, passes
end

# ---- many words at once -------------------------------------------------------------------------------------
# words evaluated along a trie: step(value, letter) extends a value by one letter, each common prefix once;
# visit(i, value), if given, receives each value at once and nothing is stored
function along_words(words::Vector{Vector{Int}}, start, step; progress = nothing, visit = nothing)
    out = visit === nothing ? Vector{typeof(start)}(undef, length(words)) : nothing
    stack = [start]; prev = Int[]
    for (cnt, i) in enumerate(sortperm(words))
        w = words[i]; c = 0
        while c < min(length(w), length(prev)) && w[c+1] == prev[c+1]; c += 1; end
        resize!(stack, c + 1)
        for l in c+1:length(w); push!(stack, step(stack[end], w[l])); end
        prev = w
        visit === nothing ? (out[i] = stack[end]) : visit(i, stack[end])
        progress === nothing || progress(cnt)
    end
    out
end
# the coordinates of every word of a list, along a trie
coordinates(H, words::Vector{Vector{Int}}; progress = nothing) =
    along_words(words, basic_vec(H, 1), (v, g) -> vec_under_mat(H, v, g); progress = progress)

# ---- the defining relations on the complete table ------------------------------------------------------------
# tested on every basis vector e_i: the Hecke relations, T_g T_g^-1 = 1, the braid relations, T_z = T_zword,
# T_z T_s = T_s T_z; returns the labels (in the letters of the group) and, for each, the number of e_i on which
# the relation fails
function check_relations(H; progress = nothing)
    S = H.S; par = H.par; n = ngens(S); Z = zletter(S)
    words = Vector{Int}[]; at(w) = (push!(words, collect(Int, w)); length(words))
    pw = [[at(fill(g, j)) for j in 0:length(par[g])] for g in 1:n]
    tests = vcat([(pw[g][end], 0, g) for g in 1:n],                   # (left word, right word, Hecke relation of g)
                 [(at([g, -g]), at(Int[]), 0) for g in 1:Z],
                 [(at(l), at(r), 0) for (l, r) in S.braid],
                 [(at([Z]), at(S.zword), 0)],
                 [(at([Z, g]), at([g, Z]), 0) for g in 1:n])
    labels = vcat([heckerel(S, g; prime = true) for g in 1:n],
                  ["$(Tword(S, [g])) $(Tword(S, [-g])) = 1" for g in 1:Z],
                  ["$(Tword(S, l)) = $(Tword(S, r))" for (l, r) in S.braid],
                  ["T_z = $(Tword(S, S.zword))"],
                  ["T_z $(Tword(S, [g])) = $(Tword(S, [g])) T_z" for g in 1:n])
    fails = zeros(Int, length(tests))
    for i in 1:H.N
        V = along_words(words, basic_vec(H, i), (v, g) -> vec_under_mat(H, v, g))
        for (t, (l, r, g)) in enumerate(tests)
            rhs = g == 0 ? V[r] : lincomb(H, [(par[g][j], V[pw[g][j]]) for j in 1:length(par[g])])
            V[l] == rhs || (fails[t] += 1)
        end
        progress === nothing || progress(i)
    end
    labels, fails
end
