#############################################################################
##
##  alg.jl — a Hecke algebra H(P) as a flat algebra over the ground ring S
##
##  Basis b_1 = 1, ..., b_d: positive words in the generators of P, closed
##  under prefixes (b_x = b_parent(x) T_letter(x)).  Stored: the sparse right
##  and left multiplications by the generators, R[s][x] = b_x T_s and
##  L[s][x] = T_s b_x.  A product x y is computed along the prefixes of the
##  words of the support of y (x b_w = (x b_parent) T_s) or along the
##  suffixes of the words of the support of x (T_u y), whichever is cheaper.
##  The trace τ_P is the coefficient of b_1.
##
##  Units.  find_inverse(A, h) recognises ± b, ± b^-1 b' and ± b b'^-1 for
##  basis elements b, b' — images of braids of P, hence units — and returns
##  the inverse, verified by multiplication; nothing otherwise (h may still
##  be a unit).  The search is skipped unless h is ± a single term at the
##  group-algebra point, which a unit of this kind must be.
##
#############################################################################

include("ring.jl")

# a sparse vector Σ val[k] b_idx[k], idx increasing, val nonzero
struct SV{S}
    idx::Vector{Int32}
    val::Vector{S}
end
Base.:(==)(x::SV, y::SV) = x.idx == y.idx && x.val == y.val
Base.hash(x::SV, h::UInt) = hash(x.val, hash(x.idx, h))
Base.iszero(x::SV) = isempty(x.idx)
nterms(x::SV) = length(x.idx)
svzero(::Type{S}) where {S} = SV{S}(Int32[], S[])                         # 0
svunit(::Type{S}, i::Integer) where {S} = SV{S}(Int32[i], S[one(S)])      # b_i
# the coefficient of b_i in x
function coefficient(x::SV{S}, i::Integer) where {S}
    k = searchsortedfirst(x.idx, Int32(i))
    (k <= length(x.idx) && x.idx[k] == i) ? x.val[k] : zero(S)
end

function lincomb(x::SV{S}, y::SV{S}, sgn::Int) where {S}       # x + sgn y
    idx = Int32[]; val = S[]; i = 1; j = 1; nx = length(x.idx); ny = length(y.idx)
    @inbounds while i <= nx || j <= ny
        if j > ny || (i <= nx && x.idx[i] < y.idx[j])
            push!(idx, x.idx[i]); push!(val, x.val[i]); i += 1
        elseif i > nx || y.idx[j] < x.idx[i]
            push!(idx, y.idx[j]); push!(val, sgn == 1 ? y.val[j] : -y.val[j]); j += 1
        else
            v = sgn == 1 ? x.val[i] + y.val[j] : x.val[i] - y.val[j]
            iszero(v) || (push!(idx, x.idx[i]); push!(val, v))
            i += 1; j += 1
        end
    end
    SV{S}(idx, val)
end
Base.:+(x::SV{S}, y::SV{S}) where {S} = isempty(y.idx) ? x : isempty(x.idx) ? y : lincomb(x, y, 1)
Base.:-(x::SV{S}, y::SV{S}) where {S} = isempty(y.idx) ? x : lincomb(x, y, -1)
Base.:-(x::SV{S}) where {S} = SV{S}(x.idx, S[-v for v in x.val])
function scale(c::S, x::SV{S}) where {S}                        # c x, c in the ground ring
    isone(c) && return x
    idx = Int32[]; val = S[]
    for k in eachindex(x.idx)
        v = c * x.val[k]; iszero(v) || (push!(idx, x.idx[k]); push!(val, v))
    end
    SV{S}(idx, val)
end
function scale(n::Integer, x::SV{S}) where {S}                  # n x, n an integer
    n == 1 && return x
    n == -1 && return -x
    scale(n * one(S), x)
end

# ---- the accumulator: a dense buffer over the basis, emptied into a sparse vector ------------------------
mutable struct Acc{S}
    buf::Vector{S}
    terms::Vector{Vector{Term}}             # for S = Poly: the terms of the products, combined once
    touched::Vector{Int32}
    mark::BitVector
end
# an empty accumulator over a basis of d elements
Acc{S}(d::Int) where {S} = Acc{S}(fill(zero(S), d), S == Poly ? [Term[] for _ in 1:d] : Vector{Term}[], Int32[], falses(d))
# a[y] += c s
@inline function addmul!(a::Acc{S}, y::Integer, c::S, s::S) where {S}
    a.mark[y] || (a.mark[y] = true; push!(a.touched, y))
    a.buf[y] += c * s
    nothing
end
@inline function addmul!(a::Acc{Poly}, y::Integer, c::Poly, s::Poly)
    a.mark[y] || (a.mark[y] = true; push!(a.touched, y))
    pushprod!(a.terms[y], c, s)
    nothing
end
# the sparse vector of the accumulator, which is emptied
function collect!(a::Acc{S}) where {S}
    sort!(a.touched); idx = Int32[]; val = S[]
    for y in a.touched
        v = a.buf[y]; a.buf[y] = zero(S); a.mark[y] = false
        iszero(v) || (push!(idx, y); push!(val, v))
    end
    empty!(a.touched); SV{S}(idx, val)
end
function collect!(a::Acc{Poly})
    sort!(a.touched); idx = Int32[]; val = Poly[]
    for y in a.touched
        v = combine!(a.terms[y]); a.mark[y] = false
        iszero(v) || (push!(idx, y); push!(val, v))
    end
    empty!(a.touched); SV{Poly}(idx, val)
end

# ---- the algebra -------------------------------------------------------------------------------------------
mutable struct FlatAlg{S}
    name::String
    q::Hecke{S}
    d::Int
    ngens::Int
    words::Vector{Vector{Int}}              # b_x as a word in the generators 1..ngens of P
    parent::Vector{Int}
    letter::Vector{Int}
    R::Vector{Vector{SV{S}}}                # R[s][x] = b_x T_s
    L::Vector{Vector{SV{S}}}                # L[s][x] = T_s b_x
    suf::Vector{Int}                        # the word of b_x as a node of the trie of all suffixes
    sufnext::Vector{Int}                    # node of s w -> node of w (node 1: the empty word)
    sufletter::Vector{Int}
    acc::Acc{S}
    binv::Vector{Union{Nothing,SV{S}}}      # inverses of the basis elements, computed on demand
    units::Dict{SV{S},Union{Nothing,SV{S}}}  # the inverses found by find_inverse
    bylength::Vector{Int}                   # the basis elements by increasing word length
    lower_d::Int                            # for a level of a tower: the rank of the algebra below (0 at the bottom)
    cosetwords::Vector{Vector{Int}}         # and the coset words of this level (in the generators of P)
    shadow::Any                             # for S = Poly: the same algebra modulo a prime at a point (built on demand)
end
Base.show(io::IO, A::FlatAlg) = print(io, A.name)
Base.zero(A::FlatAlg{S}) where {S} = svzero(S)
Base.one(A::FlatAlg{S}) where {S} = svunit(S, 1)
basis(A::FlatAlg{S}, x::Integer) where {S} = svunit(S, x)
tau(A::FlatAlg{S}, h::SV{S}) where {S} = coefficient(h, 1)       # τ_P = the coefficient of b_1 = 1

# the flat algebra on the basis words, with the right and left multiplications R and L by the generators
function FlatAlg(name::String, q::Hecke{S}, words::Vector{Vector{Int}}, R, L; lower_d = 0, cosetwords = Vector{Int}[]) where {S}
    index = Dict(w => x for (x, w) in enumerate(words)); d = length(words)
    parent = [isempty(w) ? 0 : index[w[1:end-1]] for w in words]
    all(x -> x == 1 || parent[x] < x, 1:d) || error("the basis is not ordered along its tree")
    node = Dict(Int[] => 1); sufnext = [0]; sufletter = [0]
    function sufnode(w)
        get!(node, w) do
            t = sufnode(w[2:end]); push!(sufnext, t); push!(sufletter, w[1]); length(sufnext)
        end
    end
    suf = [sufnode(w) for w in words]
    FlatAlg{S}(name, q, d, length(R), words, parent, [isempty(w) ? 0 : w[end] for w in words], R, L, suf, sufnext, sufletter,
               Acc{S}(d), Vector{Union{Nothing,SV{S}}}(nothing, d), Dict{SV{S},Union{Nothing,SV{S}}}(),
               sortperm(length.(words)), lower_d, cosetwords, nothing)
end
# the value of a polynomial modulo PMOD[] at a point, and at the group-algebra point
function evalsh(q::Poly, pt::Vector{Int})
    v = Fp(0)
    for (k, c) in q.t
        t = Fp(c); for (i, e) in enumerate(exponents(k)); e == 0 || (t = t * Fp(powermod(pt[i], e, PMOD[]))); end
        v = v + t
    end
    Sh(v, Fp(atgroup(q)))
end
function evalsh(x::SV{Poly}, pt)
    idx = Int32[]; val = Sh[]
    for (i, c) in zip(x.idx, x.val); v = evalsh(c, pt); iszero(v) || (push!(idx, i); push!(val, v)); end
    SV{Sh}(idx, val)
end
# the algebra modulo a prime at a point (the heuristic search for units runs there; the result is verified exactly)
const SHADOWPOINT = [7, 10, 3]
function shadow_alg(A::FlatAlg{Poly})
    A.shadow === nothing || return A.shadow
    pt = SHADOWPOINT[1:length(PVARS)]
    q = Hecke{Sh}(A.q.k, [evalsh(r, pt) for r in A.q.r], A.q.name * " (shadow)")
    A.shadow = FlatAlg(A.name * " mod p", q, A.words, [[evalsh(x, pt) for x in R] for R in A.R], [[evalsh(x, pt) for x in L] for L in A.L];
                       lower_d = A.lower_d, cosetwords = A.cosetwords)
end
shadow_alg(A::FlatAlg{Sh}) = A
toshadow(A::FlatAlg{Poly}, h::SV{Poly}) = evalsh(h, SHADOWPOINT[1:length(PVARS)])      # h in the shadow
toshadow(A::FlatAlg{Sh}, h::SV{Sh}) = h

# the cyclic algebra H(Z_k): basis 1, u, ..., u^(k-1), u^k = Σ r_j u^j
function cyclic_alg(q::Hecke{S}) where {S}
    k = q.k; words = [fill(1, j) for j in 0:k-1]
    rows = [j < k - 1 ? svunit(S, j + 2) : SV{S}(Int32.(1:k), copy(q.r)) for j in 0:k-1]
    FlatAlg("H(Z$k)", q, words, [rows], [rows])
end

# x T_s (mats = A.R) or T_s x (mats = A.L)
function mulgen(A::FlatAlg{S}, x::SV{S}, mats::Vector{SV{S}}) where {S}
    a = A.acc
    @inbounds for k in eachindex(x.idx)
        c = x.val[k]; row = mats[x.idx[k]]
        for j in eachindex(row.idx); addmul!(a, row.idx[j], c, row.val[j]); end
    end
    collect!(a)
end
rmulgen(A::FlatAlg, x::SV, s::Int) = mulgen(A, x, A.R[s])
lmulgen(A::FlatAlg, s::Int, x::SV) = mulgen(A, x, A.L[s])
# x T_s^-1 or T_s^-1 x:  T_s^-1 = T_s^(k-1) - r_(k-1) T_s^(k-2) - ... - r_1   (Horner; r_0 = 1)
function mulinv(A::FlatAlg{S}, x::SV{S}, mats::Vector{SV{S}}) where {S}
    r = A.q.r; img = x
    for j in length(r)-1:-1:1; img = mulgen(A, img, mats) - scale(r[j+1], x); end
    img
end
# x T_s^±1, T_s^±1 x; x T_w, T_w x
rmulletter(A::FlatAlg, x::SV, s::Int) = s > 0 ? rmulgen(A, x, s) : mulinv(A, x, A.R[-s])
lmulletter(A::FlatAlg, s::Int, x::SV) = s > 0 ? lmulgen(A, s, x) : mulinv(A, x, A.L[-s])
rmulword(A::FlatAlg, x::SV, w) = foldl((h, s) -> rmulletter(A, h, s), w; init = x)
lmulword(A::FlatAlg, w, x::SV) = foldr((s, h) -> lmulletter(A, s, h), w; init = x)
element(A::FlatAlg, w) = rmulword(A, one(A), w)                  # T_w for a word in the letters ±1..±ngens

# Σ c_k x_k for scalars c_k of the ground ring and elements x_k
function addall(A::FlatAlg{S}, terms) where {S}
    a = A.acc
    for (c, x) in terms, k in eachindex(x.idx); addmul!(a, x.idx[k], c, x.val[k]); end
    collect!(a)
end
function Base.:*(x::SV{S}, y::SV{S}, A::FlatAlg{S}) where {S}  # not used; see mul
    mul(A, x, y)
end
# x y: along the prefixes of the words of y, or the suffixes of those of x, whichever is cheaper
function mul(A::FlatAlg{S}, x::SV{S}, y::SV{S}) where {S}
    (iszero(x) || iszero(y)) && return zero(A)
    length(y.idx) == 1 && y.idx[1] == 1 && return scale(y.val[1], x)
    length(x.idx) == 1 && x.idx[1] == 1 && return scale(x.val[1], y)
    need = Set{Int32}()                                  # right: x b_w for the words w of the support of y and their prefixes
    for w in y.idx; while w != 1 && !(w in need); push!(need, w); w = A.parent[w]; end; end
    sufs = Set{Int}()                                    # left: T_u y for the suffixes u of the words of the support of x
    for v in x.idx; t = A.suf[v]; while t != 1 && !(t in sufs); push!(sufs, t); t = A.sufnext[t]; end; end
    costR = length(need) * min(A.d, 8 * length(x.idx)); costL = length(sufs) * min(A.d, 8 * length(y.idx))
    if costR <= costL
        memo = Dict{Int32,SV{S}}(Int32(1) => x)
        for w in sort!(collect(need)); memo[w] = rmulgen(A, memo[A.parent[w]], A.letter[w]); end
        addall(A, [(y.val[k], memo[y.idx[k]]) for k in eachindex(y.idx)])
    else
        memo = Dict{Int,SV{S}}(1 => y)
        left(t) = get!(() -> lmulgen(A, A.sufletter[t], left(A.sufnext[t])), memo, t)
        addall(A, [(x.val[k], left(A.suf[x.idx[k]])) for k in eachindex(x.idx)])
    end
end

# The same products as mul, depth first: mul keeps the elements x b_w (or T_u y) of all the nodes until the sum, these
# keep those of the path from the root only (at most the length of the longest word).  15 Nov 2026: at the top of G34,
# exactly, mul((T_ζ)_c, ψ_c) for t(T_π) kept growing past 25 GB.  The same elements x b_w, T_u y as mul, the same
# choice of side, so the same exact values.
#   walkpaths(f, step, nodes, up, h0): f(t, h_t) for every node t on the paths from the root 1 to `nodes` in the tree
#   up (node -> parent), h_1 = h0 and h_t = step(h_(up[t]), t); the children in increasing order
function walkpaths(f, step, nodes, up, h0)
    need = Set{Int}()
    for v in nodes; t = Int(v); while t != 1 && !(t in need); push!(need, t); t = up[t]; end; end
    kids = Dict{Int,Vector{Int}}()
    for t in sort!(collect(need)); push!(get!(kids, up[t], Int[]), t); end
    function visit(t, h)
        f(t, h)
        for u in get(kids, t, Int[]); visit(u, step(h, u)); end
    end
    visit(1, h0)
end
# the side of mul: true for the prefixes of the words of y (x b_w), false for the suffixes of those of x (T_u y)
function mulside(A::FlatAlg, x::SV, y::SV)
    need = Set{Int32}()
    for w in y.idx; while w != 1 && !(w in need); push!(need, w); w = A.parent[w]; end; end
    sufs = Set{Int}()
    for v in x.idx; t = A.suf[v]; while t != 1 && !(t in sufs); push!(sufs, t); t = A.sufnext[t]; end; end
    length(need) * min(A.d, 8 * length(x.idx)) <= length(sufs) * min(A.d, 8 * length(y.idx))
end
# x y, depth first; the sum in an accumulator of its own, collected whenever it holds more than LIMIT term products
const MULPATH_LIMIT = 50_000_000
function mul_path(A::FlatAlg{S}, x::SV{S}, y::SV{S}) where {S}
    (iszero(x) || iszero(y)) && return zero(A)
    length(y.idx) == 1 && y.idx[1] == 1 && return scale(y.val[1], x)
    length(x.idx) == 1 && x.idx[1] == 1 && return scale(x.val[1], y)
    acc = Acc{S}(A.d); held = 0
    function add!(c, h)
        for k in eachindex(h.idx)
            addmul!(acc, h.idx[k], c, h.val[k]); S == Poly && (held += nterms(c) * nterms(h.val[k]))
        end
        if held > MULPATH_LIMIT
            s = collect!(acc); held = 0
            for k in eachindex(s.idx); addmul!(acc, s.idx[k], one(S), s.val[k]); S == Poly && (held += nterms(s.val[k])); end
        end
    end
    if mulside(A, x, y)
        coef = Dict{Int,S}(Int(y.idx[k]) => y.val[k] for k in eachindex(y.idx))
        walkpaths((w, h) -> (c = get(coef, w, nothing); c === nothing || add!(c, h)),
                  (h, w) -> rmulgen(A, h, A.letter[w]), y.idx, A.parent, x)
    else
        coef = Dict{Int,S}()
        for k in eachindex(x.idx); coef[A.suf[x.idx[k]]] = x.val[k]; end
        walkpaths((t, h) -> (c = get(coef, t, nothing); c === nothing || add!(c, h)),
                  (h, t) -> lmulgen(A, A.sufletter[t], h), keys(coef), A.sufnext, y)
    end
    collect!(acc)
end
# τ_P(x y) = the coefficient of b_1 in x y, depth first, without forming x y
function taumul(A::FlatAlg{S}, x::SV{S}, y::SV{S}) where {S}
    (iszero(x) || iszero(y)) && return zero(S)
    r = zero(S)
    if mulside(A, x, y)
        coef = Dict{Int,S}(Int(y.idx[k]) => y.val[k] for k in eachindex(y.idx))
        walkpaths((w, h) -> (c = get(coef, w, nothing); c === nothing || (r += c * coefficient(h, 1))),
                  (h, w) -> rmulgen(A, h, A.letter[w]), y.idx, A.parent, x)
    else
        coef = Dict{Int,S}()
        for k in eachindex(x.idx); coef[A.suf[x.idx[k]]] = x.val[k]; end
        walkpaths((t, h) -> (c = get(coef, t, nothing); c === nothing || (r += c * coefficient(h, 1))),
                  (h, t) -> lmulgen(A, A.sufletter[t], h), keys(coef), A.sufnext, y)
    end
    r
end

# the inverse of the basis element b_x: T_(s_l)^-1 ... T_(s_1)^-1
function basisinv(A::FlatAlg{S}, x::Integer) where {S}
    A.binv[x] === nothing || return A.binv[x]
    h = one(A)
    for s in A.words[x]; h = mulinv(A, h, A.L[s]); end
    A.binv[x] = h
end
# h = c b_x with c a unit of the ground ring: (c, x); nothing otherwise
monomial(h::SV) = length(h.idx) == 1 && isunit(h.val[1]) ? (h.val[1], Int(h.idx[1])) : nothing
# ± a single term at the group-algebra point (necessary for a unit of the recognised kinds)
probable_unit(h::SV) = count(v -> !iszero(atgroup(v)), h.val) == 1
# The form of a unit: (:basis, y) for h = c b_y; (:left, x, y) for b_x h = c b_y; (:right, x, y) for h b_x = c b_y;
# c a unit of the ground ring.  Searched in the shadow of A (a point modulo a prime) and verified exactly.
function unit_form_search(A::FlatAlg{S}, h::SV{S}) where {S}
    m = monomial(h); m === nothing || return (:basis, Int(m[2]), Int(m[2]))
    probable_unit(h) || return nothing
    for x in A.bylength
        x == 1 && continue
        m = monomial(mul(A, basis(A, x), h)); m === nothing || return (:left, x, Int(m[2]))
        m = monomial(mul(A, h, basis(A, x))); m === nothing || return (:right, x, Int(m[2]))
    end
    nothing
end
# the inverse of h from a form found in the shadow, verified exactly; nothing if the form does not hold exactly
function verify_form(A::FlatAlg{S}, h::SV{S}, form) where {S}
    kind, x, y = form
    if kind == :basis
        m = monomial(h); (m !== nothing && m[2] == y) || return nothing
        return scale(inv(m[1]), basisinv(A, y))
    elseif kind == :left
        m = monomial(mul(A, basis(A, x), h))                  # b_x h = c b_y:  h^-1 = c^-1 b_y^-1 b_x
        (m !== nothing && m[2] == y) || return nothing
        return scale(inv(m[1]), mul(A, basisinv(A, y), basis(A, x)))
    else
        m = monomial(mul(A, h, basis(A, x)))                  # h b_x = c b_y:  h^-1 = c^-1 b_x b_y^-1
        (m !== nothing && m[2] == y) || return nothing
        return scale(inv(m[1]), mul(A, basis(A, x), basisinv(A, y)))
    end
end
# the inverse of h if it is a recognised unit (cached in A.units), nothing otherwise
function find_inverse(A::FlatAlg{S}, h::SV{S}) where {S}
    iszero(h) && return nothing
    m = monomial(h)
    m === nothing || return scale(inv(m[1]), basisinv(A, m[2]))
    probable_unit(h) || return nothing
    haskey(A.units, h) && return A.units[h]
    form = unit_form_search(shadow_alg(A), toshadow(A, h))
    found = form === nothing ? nothing : verify_form(A, h, form)
    found === nothing || (mul(A, h, found) == one(A) && mul(A, found, h) == one(A)) || error("find_inverse: a wrong inverse")
    A.units[h] = found
end
# a description of a recognised unit, for the records: ± b_x, ± b_x^-1 b_y, ± b_x b_y^-1
function unit_form(A::FlatAlg{S}, h::SV{S}) where {S}
    m = monomial(h); m === nothing || return (isone(m[1]) ? "" : "-") * "b_$(m[2])"
    find_inverse(A, h) === nothing && return "?"
    form = unit_form_search(shadow_alg(A), toshadow(A, h)); form === nothing && return "?"
    kind, x, y = form; c = kind == :left ? monomial(mul(A, basis(A, x), h))[1] : monomial(mul(A, h, basis(A, x)))[1]
    (isone(c) ? "" : "-") * (kind == :left ? "b_$x^-1 b_$y" : "b_$y b_$x^-1")
end

# the relations of P on the flat form: the Hecke relation and the given braid relations for the right and the
# left multiplications on every basis element, and (T_s b) T_u = T_s (b T_u)
function test_flat(A::FlatAlg{S}, relations) where {S}
    r = A.q.r; k = A.q.k; ok = true
    for v in 1:A.d, right in (true, false)
        b = basis(A, v)
        for s in 1:A.ngens
            pw = [b]; for j in 1:k; push!(pw, right ? rmulgen(A, pw[end], s) : lmulgen(A, s, pw[end])); end
            ok &= pw[k+1] == addall(A, ((r[j], pw[j]) for j in 1:k))
        end
        for (l, rr) in relations
            ok &= (right ? rmulword(A, b, l) : lmulword(A, l, b)) == (right ? rmulword(A, b, rr) : lmulword(A, rr, b))
        end
    end
    for v in 1:A.d, s in 1:A.ngens, u in 1:A.ngens
        ok &= rmulgen(A, lmulgen(A, s, basis(A, v)), u) == lmulgen(A, s, rmulgen(A, basis(A, v), u))
    end
    ok
end
# a Gram matrix of τ_P on the basis, and its determinant over the ground ring (small algebras only; Bareiss)
function gram_det(A::FlatAlg{S}) where {S}
    G = [tau(A, mul(A, basis(A, x), basis(A, y))) for x in 1:A.d, y in 1:A.d]
    bareiss(G)
end
function bareiss(M::Matrix{S}) where {S}                  # fraction-free; exact divisions through exactdiv
    n = size(M, 1); A = copy(M); sgn = 1; prev = one(S)
    for k in 1:n-1
        piv = findfirst(i -> !iszero(A[i, k]), k:n); piv === nothing && return zero(S); piv += k - 1
        if piv != k; A[k, :], A[piv, :] = A[piv, :], A[k, :]; sgn = -sgn; end
        for i in k+1:n, j in k+1:n; A[i, j] = exactdiv(A[k, k] * A[i, j] - A[i, k] * A[k, j], prev); end
        for i in k+1:n; A[i, k] = zero(S); end
        prev = A[k, k]
    end
    sgn == 1 ? A[n, n] : -A[n, n]
end
exactdiv(a::Sh, b::Sh) = Sh(a.p * inv(b.p), iszero(b.g) ? Fp(0) : a.g * inv(b.g))      # a / b in the shadow
function exactdiv(a::Poly, b::Poly)                      # a / b when b divides a (used by Bareiss on small matrices)
    iszero(a) && return a
    isunit(b) && return b.t[1][2] == 1 ? a : -a
    # long division by the leading term, checked to be exact
    q = Term[]; rem = a; kb, cb = b.t[end]
    while !iszero(rem)
        ka, ca = rem.t[end]
        (ka >= kb && ca % cb == 0) || error("exactdiv: not divisible")
        k = ka - kb; (k & PGUARD[]) == 0 || error("exactdiv")
        all(exponents(k) .+ exponents(kb) .== exponents(ka)) || error("exactdiv: not divisible")
        c = ca ÷ cb; push!(q, (k, c)); rem = rem - Poly([(k, c)]) * b
    end
    sort!(q; by = first); Poly(q)
end
