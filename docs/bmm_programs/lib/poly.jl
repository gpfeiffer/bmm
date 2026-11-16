#############################################################################
##
##  poly.jl — PP, the polynomials of the exact proof: R' = Z[x_1, ..., x_n]
##            with packed exponents and overflow-checked Int64 coefficients
##            (Int128 for a group whose file says  coefficients = "Int128")
##
##  A term is (key, coefficient).  The exponents of the n variables are
##  packed into the UInt64 key, b = 64 ÷ n bits each (at most 16); the top
##  bit of every field is a guard, so a product whose exponent in some
##  variable reaches 2^(b-1) raises an error instead of spilling into the
##  next field.  Terms are sorted by key and have nonzero coefficients, a
##  canonical form (== is equality of the term vectors).  Coefficient
##  arithmetic raises OverflowError instead of wrapping.
##  A term takes 16 bytes and no allocation of its own (Chevie's Mvp:
##  about 115 bytes and a monomial object per term); Chevie's Mvp is used
##  only for determinants and printing (mvp).
##
#############################################################################

# the coefficient type: Int64, or Int128 if the group file named on the command line asks for it (G17, whose
# words of A carry up to 16 letters z: the proof meets coefficients of powers up to about T_z^36, beyond 2^63)
const PCOEFF = coefficient_type()             # spec.jl
const Term = Tuple{UInt64,PCOEFF}
struct PP
    t::Vector{Term}
end
const PVARS = Symbol[]                       # the variables, field i = PVARS[i]
const PBITS = Ref(16)
const PGUARD = Ref(UInt64(0))
# the variables of R', and the packing of their exponents
function set_pvars!(vars::Vector{Symbol})
    n = length(vars); n <= 64 || error("poly.jl: too many variables")
    b = n == 0 ? 16 : min(16, 64 ÷ n)
    empty!(PVARS); append!(PVARS, vars); PBITS[] = b
    PGUARD[] = reduce(|, (UInt64(1) << (i * b + b - 1) for i in 0:n-1); init = UInt64(0))
    nothing
end
# the variable v as a polynomial
function pvar(v::Symbol)
    i = findfirst(==(v), PVARS); i === nothing && error("poly.jl: unknown variable $v")
    PP([(UInt64(1) << ((i - 1) * PBITS[]), 1)])
end
function maxexp(k::UInt64)                    # the largest exponent in a key
    b = PBITS[]; m = (UInt64(1) << b) - 1; e = 0
    for i in 0:length(PVARS)-1; e = max(e, Int((k >> (i * b)) & m)); end
    e
end
# the exponents of the variables in a key
exponents(k::UInt64) = [Int((k >> ((i - 1) * PBITS[])) & ((UInt64(1) << PBITS[]) - 1)) for i in eachindex(PVARS)]

const PZERO = PP(Term[])                      # shared: term vectors are never mutated
const PONE = PP([(UInt64(0), 1)])
Base.zero(::Type{PP}) = PZERO
Base.one(::Type{PP}) = PONE
Base.zero(::PP) = PZERO
Base.one(::PP) = PONE
Base.iszero(p::PP) = isempty(p.t)
Base.isone(p::PP) = length(p.t) == 1 && p.t[1] == (UInt64(0), 1)
Base.:(==)(p::PP, q::PP) = p.t == q.t
Base.hash(p::PP, h::UInt) = hash(p.t, hash(:PP, h))
nterms(p::PP) = length(p.t)

@noinline overflow_exponent() = error("poly.jl: an exponent reached 2^$(PBITS[]-1) (packed exponent overflow)")
@inline function mulkey(a::UInt64, b::UInt64)        # the key of a product, checked against exponent overflow
    s = a + b
    (s & PGUARD[]) == 0 || overflow_exponent()
    s
end
trim(out::Vector{Term}, n) = n == length(out) ? out : out[1:n]       # no spare capacity kept

function merge_terms(a::Vector{Term}, b::Vector{Term}, sgn::Int)       # a + sgn b
    out = Vector{Term}(undef, length(a) + length(b)); i = j = 1; n = 0
    @inbounds while i <= length(a) && j <= length(b)
        ka, ca = a[i]; kb, cb = b[j]
        if ka < kb
            n += 1; out[n] = a[i]; i += 1
        elseif kb < ka
            n += 1; out[n] = (kb, sgn == 1 ? cb : Base.checked_neg(cb)); j += 1
        else
            c = sgn == 1 ? Base.checked_add(ca, cb) : Base.checked_sub(ca, cb)
            c == 0 || (n += 1; out[n] = (ka, c)); i += 1; j += 1
        end
    end
    @inbounds while i <= length(a); n += 1; out[n] = a[i]; i += 1; end
    @inbounds while j <= length(b); kb, cb = b[j]; n += 1; out[n] = (kb, sgn == 1 ? cb : Base.checked_neg(cb)); j += 1; end
    PP(trim(out, n))
end
Base.:+(p::PP, q::PP) = isempty(p.t) ? q : isempty(q.t) ? p : merge_terms(p.t, q.t, 1)
Base.:-(p::PP, q::PP) = isempty(q.t) ? p : merge_terms(p.t, q.t, -1)
Base.:-(p::PP) = PP([(k, Base.checked_neg(c)) for (k, c) in p.t])
Base.:*(s::Integer, p::PP) = s == 0 ? PZERO : PP([(k, Base.checked_mul(PCOEFF(s), c)) for (k, c) in p.t])

# the product: all products of terms, sorted, equal keys combined
function Base.:*(p::PP, q::PP)
    a = p.t; b = q.t
    (isempty(a) || isempty(b)) && return PZERO
    length(a) > length(b) && ((a, b) = (b, a))
    if length(a) == 1                                    # a monomial: the order of the keys is kept
        ka, ca = a[1]
        return PP([(mulkey(ka, kb), ca == 1 ? cb : Base.checked_mul(ca, cb)) for (kb, cb) in b])
    end
    buf = Vector{Term}(undef, length(a) * length(b)); n = 0
    @inbounds for (ka, ca) in a, (kb, cb) in b
        n += 1; buf[n] = (mulkey(ka, kb), Base.checked_mul(ca, cb))
    end
    sort!(buf; by = first)
    m = 0
    @inbounds for t in 1:n                               # combine equal keys, drop zeros
        k, c = buf[t]
        if m > 0 && buf[m][1] == k
            s = Base.checked_add(buf[m][2], c); buf[m] = (k, s)
        else
            (m > 0 && buf[m][2] == 0) && (m -= 1)
            m += 1; buf[m] = (k, c)
        end
    end
    (m > 0 && buf[m][2] == 0) && (m -= 1)
    PP(trim(buf, m))
end

# Chevie's Mvp (coefficients T): for determinants and printing
function mvp(p::PP, ::Type{T} = Int64) where T
    iszero(p) && return zero(Mvp{T,Int64})
    ts = Pair{Monomial{Int64},T}[]
    for (k, c) in p.t
        e = exponents(k)
        ms = Pair{Symbol,Int64}[PVARS[i] => e[i] for i in eachindex(e) if e[i] > 0]
        push!(ts, Monomial(ModuleElt(ms; check = true)) => T(c))
    end
    Mvp{T,Int64}(ModuleElt(ts; check = true))
end
Base.show(io::IO, p::PP) = print(io, mvp(p, Int64))

# ---- from R' back to R ------------------------------------------------------------------------------------
# R is graded: deg r_j = (k - j) ε_c for the parameter r_j of a class c of order k, and τ(T_w) is homogeneous of
# degree `degree(S, w)` (the homogeneity argument of bmm.pdf of 3 Nov, Lemmas 5.6, 5.7).  The computation sets
# every invertible parameter x_c = r_0 to 1, i.e. works in R' = R/(x_c - 1).  On each homogeneous component R_D
# the map R -> R' is injective: a monomial y^β of the image comes from the unique monomial x^α y^β of degree D,
# k_c α_c = D_c - deg_c(y^β).  So an identity between homogeneous elements of R of the same degree holds in R iff
# it holds in R', and an element of R_D is recovered from its image by this function.
function lift_to_R(S::GroupSpec, p::PP, D::Vector{Int})
    where_ = Dict{Symbol,Tuple{Int,Int}}()             # parameter => (class, weight)
    for c in 1:nclasses(S), (j, nm) in enumerate(S.params[c]); where_[Symbol(nm)] = (c, length(S.params[c]) - (j - 1)); end
    ts = Pair{Monomial{Int64},Int64}[]
    for (key, coeff) in p.t
        e = exponents(key); d = zeros(Int, nclasses(S))
        ms = Pair{Symbol,Int64}[]
        for i in eachindex(e)
            e[i] == 0 && continue
            c, wt = where_[PVARS[i]]; d[c] += wt * e[i]; push!(ms, PVARS[i] => e[i])
        end
        for c in 1:nclasses(S)
            k = length(S.params[c]); α, r = divrem(D[c] - d[c], k)
            r == 0 || error("lift_to_R: a term of degree $(d) is not congruent to the degree $(D) of the element")
            α == 0 || push!(ms, Symbol(S.params[c][1]) => α)
        end
        push!(ts, Monomial(ModuleElt(ms; check = true)) => coeff)
    end
    Mvp{Int64,Int64}(ModuleElt(ts; check = true))
end
