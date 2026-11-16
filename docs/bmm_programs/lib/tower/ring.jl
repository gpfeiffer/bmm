#############################################################################
##
##  ring.jl — the ground rings
##
##    Poly  the exact ring R' = Z[x_1, ..., x_n] (n ≤ 3): sparse polynomials
##          with the exponents packed into a UInt64 key (20 bits per variable,
##          a guard bit per field) and overflow-checked Int64 coefficients.
##          An overflow of a coefficient or of an exponent raises an error:
##          a run that finishes has computed exactly.
##    Fp    integers modulo the prime PMOD[].
##    Sh    the modular shadow F_p × F_p: the value at a point (x_i = point_i)
##          and the value at the group-algebra point (x_i = 0).  The second
##          component only feeds the heuristic that filters candidate units.
##
##  A Hecke relation T^k = r_{k-1} T^{k-1} + ... + r_1 T + r_0 is a Hecke{S}
##  with r = [r_0, ..., r_{k-1}] and r_0 = 1 (we work over R').  The names of
##  the r_j are those of the group file (e0, e1 for G31; c0, c1, c2 for G32).
##
#############################################################################

# ---- Fp ---------------------------------------------------------------------------------------------------
const PMOD = Ref{Int64}(15013)
struct Fp
    v::Int64
    Fp(v::Int64, ::Val{:raw}) = new(v)
end
Fp(x::Integer) = Fp(mod(Int64(x), PMOD[]), Val(:raw))
Base.:+(a::Fp, b::Fp) = (s = a.v + b.v; Fp(s >= PMOD[] ? s - PMOD[] : s, Val(:raw)))
Base.:-(a::Fp, b::Fp) = (s = a.v - b.v; Fp(s < 0 ? s + PMOD[] : s, Val(:raw)))
Base.:-(a::Fp) = Fp(a.v == 0 ? 0 : PMOD[] - a.v, Val(:raw))
Base.:*(a::Fp, b::Fp) = Fp(a.v * b.v % PMOD[], Val(:raw))
Base.inv(a::Fp) = Fp(invmod(a.v, PMOD[]), Val(:raw))
Base.:(==)(a::Fp, b::Fp) = a.v == b.v
Base.hash(a::Fp, h::UInt) = hash(a.v, h)
Base.zero(::Type{Fp}) = Fp(0, Val(:raw)); Base.zero(::Fp) = Fp(0, Val(:raw))
Base.one(::Type{Fp}) = Fp(1, Val(:raw));  Base.one(::Fp) = Fp(1, Val(:raw))
Base.iszero(a::Fp) = a.v == 0
Base.isone(a::Fp) = a.v == 1
symm(a::Fp) = a.v > PMOD[] ÷ 2 ? a.v - PMOD[] : a.v                   # the symmetric representative
Base.show(io::IO, a::Fp) = print(io, symm(a))

# ---- Sh ---------------------------------------------------------------------------------------------------
struct Sh
    p::Fp                                   # at the point
    g::Fp                                   # at the group-algebra point
end
Sh(n::Integer) = Sh(Fp(n), Fp(n))
Base.zero(::Type{Sh}) = Sh(0); Base.zero(::Sh) = Sh(0)
Base.one(::Type{Sh}) = Sh(1);  Base.one(::Sh) = Sh(1)
Base.iszero(c::Sh) = iszero(c.p) && iszero(c.g)
Base.isone(c::Sh) = isone(c.p) && isone(c.g)
Base.:(==)(c::Sh, d::Sh) = c.p == d.p && c.g == d.g
Base.hash(c::Sh, h::UInt) = hash(c.g.v, hash(c.p.v, h))
Base.:+(c::Sh, d::Sh) = Sh(c.p + d.p, c.g + d.g)
Base.:-(c::Sh, d::Sh) = Sh(c.p - d.p, c.g - d.g)
Base.:-(c::Sh) = Sh(-c.p, -c.g)
Base.:*(c::Sh, d::Sh) = Sh(c.p * d.p, c.g * d.g)
Base.:*(n::Integer, c::Sh) = Sh(n) * c
Base.show(io::IO, c::Sh) = print(io, c.p, "|", c.g)
isunit(c::Sh) = c.p == c.g && (isone(c.g) || isone(-c.g))      # ±1: the units of R'
Base.inv(c::Sh) = isunit(c) ? c : error("not a unit")
atgroup(c::Sh) = c.g                        # the value at the group-algebra point
star(c::Sh) = error("the involution r -> r^* is not defined at a point")

# ---- Poly -------------------------------------------------------------------------------------------------
const Term = Tuple{UInt64,Int64}
struct Poly
    t::Vector{Term}                         # sorted by key; no zero coefficient
end
const PVARS = Symbol[]
const PBITS = 20
const PGUARD = Ref(UInt64(0))
const PSTAR = Ref{Tuple{Vector{Int},Vector{Int}}}((Int[], Int[]))     # the involution: variable i -> sign_i * variable perm_i
# the variables of R', the packing of their exponents, and the involution
function set_variables!(vars::Vector{Symbol}; star_perm = collect(1:length(vars)), star_sign = fill(-1, length(vars)))
    length(vars) <= 3 || error("ring.jl: at most 3 variables")
    empty!(PVARS); append!(PVARS, vars)
    PGUARD[] = reduce(|, (UInt64(1) << (i * PBITS + PBITS - 1) for i in 0:length(vars)-1); init = UInt64(0))
    PSTAR[] = (star_perm, star_sign)
    nothing
end
variable(i::Int) = Poly([(UInt64(1) << ((i - 1) * PBITS), 1)])                                # x_i
# the exponents of the variables in a key
exponents(k::UInt64) = [Int((k >> ((i - 1) * PBITS)) & ((UInt64(1) << PBITS) - 1)) for i in eachindex(PVARS)]
@noinline exponent_overflow() = error("ring.jl: an exponent reached 2^$(PBITS-1)")
@inline function mulkey(a::UInt64, b::UInt64)        # the key of a product, checked against exponent overflow
    s = a + b
    (s & PGUARD[]) == 0 || exponent_overflow()
    s
end
const PZERO = Poly(Term[])
const PONE = Poly([(UInt64(0), 1)])
Base.zero(::Type{Poly}) = PZERO; Base.zero(::Poly) = PZERO
Base.one(::Type{Poly}) = PONE;   Base.one(::Poly) = PONE
Base.iszero(p::Poly) = isempty(p.t)
Base.isone(p::Poly) = length(p.t) == 1 && p.t[1] == (UInt64(0), 1)
Base.:(==)(p::Poly, q::Poly) = p.t == q.t
Base.hash(p::Poly, h::UInt) = hash(p.t, hash(:Poly, h))
nterms(p::Poly) = length(p.t)
isunit(p::Poly) = length(p.t) == 1 && p.t[1][1] == 0 && abs(p.t[1][2]) == 1      # ±1
Base.inv(p::Poly) = isunit(p) ? p : error("not a unit")
atgroup(p::Poly) = (isempty(p.t) || p.t[1][1] != 0) ? 0 : p.t[1][2]       # the constant term
maxcoef(p::Poly) = maximum(abs(c) for (_, c) in p.t; init = 0)                  # the largest |coefficient|

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
    Poly(n == length(out) ? out : out[1:n])
end
Base.:+(p::Poly, q::Poly) = isempty(p.t) ? q : isempty(q.t) ? p : merge_terms(p.t, q.t, 1)
Base.:-(p::Poly, q::Poly) = isempty(q.t) ? p : merge_terms(p.t, q.t, -1)
Base.:-(p::Poly) = Poly([(k, Base.checked_neg(c)) for (k, c) in p.t])
Base.:*(s::Integer, p::Poly) = s == 0 ? PZERO : s == 1 ? p : Poly([(k, Base.checked_mul(Int64(s), c)) for (k, c) in p.t])

# the terms of a product, pushed on a list; combine! sorts and adds them up
@inline function pushprod!(a::Vector{Term}, p::Poly, q::Poly)
    @inbounds for (k1, c1) in p.t, (k2, c2) in q.t; push!(a, (mulkey(k1, k2), Base.checked_mul(c1, c2))); end
end
# When the keys lie in a short range (R' = Z[e1]: a key is the exponent of e1), they are added up in a dense
# buffer indexed by key - lo instead of sorted: the same terms in the same order (increasing keys, no zero
# coefficient), with the same overflow checks (an overflow leaves DENSE clean and raises an error).  DENSE is all
# zeros between two calls (one thread).
const DENSE = Int64[]
function combine!(a::Vector{Term})
    n = length(a)
    n == 0 && return Poly(Term[])
    lo = hi = @inbounds a[1][1]
    @inbounds for i in 2:n; k = a[i][1]; k < lo && (lo = k); k > hi && (hi = k); end
    if hi - lo < UInt64(4n + 64)
        m = Int(hi - lo) + 1; d = DENSE
        if length(d) < m; l0 = length(d); resize!(d, m); fill!(view(d, l0+1:m), 0); end
        ovf = false
        @inbounds for (k, c) in a; j = Int(k - lo) + 1; v, o = Base.Checked.add_with_overflow(d[j], c); d[j] = v; ovf |= o; end
        ovf && (fill!(view(d, 1:m), 0); throw(OverflowError("ring.jl: a coefficient overflowed Int64")))
        nz = 0
        @inbounds for j in 1:m; d[j] == 0 || (nz += 1); end
        out = Vector{Term}(undef, nz); t = 0
        @inbounds for j in 1:m
            c = d[j]; c == 0 && continue
            t += 1; out[t] = (lo + UInt64(j - 1), c); d[j] = 0
        end
        empty!(a); return Poly(out)
    end
    sort!(a; by = first); out = Term[]; i = 1
    @inbounds while i <= n
        k, c = a[i]; i += 1
        while i <= n && a[i][1] == k; c = Base.checked_add(c, a[i][2]); i += 1; end
        c == 0 || push!(out, (k, c))
    end
    empty!(a); Poly(out)
end
# the product (a monomial factor keeps the order of the keys; otherwise all products, sorted and combined)
function Base.:*(p::Poly, q::Poly)
    (isempty(p.t) || isempty(q.t)) && return PZERO
    if length(p.t) == 1                                  # a monomial keeps the order of the keys
        kp, cp = p.t[1]
        return Poly([(mulkey(kp, kq), cp == 1 ? cq : Base.checked_mul(cp, cq)) for (kq, cq) in q.t])
    elseif length(q.t) == 1
        kq, cq = q.t[1]
        return Poly([(mulkey(kp, kq), cq == 1 ? cp : Base.checked_mul(cp, cq)) for (kp, cp) in p.t])
    end
    buf = Term[]; sizehint!(buf, length(p.t) * length(q.t)); pushprod!(buf, p, q); combine!(buf)
end
# the involution of R': x_i -> sign_i x_perm(i)
function star(p::Poly)
    perm, sgn = PSTAR[]; out = Term[]
    for (k, c) in p.t
        e = exponents(k); key = UInt64(0); s = 1
        for i in eachindex(e)
            e[i] == 0 && continue
            key += UInt64(e[i]) << ((perm[i] - 1) * PBITS); isodd(e[i]) && sgn[i] < 0 && (s = -s)
        end
        push!(out, (key, s * c))
    end
    sort!(out; by = first); Poly(out)
end
function Base.show(io::IO, p::Poly)
    iszero(p) && return print(io, "0")
    first = true
    for (k, c) in Iterators.reverse(p.t)
        e = exponents(k); mon = join([e[i] == 1 ? string(PVARS[i]) : "$(PVARS[i])^$(e[i])" for i in eachindex(e) if e[i] > 0], "*")
        sgn = c < 0 ? "-" : (first ? "" : "+"); ac = abs(c)
        print(io, first ? sgn : " $sgn ", (ac == 1 && !isempty(mon)) ? "" : string(ac), (ac == 1 || isempty(mon)) ? "" : "*", mon)
        first = false
    end
end

const Scalar = Union{Poly,Sh}

# ---- the Hecke relation ------------------------------------------------------------------------------------
struct Hecke{S}
    k::Int
    r::Vector{S}                            # T^k = Σ_j r[j+1] T^j, r[1] = r_0 = 1
    name::String
end
# exact: T^k = r_{k-1} T^{k-1} + ... + r_1 T + 1 over R' = Z[r_1, ..., r_{k-1}]; vars = the names of r_1, ..., r_{k-1}
# and r0 the name of r_0 (from the group file: [:e1], :e0 for G31; [:c1, :c2], :c0 for G32).  The involution
# r -> r^* of R' (the image of T_s -> T_s^-1 on the coefficients) is r_j -> -r_(k-j).
const R0NAME = Ref(:r0)
const RNAMES = String[]                     # the names of r_1, ..., r_(k-1), for the records (exact and modular)
function hecke_exact(k::Int, vars::Vector{Symbol}, r0::Symbol)
    length(vars) == k - 1 || error("hecke_exact: $(k - 1) parameter names needed, got $vars")
    set_variables!(vars; star_perm = reverse(collect(1:k-1)), star_sign = fill(-1, k - 1))
    R0NAME[] = r0; empty!(RNAMES); append!(RNAMES, string.(vars))
    r = vcat([one(Poly)], [variable(j) for j in 1:k-1])
    Hecke{Poly}(k, r, "T^$k = " * join(["$(vars[j]) T" * (j > 1 ? "^$j" : "") for j in k-1:-1:1], " + ") * " + 1")
end
# shadow at the point r_j = point[j] modulo p (names: the names of r_1, ..., r_{k-1}, for the text only)
function hecke_shadow(k::Int, p::Integer, point::Vector{Int}, names::Vector{String})
    PMOD[] = p; empty!(RNAMES); append!(RNAMES, names)
    length(point) >= k - 1 || error("hecke_shadow: the point needs $(k - 1) values")
    r = vcat([Sh(1)], [Sh(Fp(point[j]), Fp(0)) for j in 1:k-1])
    Hecke{Sh}(k, r, "T^$k = " * join(["$(names[j]) T" * (j > 1 ? "^$j" : "") for j in k-1:-1:1], " + ") * " + 1;  p = $p, " *
              join(["$(names[j]) = $(point[j])" for j in 1:k-1], ", "))
end
