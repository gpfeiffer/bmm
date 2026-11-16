#############################################################################
##
##  lambda.jl — the parabolic ring  Λ = K[u]/(u^e - r_{e-1} u^{e-1} - ... - r_1 u - 1)
##
##  Λ is the algebra H(W_0) ⊗ R' of bmm.pdf, §3.2 ("extending scalars from
##  R(P) to R(W)", P = W_0 = <u>), with its basis 1, T_u, ..., T_u^{e-1} (the fixed basis
##  of H(W_0) of Definition 3.5, the BFS_o basis candidate B_P · T_o); it is
##  the ring of coefficients of the coset table (hecke.jl).  u = T_u is the
##  parabolic generator, of order e, and r_0 = 1 because all programs work
##  over R', the ring in which every invertible parameter is 1.  K is either
##      Fp            integers modulo a prime P (the modular programs; modp.jl), or
##      PP            the polynomials of R' (the exact proof; poly.jl).
##  An element is Lam{e,K}: the coefficients of 1, u, ..., u^{e-1}.
##  The reduction coefficients r_0, ..., r_{e-1} are installed once per run
##  by set_lambda!(r).
##
#############################################################################
# ---- Λ -------------------------------------------------------------------------------------------------
struct Lam{E,K}
    c::NTuple{E,K}
end
const LAMRED = Ref{Any}(nothing)                 # Vector{K}: r_0, ..., r_{e-1}

# install the reduction coefficients r_0 = 1, r_1, ..., r_{e-1}
function set_lambda!(r::Vector)
    isone(r[1]) || error("lambda.jl: r_0 must be 1 (work over R')")
    LAMRED[] = r
    nothing
end

# 0, 1, u and the scalar s as elements of Λ
@inline lzero(::Type{Lam{E,K}}) where {E,K} = Lam{E,K}(ntuple(_ -> zero(K), E))
@inline lone(::Type{Lam{E,K}}) where {E,K} = Lam{E,K}(ntuple(i -> i == 1 ? one(K) : zero(K), E))
@inline lu(::Type{Lam{E,K}}) where {E,K} = Lam{E,K}(ntuple(i -> i == 2 ? one(K) : zero(K), E))
@inline lscal(s::K, ::Type{Lam{E,K}}) where {E,K} = Lam{E,K}(ntuple(i -> i == 1 ? s : zero(K), E))
Base.zero(::Type{L}) where {L<:Lam} = lzero(L)
Base.zero(x::Lam) = lzero(typeof(x))
Base.one(::Type{L}) where {L<:Lam} = lone(L)
Base.iszero(x::Lam) = all(iszero, x.c)
Base.:(==)(x::Lam, y::Lam) = x.c == y.c
Base.:+(x::Lam{E,K}, y::Lam{E,K}) where {E,K} = Lam{E,K}(ntuple(i -> x.c[i] + y.c[i], E))
Base.:-(x::Lam{E,K}, y::Lam{E,K}) where {E,K} = Lam{E,K}(ntuple(i -> x.c[i] - y.c[i], E))
Base.:-(x::Lam{E,K}) where {E,K} = Lam{E,K}(ntuple(i -> -x.c[i], E))
Base.:*(s::K, x::Lam{E,K}) where {E,K} = Lam{E,K}(ntuple(i -> s * x.c[i], E))

# the product of Λ: the product of the polynomials in u, then u^e, ..., u^(2e-2) reduced
function Base.:*(x::Lam{E,K}, y::Lam{E,K}) where {E,K}
    r = LAMRED[]::Vector{K}
    p = Vector{K}(undef, 2 * E - 1)
    @inbounds for i in 1:2 * E - 1; p[i] = zero(K); end
    @inbounds for i in 1:E
        iszero(x.c[i]) && continue
        for j in 1:E
            iszero(y.c[j]) || (p[i+j-1] += x.c[i] * y.c[j])
        end
    end
    @inbounds for l in 2 * E - 1:-1:E+1               # u^(l-1) = Σ_k r_k u^(l-1-E+k)
        iszero(p[l]) && continue
        for k in 1:E
            iszero(r[k]) || (p[l-E+k-1] += p[l] * r[k])
        end
    end
    Lam{E,K}(ntuple(i -> p[i], E))
end

# u^-1 = u^{e-1} - r_{e-1} u^{e-2} - ... - r_1      (r_0 = 1)
function luinv(::Type{Lam{E,K}}) where {E,K}
    r = LAMRED[]::Vector{K}
    Lam{E,K}(ntuple(i -> i == E ? one(K) : -r[i+1], E))
end

# the transpose of multiplication by u on a coordinate functional φ = (φ(1), φ(u), ..., φ(u^{e-1})):
# (ut φ)(u^n) = φ(u^{n+1}), and φ(u^e) = Σ_k r_k φ(u^k)
function ut(φ::NTuple{E,K}) where {E,K}
    r = LAMRED[]::Vector{K}
    last = zero(K)
    @inbounds for k in 1:E; iszero(r[k]) || (last += r[k] * φ[k]); end
    ntuple(i -> i < E ? φ[i+1] : last, E)
end
# <x, φ> = Σ_n x_n φ(u^n)
@inline function lpair(x::Lam{E,K}, φ::NTuple{E,K}) where {E,K}
    s = zero(K)
    @inbounds for n in 1:E; (iszero(x.c[n]) || iszero(φ[n])) || (s += x.c[n] * φ[n]); end
    s
end

function Base.show(io::IO, x::Lam{E,K}) where {E,K}
    iszero(x) && return print(io, "0")
    parts = String[]
    for (k, c) in enumerate(x.c)
        iszero(c) && continue
        push!(parts, k == 1 ? "($c)" : k == 2 ? "($c)u" : "($c)u^$(k-1)")
    end
    print(io, join(parts, " + "))
end
