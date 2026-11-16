#############################################################################
##
##  modp.jl — the modular programs: Fp, the integers modulo a prime; the
##  point of R' (values of the non-invertible parameters); dense
##  determinants and solutions modulo p (blocked LU, BLAS); the flattened
##  coordinates of a vector of Λ^N.
##
#############################################################################

using LinearAlgebra

# ---- Fp: integers modulo the prime PMOD[] (set once per run) -------------------------------------------
const PMOD = Ref{Int64}(15013)
struct Fp <: Number
    v::Int64
    Fp(x::Integer, ::Val{:raw}) = new(Int64(x))
end
Fp(x::Integer) = Fp(mod(x, PMOD[]), Val(:raw))
Base.:+(a::Fp, b::Fp) = (s = a.v + b.v; Fp(s >= PMOD[] ? s - PMOD[] : s, Val(:raw)))
Base.:-(a::Fp, b::Fp) = (s = a.v - b.v; Fp(s < 0 ? s + PMOD[] : s, Val(:raw)))
Base.:-(a::Fp) = Fp(a.v == 0 ? 0 : PMOD[] - a.v, Val(:raw))
Base.:*(a::Fp, b::Fp) = Fp(a.v * b.v % PMOD[], Val(:raw))
Base.inv(a::Fp) = Fp(invmod(a.v, PMOD[]), Val(:raw))
Base.:(==)(a::Fp, b::Fp) = a.v == b.v
Base.hash(a::Fp, h::UInt) = hash(a.v, h)
Base.zero(::Type{Fp}) = Fp(0, Val(:raw)); Base.zero(::Fp) = Fp(0, Val(:raw))
Base.one(::Type{Fp}) = Fp(1, Val(:raw)); Base.one(::Fp) = Fp(1, Val(:raw))
Base.iszero(a::Fp) = a.v == 0
Base.isone(a::Fp) = a.v == 1
Base.convert(::Type{Fp}, x::Integer) = Fp(x)
symm(a::Fp) = a.v > PMOD[] ÷ 2 ? a.v - PMOD[] : a.v            # symmetric representative
Base.show(io::IO, a::Fp) = print(io, symm(a))

const DEFAULT_POINT = [11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]   # > 8, so no parameter value looks like a small integer
const DENSE_MAX = 2500      # |W| up to which the dense |W| x |W| matrices (Float64, 50 MB at 2500) are formed

# the point: values of r_1, ..., r_{k-1} class by class (r_0 = 1)
function point_values(S::GroupSpec, s::AbstractString)
    v = isempty(s) ? DEFAULT_POINT : parse.(Int, split(s, ","))
    out = Vector{Vector{Int}}(); t = 0
    for c in 1:nclasses(S)
        k = length(S.params[c]); push!(out, vcat([1], v[t+1:t+k-1])); t += k - 1
    end
    out
end

# blocked LU of the augmented [A | b] modulo P, in Float64 so that BLAS can do the trailing update: the entries
# are reduced to [0, P) with P < 2^15, a product is < 2^30 and a block sum of 64 products < 2^36 < 2^53, so every
# intermediate value is an exact integer.  Returns (det A mod P, x with A x = b, or nothing if A is singular).
function det_solve!(A::Matrix{Float64}; bs = 64)
    P = PMOD[]; n = size(A, 1); nc = size(A, 2); pf = Float64(P); sgn = 1; det = 1; k = 1
    while k <= n
        kb = min(bs, n - k + 1); kend = k + kb - 1
        for j in k:kend
            piv = 0
            @inbounds for i in j:n; if A[i, j] != 0.0; piv = i; break; end; end
            piv == 0 && return 0, nothing
            if piv != j
                @inbounds for c in 1:nc; A[j, c], A[piv, c] = A[piv, c], A[j, c]; end
                sgn = -sgn
            end
            d = Int(A[j, j]); det = Int(mod(Int128(det) * d, P)); ipv = Float64(invmod(d, P))
            @inbounds for i in j+1:n; A[i, j] = mod(A[i, j] * ipv, pf); end
            @inbounds for c in j+1:kend
                ajc = A[j, c]; ajc == 0.0 && continue
                for i in j+1:n; A[i, c] = mod(A[i, c] - A[i, j] * ajc, pf); end
            end
        end
        if kend < nc
            @inbounds for i in k+1:kend, j in k:i-1
                lij = A[i, j]; lij == 0.0 && continue
                for c in kend+1:nc; A[i, c] = mod(A[i, c] - lij * A[j, c], pf); end
            end
            if kend < n
                L21 = view(A, kend+1:n, k:kend); U12 = view(A, k:kend, kend+1:nc); Cv = view(A, kend+1:n, kend+1:nc)
                BLAS.gemm!('N', 'N', -1.0, L21, U12, 1.0, Cv)
                @inbounds for i in eachindex(Cv); Cv[i] = mod(Cv[i], pf); end
            end
        end
        k = kend + 1
    end
    det = sgn == 1 ? det : mod(-det, P)
    x = zeros(Int, n)
    for i in n:-1:1
        s = nc > n ? Int(A[i, nc]) : 0
        @inbounds for j in i+1:n; s = (s - Int(A[i, j]) * x[j]) % P; end
        x[i] = mod(s * invmod(Int(A[i, i]), P), P)
    end
    det, x
end
detmod(A::AbstractMatrix) = first(det_solve!(Float64.(A)))      # det A modulo p
sym(x::Integer) = x > PMOD[] ÷ 2 ? x - PMOD[] : x               # the symmetric representative of x in [0, p)

# flattened coordinates: (coset j, u^n) <-> (j-1) e + n + 1
function putrow!(A, r, v::SV{Lam{E,Fp}}) where E
    @inbounds for (j, x) in zip(v.idx, v.val), n in 1:E; A[r, (j-1)*E + n] = x.c[n].v; end
end
