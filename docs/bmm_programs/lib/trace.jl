#############################################################################
##
##  trace.jl — the canonical trace τ, computed from the coset table of A
##
##  T = MakeTrace(H) sets up τ from the trace "J,i,m" of the group file
##  (the triple of E_j, bmm.pdf §4.3; Table 1 lists the non-trivial ones of G17, G18, G19, G27, and the
##  former ones of G16, G21): τ(T_z^(kJ) h) is the coefficient of T_u^m T_(w_i)
##  in h (k = zstep), that is, τ(T_z^(kJ) h) = φ_J(e_1 ρ(h)) for the
##  coordinate functional φ_J.
##      can_trace(T, w)    THE CANONICAL TRACE τ(T_w) in R, for a word w or
##                         a list of words (modulo p: the value at the point)
##  The programs compute in the coefficient ring K of the table, R' (the
##  invertible parameters 1) or F_p:
##      trace(T, w)        τ(T_w) in K, for a word w or a list of words
##      trace(T, v)        τ(h) in K, for h with coordinates v in the basis A
##      functional(T, w)   the functional h ↦ τ(h T_w), so that
##                         τ(h h') = pairing(v, functional(T, w'))
##      trace_table(T, words, factors)   many values at once (below)
##      T.φ[j+1]           the functional h ↦ τ(T_z^(kj) h), j = 0, ..., d-1,
##                         built when first used (can_trace uses only φ_0)
##
#############################################################################

# a functional on Λ^N in A-coordinates: coset j => (f(e_j), f(u e_j), ..., f(u^{e-1} e_j))
const Functional{E,K} = Dict{Int32,NTuple{E,K}}

# the trace "J,i,m": φ_J = the coefficient of u^m e_i
function trace_functional(H::CosetTable{E,K}, trace::AbstractString) where {E,K}
    J, i, m = parse_trace(trace)
    J, Functional{E,K}(Int32(i) => ntuple(a -> a == m + 1 ? one(K) : zero(K), E))
end

# the trace τ(z^(kJ) h) = φ_J(e_1 ρ(h)) and its levels φ_j, with the transposed table for the action of H
# on functionals: (ρ(g) f)(v) = f(v T_g)
# the levels φ_j : h ↦ τ(z^(kj) h), j = 0, ..., d-1, as a vector whose entry φ[j+1] is computed when it is
# first used, from φ_J: φ_(j-1) = φ_j ∘ ρ(T_z^-k) below J, φ_(j+1) = φ_j ∘ ρ(T_z^k) above J.  can_trace needs
# only φ_0, which is φ_J itself when J = 0 (A quasi-symmetric); the proof uses them all.
const Transposed{E,K} = Vector{Vector{Vector{Tuple{Int32,Lam{E,K}}}}}   # TR[column(g)][j] = the (i, x), x the coefficient of e_j in e_i T_g
struct Levels{E,K} <: AbstractVector{Functional{E,K}}
    H::CosetTable{E,K}
    TR::Transposed{E,K}
    J::Int
    φ::Vector{Union{Nothing,Functional{E,K}}}        # nothing: not computed yet
end
Base.size(L::Levels) = size(L.φ)
Base.IndexStyle(::Type{<:Levels}) = IndexLinear()
# φ_j, computed from its neighbour towards J on first use
function Base.getindex(L::Levels{E,K}, i::Int) where {E,K}
    if L.φ[i] === nothing
        S = L.H.S; Z = zletter(S); k = S.zstep
        L.φ[i] = i - 1 < L.J ? colword(L, L[i+1], fill(-Z, k)) : colword(L, L[i-1], fill(Z, k))
    end
    L.φ[i]::Functional{E,K}
end

struct Trace{E,K}
    H::CosetTable{E,K}
    J::Int
    TR::Transposed{E,K}
    φ::Levels{E,K}                                       # φ_j : h ↦ τ(z^(kj) h), j = 0, ..., d-1
end
# the trace from φ_J; the other levels φ_j are φ_J moved by powers of T_z^±k
function MakeTrace(H::CosetTable{E,K}, J::Int, φJ::Functional{E,K}) where {E,K}
    S = H.S; N = H.N
    0 <= J < S.zlevels || error("the level J = $J of the trace is not in 0, ..., zlevels - 1 = $(S.zlevels - 1)")
    function transposed(R)                             # for each j, the (i, x) with x the coefficient of e_j in e_i T_g
        T = [Tuple{Int32,Lam{E,K}}[] for _ in 1:N]
        for i in 1:N, (j, x) in zip(R[i].idx, R[i].val); push!(T[j], (Int32(i), x)); end
        T
    end
    TR = [transposed(R) for R in H.rows]
    φ = Vector{Union{Nothing,Functional{E,K}}}(nothing, S.zlevels); φ[J+1] = φJ
    Trace{E,K}(H, J, TR, Levels{E,K}(H, TR, J, φ))
end
# the trace of the group file (or another "J,i,m")
function MakeTrace(H::CosetTable, trace::AbstractString = H.S.trace)
    isempty(trace) && error("no trace in the group file (programs/zbasis_modular.jl proposes one)")
    MakeTrace(H, trace_functional(H, trace)...)
end
# load_trace("G16") or load_trace("G16/group16.toml"): the trace of any group.  For the engine tower (G31–G34)
# the driver of the engine is loaded and its build_trace(S) returns a CanTrace (lib/cantrace.jl), which
# can_trace accepts as well.
function load_trace(file::AbstractString; kw...)
    S = read_spec(file)
    S.engine == "cyclic" && return MakeTrace(HeckeCRG(file; kw...))
    Base.include(Main, joinpath(@__DIR__, S.engine, "driver.jl"))      # at run time: a path from @__DIR__
    Base.invokelatest(S -> Main.build_trace(S; kw...), S)
end

# f ∘ ρ(T_g) and f ∘ ρ(T_w): the functionals v ↦ f(v T_g), v ↦ f(v T_w)
function colapply(T::Union{Trace{E,K},Levels{E,K}}, f, g) where {E,K}
    TT = T.TR[column(T.H.S, g)]; acc = Dict{Int32,Vector{K}}()
    for (j, fj) in f
        ψ = fj
        for m in 1:E
            for (i, x) in TT[j]; o = get!(() -> fill(zero(K), E), acc, i); o[m] += lpair(x, ψ); end
            m < E && (ψ = ut(ψ))
        end
    end
    Functional{E,K}(i => ntuple(m -> o[m], E) for (i, o) in acc if !all(iszero, o))
end
function colword(T::Union{Trace,Levels}, f, w)
    for g in reverse(w); f = colapply(T, f, g); end
    f
end

# f(v), the value of a functional on a coordinate vector
function pairing(v::SV, f::Functional{E,K}) where {E,K}
    s = zero(K)
    for (j, x) in zip(v.idx, v.val); fj = get(f, j, nothing); fj === nothing || (s += lpair(x, fj)); end
    s
end
# τ(z^(k·level) h) for h given by its coordinates v, by a word w, or for every word of a list (along a trie)
function trace(T::Trace{E,K}, x; level = 0, progress = nothing) where {E,K}
    x isa SV && return pairing(x, T.φ[level+1])
    x isa Vector{Int} && return pairing(coordinates(T.H, x), T.φ[level+1])
    out = Vector{K}(undef, length(x))
    along_words(x, basic_vec(T.H, 1), (v, g) -> vec_under_mat(T.H, v, g); progress = progress,
                visit = (i, v) -> (out[i] = pairing(v, T.φ[level+1])))
    out
end
# the functional h ↦ τ(z^(k·level) h T_w), for a word w or for every word of a list
functional(T::Trace, w; level = 0, progress = nothing) = w isa Vector{Int} ? colword(T, T.φ[level+1], w) :
    along_words([reverse(x) for x in w], T.φ[level+1], (f, g) -> colapply(T, f, g); progress = progress)

# many values at once.  Since e_1 T_u = u e_1, the coordinates of T_u^d h are u^d times those of h, so
# τ(T_u^d h h') = (u^d v) · f = v · ut^d f: a functional is stored with its e shifts ut^d (shifted(f)), and
# trace_table(T, words, factors; start = v_0) gives for every word w_i and factor f_j the e values
#     done[i][j, d+1] = τ(T_u^d h_0 T_{w_i} h'_j),  d = 0, ..., e-1   (v_0 the coordinates of h_0, default 1).
function utpow(t, n)                                   # ut^n t
    for _ in 1:n; t = ut(t); end
    t
end
function shifted(f::Functional{E,K}) where {E,K}
    ks = sort!(collect(keys(f)))
    (idx = ks, val = [ntuple(d -> utpow(f[j], d - 1), E) for j in ks])
end
function trace_table(T::Trace{E,K}, words, factors; start = basic_vec(T.H, 1), progress = nothing) where {E,K}
    N = T.H.N; nc = length(factors); colpos = zeros(Int32, N, nc); rowpos = zeros(Int32, N); accs = Vector{K}(undef, E)
    for (j, c) in enumerate(factors), (t, k) in enumerate(c.idx); colpos[k, j] = t; end
    done = Dict{Int,Matrix{K}}()
    along_words(words, start, (v, g) -> vec_under_mat(T.H, v, g); visit = function (t, r)
        for (p, k) in enumerate(r.idx); rowpos[k] = p; end
        vals = Matrix{K}(undef, nc, E)
        for j in 1:nc
            c = factors[j]; fill!(accs, zero(K))
            if length(r.idx) <= length(c.idx)
                for (p, k) in enumerate(r.idx)
                    q = colpos[k, j]; q == 0 && continue
                    for d in 1:E; accs[d] += lpair(r.val[p], c.val[q][d]); end
                end
            else
                for (q, k) in enumerate(c.idx)
                    p = rowpos[k]; p == 0 && continue
                    for d in 1:E; accs[d] += lpair(r.val[p], c.val[q][d]); end
                end
            end
            vals[j, :] = accs
        end
        for k in r.idx; rowpos[k] = 0; end
        done[t] = vals
        progress === nothing || progress(length(done))
    end)
    done
end

# THE CANONICAL TRACE τ(T_w) in R, for a word w or a list of words: trace(T, w) computes it in R', and the
# invertible parameters are restored by homogeneity (τ(T_w) has degree w(T_w): the homogeneity argument of
# bmm.pdf of 3 Nov, Lemma 5.7).  Modulo p: the value at the point.
can_trace(T::Trace, w::Vector{Int}) = coeftype(T.H) == Fp ? trace(T, w) : lift_to_R(T.H.S, trace(T, w), degree(T.H.S, w))
can_trace(T::Trace, ws::Vector{Vector{Int}}) = coeftype(T.H) == Fp ? trace(T, ws) :
    [lift_to_R(T.H.S, x, degree(T.H.S, w)) for (w, x) in zip(ws, trace(T, ws))]
