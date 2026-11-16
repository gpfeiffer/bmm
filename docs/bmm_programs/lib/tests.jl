#############################################################################
##
##  tests.jl — the tests of bmm.pdf, Section 4, for t = E_j (can_trace, bmm.pdf §4.3), the
##             linear form that these tests prove to be the canonical trace τ_B
##
##  B = { z^(kj) u^m x } is the z^k-basis, UX = { u^m x } its level 0, X the
##  words of the basis file.  The values t(b), the blocks F_r of
##  Gram_t(B, B^-1) (Lemma 4.16), the symmetry criterion (Proposition 4.11) and
##  condition (3) of the conjecture.
##
##  The blocks are never formed entry by entry.  For b = u^a x, b' = u^c x',
##      F_r[b, b'] = t(z^(kr) u^a x x'^-1 u^-c) = f(a - c),   f(n) = t(z^(kr) u^n x x'^-1)
##  (t a trace, z central, T_u acting as u on the left), and the Hecke
##  relation u^e = Σ r_j u^j gives f(n + e) = Σ r_j f(n + j).  So the e values
##  f(0), ..., f(e-1) of each pair (x, x') determine the e x e block of the
##  pair: |X| coordinate vectors against |X| functionals (the "right factors"
##  ρ(x'^-1) φ_r), which is e^2 times less work than the entries themselves.
##
#############################################################################

# t(T_u^d h) for negative d from f = (t(h), ..., t(T_u^{e-1} h)) and u^e = Σ r_k u^k:  f(d) = f(d+e) - Σ_{k≥1} r_k f(d+k)
function value_at_power(f::AbstractVector{K}, d::Int, r::Vector{K}) where K
    e = length(f); d >= 0 && return f[d+1]
    g = Vector{K}(undef, e - d); for t in 0:e-1; g[t-d+1] = f[t+1]; end
    for t in -1:-1:d
        s = g[t+e-d+1]
        for k in 1:e-1; iszero(r[k+1]) || (s -= r[k+1] * g[t+k-d+1]); end
        g[t-d+1] = s
    end
    g[1]
end

# t(b) for all b in B: vals[i][j+1, m+1] = t(z^(kj) u^m x_i); and the number of b with t(b) ≠ δ_{b,1}
basis_values(T, X; kw...) = trace_table(T, X, [shifted(f) for f in T.φ]; kw...)
wrong_basis_values(vals, ::Type{K}) where K =
    sum(count(v[j, m] != (i == 1 && j == 1 && m == 1 ? one(K) : zero(K)) for j in axes(v, 1), m in axes(v, 2)) for (i, v) in vals)

# the block F_r in reduced form (see the header): the right factors ρ(x'^-1) φ_r, shifted
block_factors(T, X, r::Int; progress = nothing) = [shifted(f) for f in functional(T, [-reverse(x) for x in X]; level = r, progress = progress)]
# the values of trace_table as an array P[i, i', d+1] = f(d) of the pairs (x_i, x_i')
function block_array(vals, nX::Int, E::Int, ::Type{K}) where K
    P = Array{K,3}(undef, nX, nX, E)
    for (i, v) in vals; P[i, :, :] = v; end
    P
end
struct FView{K} <: AbstractMatrix{K}              # the block as a matrix, computed on demand from P[i, i', d+1] = f(d)
    P::Array{K,3}
    r::Vector{K}                                   # the Hecke relation of u: r_0, ..., r_{e-1}
end
Base.size(F::FView) = (size(F.P, 1) * size(F.P, 3), size(F.P, 2) * size(F.P, 3))
function Base.getindex(F::FView, p::Int, q::Int)
    e = size(F.P, 3); i, a = divrem(p - 1, e); j, b = divrem(q - 1, e)
    value_at_power(view(F.P, i + 1, j + 1, :), a - b, F.r)
end

# the words w_i of the tree, from its edges (i, k, g): w_k = w_i g
function tree_words(edges)
    words = [Int[] for _ in 1:length(edges)+1]
    for (i, k, g) in edges; words[k] = vcat(words[i], g); end
    words
end
# Proposition 4.11 on the basis A: for every generator g, the number of a in A with t(T_g a) ≠ t(a T_g)
function symmetry_failures(T, edges)
    S = T.H.S; A = level0(S, tree_words(edges))                  # the words u^m w_i of A
    [count(trace(T, [vcat(g, a) for a in A]) .!= trace(T, [vcat(a, g) for a in A])) for g in 1:ngens(S)]
end

# Condition (3) of the conjecture: t(π) and the number of b ≠ 1 in B with t(b^-1 π) ≠ 0.  For b = z^(kj) u^m x,
# t(b^-1 π) = t(u^-m x^-1 z^(q - kj)) = g(-m), g(d) = t(u^d x^-1 z^(q - kj)), with the functional of z^(q - kj).
function condition3(T::Trace{E,K}, X) where {E,K}
    S = T.H.S; Z = zletter(S); k = S.zstep; nl = S.zlevels; φ = T.φ
    ψ = Vector{Functional{E,K}}(undef, nl)
    for j in 0:nl-1
        if S.pipower == k * nl                           # π = z^(k nl): the levels φ_j themselves, shifted by one
            ψ[j+1] = j == 0 ? colword(T, φ[nl], fill(Z, k)) : φ[nl-j+1]
        else
            ψ[j+1] = colword(T, φ[1], fill(Z, S.pipower - k * j))
        end
    end
    r = copy(LAMRED[]::Vector{K})
    G = trace_table(T, [-reverse(x) for x in X], [shifted(p) for p in ψ])
    taupi = zero(K); nonzero = 0
    for (i, vals) in G, j in 0:nl-1, m in 0:E-1
        t = value_at_power(view(vals, j + 1, :), -m, r)
        if i == 1 && j == 0 && m == 0                    # b = 1 (X[1] is the identity)
            taupi = t
        elseif !iszero(t)
            nonzero += 1
        end
    end
    taupi, nonzero
end

# strongly connected components of the support of a square matrix (det F_0 factorises over them)
function strongly_connected_components(F::AbstractMatrix)
    n = size(F, 1); adj = [[j for j in 1:n if j != i && !iszero(F[i, j])] for i in 1:n]
    idx = zeros(Int, n); low = zeros(Int, n); on = falses(n); st = Int[]; c = Ref(0); comps = Vector{Vector{Int}}()
    function vis(v)
        c[] += 1; idx[v] = low[v] = c[]; push!(st, v); on[v] = true
        for w in adj[v]
            if idx[w] == 0
                vis(w); low[v] = min(low[v], low[w])
            elseif on[w]
                low[v] = min(low[v], idx[w])
            end
        end
        if low[v] == idx[v]
            cc = Int[]
            while true; w = pop!(st); on[w] = false; push!(cc, w); w == v && break; end
            push!(comps, sort!(cc))
        end
    end
    for v in 1:n; idx[v] == 0 && vis(v); end
    comps
end

# ---- the tests as they appear in the records ("testing ... true" lines; `testing` is in report.jl) ----------
# the defining relations of H on the complete table
function test_relations(H; progress = nothing)
    labels, fails = check_relations(H; progress = progress)
    for (lab, f) in zip(labels, fails)
        testing(lab, f == 0; note = f == 0 ? "" : "fails on $f rows")
    end
end
# the criterion of Proposition 4.11 on the basis A, one line per generator
function test_symmetry(T, edges)
    S = T.H.S; bad = symmetry_failures(T, edges)
    for g in 1:ngens(S)
        s = S.letters[g]
        testing("t(a T_$s) = t(T_$s a) for all a in A", bad[g] == 0; note = bad[g] == 0 ? "" : "$(bad[g]) failures")
    end
end
