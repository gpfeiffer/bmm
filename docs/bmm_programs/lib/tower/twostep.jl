#############################################################################
##
##  twostep.jl — the module Tower: the engine of G31, G32, G33, G34 (bmm.pdf, Section 5)
##
##  Loaded by lib/tower/driver.jl, which runs the steps; the records are written through
##  lib/report.jl (say, testing, stage, ...), so the module imports those functions from Main.
##  The files of the module:
##    ring.jl    the ground rings: Poly (R' = Z[r_1, ..., r_{k-1}], r_0 = 1, exact), Fp, Sh (mod p)
##    alg.jl     H(P) as a flat algebra over the ground ring: basis B_P, products, τ_P, units
##    coset.jl   the coset table of H(W) over H(P), its rows and columns, and the relations on the table
##    setrow.jl  the setRow procedure of bmm.pdf §3.3 that fills the table, its programs and their execution
##    twostep.jl (this file) the trace in two steps t = τ_P ∘ E and the tests of Proposition 5.3
##
##  H(W) = ⊕_n H(P) x_n; E(Σ p_n x_n) = p_1; t = τ_P ∘ E, the coefficient of
##  1 on the parabolic basis B = { b x_n }.  Columns ψ in H(P)^N are the left
##  linear forms Σ p_n x_n -> Σ p_n ψ_n, and M_β ψ is h -> ψ(h T_β); so
##  M_β e_1 is the column (E(x_n T_β))_n.  Rows are elements of H(W).
##  The tests (the stages of the records, lib/tower/driver.jl):
##    Bimodule map (Lemma 5.1)
##          E(x_n T_s) = δ_(n,1) T_s for s in P: read off the table.
##    Linear form t: symmetry (Proposition 4.11)
##          t(b T_s) = t(T_s b) for every generator s of the level and every
##          element b of the basis B = B_P · X (test_symmetry), both sides
##          computed from the definition t = τ_P ∘ E.
##    Values on B (§5.1: τ_B = τ_P ∘ E_X): for the z-basis {T_z^j} B_P T_A of G31,
##          E(T_z^j T_a) = δ_(j,0) δ_(a,1).
##    Pairing (Lemma 5.2; Lemma 4.16 for the blocks F_r)
##          a pairing matrix M = (E(u_i y_j)) that is triangular with
##          recognised units on the diagonal:
##          family:       u_i = x_(n_i), y_i = rev(x_(m_i)) or comp(x_(m_i)) times T_Δ^(k_i) or T_z^(k_i)
##                        (a given list, G32/family32.txt);
##          translates:   u = T_z^j x_a, y = rev(x_b) T_z^-j' (central z; the z-basis of bmm.pdf §5.3);
##          ztree:        u = T_y, y = w z^i in a second breadth-first tree Y_1 with the letter z,
##                        y' = rev(w) T_z^-i (G31: Proposition 5.3 with Y_1 ≠ X);
##          complementary: u_n = x_n, y_n = the complementary word of x_n (the levels below the top).
##    Condition (3) (Proposition 5.3 (3), via (2.4))
##          directly, t(T_β^-1 T_π) = δ_(β,1) t(T_π) on B (small levels), or
##          through a central braid ζ with ζ² = π:
##          τ_P(E(x_m^-1 T_ζ) b^-1) = τ_P(b ψ_m)^* t(T_π), ψ = M_ζ e_1,
##          computed through the single coset c on which ψ lives (test_T3_zeta; t(T_π) = τ_P((T_ζ)_c ψ_c)
##          with (T_ζ)_c read off the row of T_ζ, the coordinates of 1·T_ζ), or
##          on all cosets of its support (test_T3_general).
##
#############################################################################

module Tower

using Chevie
import Main: say, wrapped, progress_printer, stamp, sup         # the records: lib/report.jl

# one tested identity: the line "testing <what> ... true" of lib/report.jl; when it is false, the first
# counterexamples follow, one per line "    ! ..."
function testing(what, ok::Bool; note = "", details = String[])
    Main.testing(what, ok; note = note)
    ok || foreach(l -> say("    ! " * l), first(details, 10))
    ok
end
# an identity that cannot be tested in the ring of the computation (r -> r^* modulo p): said, and counted
const NOTCOMPUTED = String[]
notcomputed(what, why) = (say("not computed: $what ($why)"); push!(NOTCOMPUTED, what); nothing)

include("coset.jl")
include("setrow.jl")        # the setRow procedure of bmm.pdf §3.3 over H(P)

# ---- the trace pairing of H(P): τ_P(h h') = Σ h_x h'_y G[x, y], G[x, y] = τ_P(b_x b_y), stored sparsely by rows ----
const GRAM = IdDict{Any,Any}()
# the rows of G for the algebra A, computed once
function gram_rows(A::FlatAlg{S}) where {S}
    get!(GRAM, A) do
        G = [Tuple{Int32,S}[] for _ in 1:A.d]
        for x in 1:A.d
            bx = basis(A, x)
            for y in 1:A.d
                c = tau(A, mul(A, bx, basis(A, y))); iszero(c) || push!(G[x], (Int32(y), c))
            end
        end
        G
    end
end
# the columns of G (G[x, y] stored at y), computed once from the rows
const GRAMC = IdDict{Any,Any}()
function gram_cols(A::FlatAlg{S}) where {S}
    get!(GRAMC, A) do
        G = gram_rows(A); C = [Tuple{Int32,S}[] for _ in 1:A.d]
        for x in 1:A.d, (y, g) in G[x]; push!(C[y], (Int32(x), g)); end
        C
    end
end
# The Gram matrix G[k, j] = τ(b_k b_j) of the flat algebra AL = H(P_i) built on the table T of its level
# (H(P_i) = ⊕_n H(P) x_n, τ = τ_P ∘ E), through the table instead of |AL|² products: for b_k = b_i x_n,
# k = (n-1) d_P + i,  τ(b_k b_j) = τ_P(E(b_i x_n b_j)) = τ_P(b_i E(x_n b_j)) = Σ_l G_P[i, l] (c_j)_n[l],
# c_j = M_(w_j) e_1 the column h -> E(h b_j) of the word w_j of b_j (only the definition of τ and the left
# H(P)-linearity of E are used).  The columns are computed along the trie of the suffixes of the basis words of AL
# (M_(s w) e_1 = M_s M_w e_1).  Stored in GRAM and GRAMC; returns (number of nonzero entries, trie nodes).
function gram_from_table!(T::Table{S}, AL::FlatAlg{S}; progress = nothing) where {S}
    A = T.A; dP = A.d; N = T.N; d = AL.d
    d == N * dP || error("gram_from_table!: AL is not the flat algebra of the table")
    GP = gram_cols(A)
    nodes = length(AL.sufnext)
    kids = [Int[] for _ in 1:nodes]; for t in 2:nodes; push!(kids[AL.sufnext[t]], t); end
    word_at = zeros(Int, nodes); for j in 1:d; word_at[AL.suf[j]] = j; end
    cols = [Tuple{Int32,S}[] for _ in 1:d]
    acc = Acc{S}(dP); done = Ref(0)
    function visit(t, c)
        j = word_at[t]
        if j > 0
            out = Tuple{Int32,S}[]
            for n in 1:N
                v = c[n]; v === nothing && continue
                for k in eachindex(v.idx), (i, g) in GP[v.idx[k]]; addmul!(acc, i, v.val[k], g); end
                w = collect!(acc)
                for k in eachindex(w.idx); push!(out, (Int32((n - 1) * dP + w.idx[k]), w.val[k])); end
            end
            cols[j] = out
            done[] += 1; progress === nothing || progress(done[])
        end
        for u in kids[t]; visit(u, col_letter(T, c, AL.sufletter[u])); end
    end
    visit(1, colunit(S, N, 1))
    rows = [Tuple{Int32,S}[] for _ in 1:d]
    for j in 1:d, (k, g) in cols[j]; push!(rows[k], (Int32(j), g)); end
    GRAM[AL] = rows; GRAMC[AL] = cols
    sum(length, rows), nodes
end
# τ_P(h g) through the rows of G
function taupair(A::FlatAlg{S}, h::SV{S}, g::SV{S}) where {S}
    G = gram_rows(A); r = zero(S)
    for (x, c) in zip(h.idx, h.val)
        for (y, gxy) in G[x]
            d = coefficient(g, y); iszero(d) || (r += c * gxy * d)
        end
    end
    r
end

# ---- Bimodule map (Lemma 5.1) ---------------------------------------------------------------------------------
# E(x_n T_s) = δ_(n,1) T_s for s in P, read off the rows of the table
function test_T1(T::Table)
    fails = [(n, s) for s in T.subset for n in 2:T.N if !iszero(rcoef(T.rows[s][n], 1))]
    testing("E(x_n T_s) = δ_(n,1) T_s for all cosets n and the generators s of P", isempty(fails) && test_one(T);
          note = isempty(fails) ? "" : "fails for $(length(fails)) pairs (n, s)",
          details = ["E(x_$n T_$(wordstr(T, [s]))) ≠ 0,  x_$n = $(wordstr(T, T.words[n]))" for (n, s) in fails])
end

# ---- Linear form t: symmetry (Proposition 4.11) on the basis B = B_P · X -----------------------------------------
# For a generator s of the level and an element b x of B (b in B_P, x in X), both sides from the definition
# t = τ_P ∘ E and the left H(P)-linearity of E:
#   t(b x T_s) = τ_P(b E(x T_s)) = τ_P(b ψ_x),           ψ = M_s e_1 = (E(x_n T_s))_n;
#   t(T_s b x) = τ_P(E(r x)) = Σ_n τ_P(r_n E(x_n x)),    r = T_s b = Σ_n r_n x_n.
# The rows r = T_s b are computed along the tree of the basis words of H(P) (T_s b_(y l) = (T_s b_y) T_l).  The values
# E(x_n x), x in X, are computed once for each coset n that some row r reaches (ECache): the rows x_n x along the
# tree X up to the depth L, and for a deeper x = x_p u (|x_p| = L) as E(x_n x_p u) = Σ_k (x_n x_p)_k E(x_k u) through
# the column M_u e_1 = (E(x_k u))_k (memoized).  τ_P(u v) = Σ_y' D_u[y'] v[y'] with D_u[y'] = τ_P(u b_y') =
# Σ_y u_y G_P[y, y'] (the Gram matrix of H(P)).  Every pair (b, x) is one identity; where neither side has a term,
# both are the empty sum 0.

# E(x_n x) for x in X, by coset n: at[n][y'] = the pairs (m, coefficient of b_y' in E(x_n x_m)), computed on demand
mutable struct ECache{S}
    at::Dict{Int,Dict{Int32,Vector{Tuple{Int32,S}}}}
    tails::Dict{Vector{Int},Col{S}}
    L::Int
    rowops::Int
    entries::Int
    terms::Int
end
ECache{S}(L::Int) where {S} = ECache{S}(Dict{Int,Dict{Int32,Vector{Tuple{Int32,S}}}}(), Dict{Vector{Int},Col{S}}(), L, 0, 0, 0)
# the column M_u e_1 = (E(x_k u))_k of a word u (memoized; M_(l u') e_1 = M_l M_(u') e_1)
function tailcol(T::Table{S}, C::ECache{S}, u::Vector{Int}) where {S}
    isempty(u) && return colunit(S, T.N, 1)
    haskey(C.tails, u) && return C.tails[u]
    c = col_letter(T, tailcol(T, C, u[2:end]), u[1]); C.tails[u] = c
    c
end
function ecache_at!(T::Table{S}, C::ECache{S}, n::Int) where {S}
    haskey(C.at, n) && return C.at[n]
    D = Dict{Int32,Vector{Tuple{Int32,S}}}()
    function put(m, v)
        (v === nothing || iszero(v)) && return
        C.entries += 1; C.terms += nterms(v)
        for k in eachindex(v.idx); push!(get!(() -> Tuple{Int32,S}[], D, v.idx[k]), (Int32(m), v.val[k])); end
    end
    descendants(m) = vcat([m], [x for c in T.children[m] for x in descendants(c)])
    function walk(m, r)                                   # r = the coordinates of x_n x_m
        put(m, rcoef(r, 1))
        for c in T.children[m]
            if length(T.words[c]) <= C.L
                C.rowops += 1; walk(c, row_gen(T, r, T.letter[c]))
            else                                          # x_d = x_m u, |x_m| = L: through the column of u
                for d in descendants(c); put(d, colval(T, r, tailcol(T, C, T.words[d][length(T.words[m])+1:end]))); end
            end
        end
    end
    walk(1, erow(S, n))
    C.at[n] = D
end

# Proposition 4.11 for a generator s of P when the table gives E(x_n T_s) = δ_(n,1) T_s: for b in B_P and x in X,
#   t(T_s b x) = τ_P(T_s b E(x)) = δ_(x,1) τ_P(T_s b),     t(b x T_s) = τ_P(b E(x T_s)) = δ_(x,1) τ_P(b T_s),
# so the identities with x ≠ 1 read 0 = 0, and those with x = 1 compare the coefficients of 1 of T_s b and b T_s,
# the left and right multiplications of the flat algebra H(P) (no Gram matrix is needed).
function test_symmetry_P(T::Table{S}, s::Int) where {S}
    A = T.A; N = T.N; d = A.d; j = T.pindex[s]; s_ = wordstr(T, [s])
    bad = [y for y in 1:d if coefficient(A.L[j][y], 1) != coefficient(A.R[j][y], 1)]
    say("T_$s_ in P and E(x_n T_$s_) = δ_(n,1) T_$s_ (the table): t(T_$s_ b x) = δ_(x,1) τ_P(T_$s_ b), t(b x T_$s_) = δ_(x,1) τ_P(b T_$s_)")
    testing("t(b T_$s_) = t(T_$s_ b) for all b in B = B_P · X", isempty(bad);
            note = isempty(bad) ? "$(d * N) identities: $(d * (N - 1)) read 0 = 0, $d read τ_P(T_$s_ b) = τ_P(b T_$s_)" :
                                  "fails for $(length(bad)) of the $d elements of B_P",
            details = ["b = b_$y ($(wordstr(T, Pword(T, A.words[y]))))" for y in bad])
end

# Proposition 4.11 for the generator s on the basis B = B_P · X: t(b x T_s) = t(T_s b x) for all b in B_P, x in X.
# gram() makes sure that the Gram matrix of H(P) is known (it is not needed for the generators of P).
function test_symmetry(T::Table{S}, s::Int, C::ECache{S}; gram = () -> nothing) where {S}
    A = T.A; N = T.N; d = A.d
    ψ = col_gen(T, colunit(S, N, 1), s); suppψ = support(ψ)
    T.pindex[s] > 0 && suppψ == [1] && ψ[1] == Tgen(T, s) && return test_symmetry_P(T, s)
    gram(); Grow = gram_rows(A); Gcol = gram_cols(A)
    # the right-hand sides: rv[m][y] = τ_P(b_y ψ_m) = Σ_l G_P[y, l] (ψ_m)_l
    accd = Acc{S}(d); rv = Dict{Int,Vector{S}}()
    for m in suppψ
        v = ψ[m]
        for k in eachindex(v.idx), (y, g) in Gcol[v.idx[k]]; addmul!(accd, y, v.val[k], g); end
        w = collect!(accd); dense = fill(zero(S), d); for k in eachindex(w.idx); dense[w.idx[k]] = w.val[k]; end
        rv[m] = dense
    end
    kids = [Int[] for _ in 1:d]; for y in 2:d; push!(kids[A.parent[y]], y); end
    accx = Acc{S}(N); bad = 0; examples = String[]; done = 0; prog = progress_printer("basis elements b of H(P)", d)
    maxrow = 0; cosets = Set{Int}(); nonzero = 0
    function visit(y, r)
        maxrow = max(maxrow, length(r))
        for (n, u) in r                                       # Σ_n τ_P(r_n E(x_n x)) for all x at once
            push!(cosets, n); En = ecache_at!(T, C, Int(n)); isempty(En) && continue
            for k in eachindex(u.idx), (y2, g) in Grow[u.idx[k]]; addmul!(accd, y2, u.val[k], g); end
            D = collect!(accd)                                # D[y'] = τ_P(r_n b_y')
            for k in eachindex(D.idx)
                lst = get(En, D.idx[k], nothing); lst === nothing && continue
                for (m, c) in lst; addmul!(accx, m, D.val[k], c); end
            end
        end
        lhs = collect!(accx)                                  # x_m -> t(T_s b_y x_m)
        nonzero += length(lhs.idx)
        rhs = SV{S}(Int32[m for m in suppψ if !iszero(rv[m][y])], S[rv[m][y] for m in suppψ if !iszero(rv[m][y])])
        if lhs != rhs
            bad += 1; length(examples) < 6 && push!(examples, "b = b_$y ($(wordstr(T, Pword(T, A.words[y])))): fails at the cosets " *
                join(sort(unique(vcat(lhs.idx, rhs.idx))), ", "))
        end
        done += 1; prog(done)
        for k in kids[y]; visit(k, row_gen(T, r, T.subset[A.letter[k]])); end
    end
    visit(1, T.rows[s][1])
    s_ = wordstr(T, [s])
    say("T_$s_: the rows T_$s_ b reach $(length(cosets)) coset(s) (at most $maxrow at once); E(x_n T_$s_) ≠ 0 at $(length(suppψ)) coset(s); " *
        "$nonzero nonzero values t(T_$s_ b x)  $(stamp())")
    testing("t(b T_$s_) = t(T_$s_ b) for all b in B = B_P · X", bad == 0;
            note = bad == 0 ? "$(d * N) identities" : "fails for $bad of the $d elements of B_P", details = examples)
end

# ---- central elements ---------------------------------------------------------------------------------------------
# T_w T_s = T_s T_w for all generators s (the coordinates of both products, from e_1)
function test_central(T::Table, w, label)
    rw = coords(T, w)
    bad = [s for s in 1:T.ngens if row_gen(T, rw, s) != row_word(T, T.rows[s][1], w)]
    testing("$label is central: T_$label T_s = T_s T_$label for all generators s", isempty(bad); details = ["T_$label does not commute with T_$(wordstr(T, [s]))" for s in bad])
    rw
end
# the Garside-type relation T_Δ T_s = T_(σ(s)) T_Δ (σ a permutation of the generators), so that T_Δ^2 is central
function test_garside(T::Table, Δ, σ)
    rΔ = coords(T, Δ)
    bad = [s for s in 1:T.ngens if row_gen(T, rΔ, s) != row_word(T, T.rows[σ[s]][1], Δ)]
    testing("T_Δ T_s = T_σ(s) T_Δ for all generators s, Δ = $(wordstr(T, Δ)), σ = ($(join([wordstr(T, [σ[s]]) for s in 1:T.ngens], ", ")))", isempty(bad);
          details = ["fails for s = $(wordstr(T, [s]))" for s in bad])
    testing("σ is an involution, so T_Δ^2 is central", all(σ[σ[s]] == s for s in 1:T.ngens))
end

# ---- Condition (3) through ζ: ζ central, ζ² = π, ψ = M_ζ e_1 -----------------------------------------------------
# The form h -> t(h T_ζ) is ψ = M_ζ e_1.  When it lives on a single coset c, the test runs through c (test_T3_zeta);
# otherwise on all cosets of its support (test_T3_general, below).
function test_T3_through(T::Table{S}, ζ, label) where {S}
    ψ = col_word(T, colunit(S, T.N, 1), ζ); supp = support(ψ)
    length(supp) == 1 ? test_T3_zeta(T, ζ, label, ψ) : test_T3_general(T, ζ, label, ψ)
end

# ---- pieces of the long tests, for the checkpoints of the driver (lib/tower/driver.jl) ------------------------------
# Each test below that runs for hours on G34 is also given as a sequence of pieces, with its state in the arguments,
# so that the driver can write a checkpoint between two pieces.  Run one after the other, the pieces compute exactly
# what the test computes, in the same order, and write the same lines.
#
# M_w ψ through the letters ls = reverse(w)[range], a slice of the letters of w from the right (col_word in pieces)
col_letters(T::Table, ψ::Col, ls) = foldl((c, l) -> col_letter(T, c, l), ls; init = ψ)
# the walk of the coset tree from a column ψ0: node m gets the column M_(x_m^-1) ψ0, the children through col_inv,
# depth first in the order of the recursive walks of test_T3_direct, test_T3_zeta and test_T3_general; it keeps the
# columns of the path from the root only, as they do
mutable struct ColWalk{S}
    stack::Vector{Tuple{Int,Col{S},Int}}       # (node, its column, the next child to visit)
    X::Vector{Any}                              # X[m]: the first coordinate of the column of m
    nnz::Vector{Int}                            # the number of nonzero coordinates of each column, in the order of the walk
    done::Int
end
function colwalk_start(T::Table{S}, ψ0::Col{S}) where {S}
    w = ColWalk{S}(Tuple{Int,Col{S},Int}[], Vector{Any}(nothing, T.N), Int[], 0)
    colwalk_visit!(w, 1, ψ0); w
end
colwalk_visit!(w::ColWalk, m, col) = (w.X[m] = col[1]; push!(w.nnz, count(!isnothing, col)); w.done += 1; push!(w.stack, (m, col, 1)))
# K more nodes of the walk (all of them if K = 0); true when the walk is complete
function colwalk!(T::Table, w::ColWalk, K::Int = 0; prog = nothing)
    n = 0
    while !isempty(w.stack)
        m, col, i = w.stack[end]
        kids = T.children[m]
        if i > length(kids); pop!(w.stack); continue; end
        K > 0 && n >= K && return false
        w.stack[end] = (m, col, i + 1); k = kids[i]
        colwalk_visit!(w, k, col_inv(T, col, T.letter[k])); n += 1
        prog === nothing || prog(w.done)
    end
    true
end

# test_T3_zeta in pieces: zeta_head (after ψ = M_ζ e_1; returns c, or 0 if ψ does not live on one coset: then the test
# is test_T3_general), for ζ = u v the row of T_u (row_word from the row of 1) and the column M_v e_c (col_letters),
# zeta_values, the walk from e_c (colwalk!), zeta_tail.  (T_ζ)_c = (M_ζ e_c)_1, the coefficient of x_c in 1·T_ζ, is
# Σ_n (T_u)_n (M_v e_c)_n (colval).  (Until 13 Nov 2026 it was read off the whole column M_ζ e_c, u = 1: at the top
# of G34 that column filled up letter after letter, the 22nd of 24 slices running for more than 5 h modulo p at 16 GB;
# the driver now takes v = z there.)
function test_T3_zeta_head(T::Table{S}, label, ψ) where {S}
    supp = support(ψ)
    say("the form h -> t(h T_ζ), ζ = $label: supported on the coset$(length(supp) == 1 ? "" : "s") $(join(supp, ", "))" *
        (length(supp) == 1 ? "; x_$(supp[1]) = $(wordstr(T, T.words[supp[1]])), $(nterms(ψ[supp[1]])) terms" : ""))
    testing("the form h -> t(h T_ζ) lives on a single coset c", length(supp) == 1) || return 0
    supp[1]
end
function test_T3_zeta_values(T::Table{S}, ψ, c, tζc) where {S}    # tζc = (T_ζ)_c, the coefficient of x_c in T_ζ
    tπ = (tζc === nothing || iszero(tζc)) ? zero(S) : taumul(T.A, tζc, ψ[c])      # = tau(T.A, mul(T.A, tζc, ψ[c])), depth first (alg.jl)
    say("t(T_π) = t(T_ζ^2) = τ_P((T_ζ)_c ψ_c) = $tπ")
    testing("t(T_π) = 1", isone(tπ))
    tπ
end
function test_T3_zeta_tail(T::Table{S}, ψ, c, tπ, w::ColWalk) where {S}
    A = T.A; N = T.N; d = A.d; X = w.X; g = ψ[c]
    say("the columns M_(x_m^-1) e_c: $(sum(w.nnz)) nonzero entries of $(N^2)")
    nz = [m for m in 1:N if X[m] !== nothing && m != c]
    testing("E(x_m^-1 T_ζ) = 0 for the $(N - 1) cosets m ≠ c", isempty(nz); note = isempty(nz) ? "" : "fails for $(length(nz)) cosets")
    if S == Sh
        notcomputed("τ_P(E(x_c^-1 T_ζ) b^-1) = τ_P(b ψ_c)^* t(T_π) for the $d elements b of the basis of H(P)", "r -> r^* is not defined at a point; tested in the exact run")
    else
        # the identity τ_P(v b^-1) = τ_P(b g)^* t(T_π) for all b in the basis, v = E(x_c^-1 T_ζ): both sides are linear
        # forms in h = b^-1 (the right one through h -> τ_P(h^† g)^*), so it is equivalent to τ_P(v b_y) = τ_P(b_y^-1 g)^* t(T_π)
        # for all y, computed along the tree of the basis words: v b_(ys) = (v b_y) T_s and b_(ys)^-1 g = T_s^-1 (b_y^-1 g).
        v = X[c] === nothing ? zero(A) : mul_path(A, X[c], g)                  # = mul, depth first (alg.jl)
        kids = [Int[] for _ in 1:d]; for y in 2:d; push!(kids[A.parent[y]], y); end
        bad = 0
        function walkP(y, vb, ig)
            tau(A, vb) == star(tau(A, ig)) * tπ || (bad += 1)
            for k in kids[y]; walkP(k, rmulgen(A, vb, A.letter[k]), mulinv(A, ig, A.L[A.letter[k]])); end
        end
        walkP(1, v, g)
        testing("τ_P(E(x_c^-1 T_ζ) b^-1) = τ_P(b ψ_c)^* t(T_π) for all $d elements b of the basis of H(P) (on the basis {b_y}: τ_P(v b_y) = τ_P(b_y^-1 ψ_c)^* t(T_π))", bad == 0;
              note = bad == 0 ? "" : "fails for $bad elements")
    end
end
# test_T3_general in pieces: general_head (after ψ; returns t(T_π)), the walk from ψ (colwalk!), general_tail
function test_T3_general_head(T::Table{S}, ζ, label, ψ) where {S}
    supp = support(ψ)
    say("the form h -> t(h T_ζ), ζ = $label, lives on $(length(supp)) cosets: $(first(supp, 12))$(length(supp) > 12 ? "..." : "")")
    tπ = tau(T.A, colval(T, coords(T, ζ), ψ))                         # t(T_ζ T_ζ)
    say("t(T_π) = t(T_ζ^2) = $tπ")
    testing("t(T_π) = 1", isone(tπ))
    tπ
end
function test_T3_general_tail(T::Table{S}, ψ, tπ, w::ColWalk) where {S}
    A = T.A; N = T.N; d = A.d; X = w.X
    act = [m for m in 1:N if X[m] !== nothing || ψ[m] !== nothing]
    say("E(x_m^-1 T_ζ) or E(x_m T_ζ) is nonzero for $(length(act)) cosets m")
    bad = count(m -> ψ[m] === nothing && X[m] !== nothing, act)
    testing("E(x_m^-1 T_ζ) = 0 for the cosets m with E(x_m T_ζ) = 0", bad == 0; note = bad == 0 ? "" : "fails for $bad cosets")
    if S == Sh
        notcomputed("τ_P(E(x_m^-1 T_ζ) b^-1) = τ_P(b E(x_m T_ζ))^* t(T_π) for the cosets m with E(x_m T_ζ) ≠ 0 and the elements b of the basis of H(P)", "r -> r^* is not defined at a point; tested in the exact run")
    else
        kids = [Int[] for _ in 1:d]; for y in 2:d; push!(kids[A.parent[y]], y); end
        nbad = 0
        for m in act
            ψ[m] === nothing && continue
            v = X[m] === nothing ? zero(A) : X[m]; g = ψ[m]
            function walkP(y, vb, ig)
                tau(A, vb) == star(tau(A, ig)) * tπ || (nbad += 1)
                for c in kids[y]; walkP(c, rmulgen(A, vb, A.letter[c]), mulinv(A, ig, A.L[A.letter[c]])); end
            end
            walkP(1, v, g)
        end
        testing("τ_P(E(x_m^-1 T_ζ) b^-1) = τ_P(b E(x_m T_ζ))^* t(T_π) for the $(count(m -> ψ[m] !== nothing, act)) cosets m with E(x_m T_ζ) ≠ 0 and all $d elements b of the basis of H(P)",
              nbad == 0; note = nbad == 0 ? "" : "fails $nbad times")
    end
end
# On a single coset c:
# On the basis { b x_m T_ζ } of images of braids, condition (3) reads τ_P(E(x_m^-1 T_ζ) b^-1) = τ_P(b ψ_m)^* t(T_π).
# E(x_m^-1 T_ζ) = (x_m^-1)_c ψ_c, and (x_m^-1)_c = (M_(x_m^-1) e_c)_1: the columns from e_c along the tree.
# t(T_π) = t(T_ζ T_ζ) = τ_P((T_ζ)_c ψ_c) with (T_ζ)_c = (M_ζ e_c)_1 = Σ_n (T_u)_n (M_v e_c)_n, ζ = u v, v the last
# nv letters of ζ (default all of them: u = 1).
function test_T3_zeta(T::Table{S}, ζ, label, ψ = col_word(T, colunit(S, T.N, 1), ζ); nv = length(ζ)) where {S}
    c = test_T3_zeta_head(T, label, ψ); c == 0 && return
    tπ = test_T3_zeta_values(T, ψ, c, colval(T, coords(T, ζ[1:end-nv]), col_word(T, colunit(S, T.N, c), ζ[end-nv+1:end])))
    w = colwalk_start(T, colunit(S, T.N, c)); colwalk!(T, w; prog = progress_printer("columns", T.N))
    test_T3_zeta_tail(T, ψ, c, tπ, w)
end

# ---- Pairing (Lemma 5.2) -------------------------------------------------------------------------------------------
# strongly connected components of i -> j (M_ij ≠ 0, i ≠ j); all of size 1 iff M is triangular in some order
function scc(adj::Vector{Vector{Int}})
    N = length(adj); idx = zeros(Int, N); low = zeros(Int, N); on = falses(N); st = Int[]; comps = Vector{Int}[]; c = 0
    for root in 1:N
        idx[root] == 0 || continue
        work = [(root, 1)]
        while !isempty(work)
            v, i = pop!(work)
            if i == 1; c += 1; idx[v] = low[v] = c; push!(st, v); on[v] = true; end
            descended = false
            while i <= length(adj[v])
                w = adj[v][i]; i += 1
                if idx[w] == 0
                    push!(work, (v, i)); push!(work, (w, 1)); descended = true; break
                elseif on[w]
                    low[v] = min(low[v], idx[w])
                end
            end
            descended && continue
            if low[v] == idx[v]
                comp = Int[]
                while true; w = pop!(st); on[w] = false; push!(comp, w); w == v && break; end
                push!(comps, sort!(comp))
            end
            isempty(work) || (u = work[end][1]; low[u] = min(low[u], low[v]))
        end
    end
    comps
end
# a unit of H(P), possibly times a power of a central element z_P: returns (inverse, description) or nothing.
# The exponent j and the form of the unit are found in the shadow of H(P); the exact program computes h z_P^-j
# once and verifies the form (verify_form), then multiplies the inverse back.
const ZPOW = IdDict{Any,Dict{Int,Any}}()
# z_P^j in A (j may be negative), cached
function zpower(A::FlatAlg, zP, j::Int)
    D = get!(ZPOW, A, Dict{Int,Any}())
    get!(D, j) do
        j == 0 ? one(A) : j > 0 ? mul(A, zpower(A, zP, j - 1), element(A, zP)) : mul(A, zpower(A, zP, j + 1), element(A, -reverse(zP)))
    end
end
function recognise_unit(A::FlatAlg{S}, h::SV{S}, zP) where {S}
    iszero(h) && return nothing
    As = shadow_alg(A); hs = toshadow(A, h)
    for j in (isempty(zP) ? (0:0) : (0, 1, -1, 2, -2, 3, -3))
        form = unit_form_search(As, mul(As, hs, zpower(As, zP, -j))); form === nothing && continue
        u = mul(A, h, zpower(A, zP, -j))                          # h = u z_P^j
        inv = verify_form(A, u, form); inv === nothing && continue
        hinv = mul(A, zpower(A, zP, -j), inv)
        (mul(A, h, hinv) == one(A) && mul(A, hinv, h) == one(A)) || error("recognise_unit: a wrong inverse")
        kind, x, y = form                                         # u = c b_y, b_x u = c b_y or u b_x = c b_y
        if kind == :basis
            c = monomial(u)[1]; desc = "b_$y"
        elseif kind == :left
            c = monomial(mul(A, basis(A, x), u))[1]; desc = "b_$x^-1 b_$y"
        else
            c = monomial(mul(A, u, basis(A, x)))[1]; desc = "b_$y b_$x^-1"
        end
        return hinv, (isone(c) ? "" : "-") * desc * (j == 0 ? "" : " z_P^$j")
    end
    nothing
end

# the diagonal entries of a matrix that is triangular in some order, as units; cols[j] = the column j as a Dict n => entry
function test_triangular(T::Table{S}, cols::Vector{Dict{Int,SV{S}}}, rowof::Vector{Int}, zP, what) where {S}
    n = length(cols); pos = Dict(rowof[i] => i for i in 1:n)
    adj = [Int[] for _ in 1:n]
    for j in 1:n, (r, _) in cols[j]
        i = pos[r]; i != j && push!(adj[i], j)
    end
    comps = scc(adj); big = filter(c -> length(c) > 1, comps)
    say("$what: $(sum(length, cols)) nonzero entries of $(n^2); $(length(comps)) diagonal blocks, $(count(c -> length(c) == 1, comps)) of size 1" *
        (isempty(big) ? " (the matrix is triangular in a suitable order)" : ", the others of sizes $(join(sort(length.(big), rev = true), ", "))"))
    testing("$what is triangular (every strongly connected component of its support is a single index)", isempty(big)) || return false
    forms = Dict{String,Int}(); bad = String[]
    for i in 1:n
        dg = get(cols[i], rowof[i], nothing)
        res = dg === nothing ? nothing : recognise_unit(T.A, dg, zP)
        if res === nothing
            push!(bad, "entry $i (row x_$(rowof[i])): " * (dg === nothing ? "zero" : "$(nterms(dg)) terms, not recognised"))
        else
            forms[res[2]] = get(forms, res[2], 0) + 1
        end
    end
    fl = sort(collect(forms); by = x -> (-x[2], x[1]))
    nbasis = sum((m for (f, m) in fl if !occursin("^-1", f) && !occursin("z_P", f)); init = 0)
    say("diagonal entries: " * join(["$f" * (m > 1 ? " ×$m" : "") for (f, m) in first(fl, 12)], ", ") * (length(fl) > 12 ? ", ... ($(length(fl)) forms)" : ""))
    testing("the $n diagonal entries of $what are recognised units of H(P) (± b, ± b^-1 b', ± b b'^-1, times a power of z_P)", isempty(bad);
          note = "$nbasis are ± a basis element", details = bad)
end

# Pairing, a given family: fam[i] = (n_i, m_i, k_i): row i is x_(n_i), column i is rev(x_(m_i)) T_Δ^(k_i)
function test_T4_family(T::Table{S}, fam, Δ, zP; tname = "Δ") where {S}
    N = T.N
    testing("the family lists $N rows, each coset once, with k_i ≥ 0", sort([f[1] for f in fam]) == 1:N && all(f -> f[3] >= 0, fam) && length(fam) == N) || return false
    kmax = maximum(f[3] for f in fam)
    ψ = Vector{Col{S}}(undef, kmax + 1); ψ[1] = colunit(S, N, 1)
    for k in 1:kmax
        ψ[k+1] = col_word(T, ψ[k], Δ)
        say("  the form h -> t(h T_$tname^$k): $(length(support(ψ[k+1]))) coset(s) $(first(support(ψ[k+1]), 5)), $(sum(nterms(h) for h in ψ[k+1] if h !== nothing)) terms  $(stamp())")
    end
    cols = [Dict{Int,SV{S}}() for _ in 1:N]; col = Dict((f[2], f[3]) => i for (i, f) in enumerate(fam))
    for k in 0:kmax
        wanted = falses(N)
        for f in fam; f[3] == k || continue; m = f[2]; while m != 0 && !wanted[m]; wanted[m] = true; m = T.parent[m]; end; end
        function walk(m, c)
            i = get(col, (m, k), 0)
            if i != 0
                for n in 1:N; c[n] === nothing || (cols[i][n] = c[n]); end
            end
            for ch in T.children[m]; wanted[ch] && walk(ch, col_gen(T, c, T.letter[ch])); end
        end
        wanted[1] && walk(1, ψ[k+1])
        say("  $tname^$k: $(count(f -> f[3] == k, fam)) columns, from $(count(wanted)) columns computed along the tree  $(stamp())")
    end
    test_triangular(T, cols, [f[1] for f in fam], zP, "the pairing matrix (E(x_(n_i) rev(x_(m_i)) T_$tname^(k_i)))")
end

# Values on B for the z-basis B = {T_z^j} · B_P · T_A (G31): t(b T_z^j T_a) = τ_P(b E(T_z^j T_a)), so t(β) = δ_(β,1)
# on B if E(T_z^j T_a) = δ_(j,0) δ_(a,1) for j < d, a in A.  E(T_z^j T_a) = E(x_a T_z^j) (z central) is the value at
# the coset of x_a of the form ψ_j = M_z^j e_1 (h -> E(h T_z^j)): nodes[a] = the coset of the word a of A.
function test_values_translates(T::Table{S}, z, nodes, d) where {S}
    ψ = colunit(S, T.N, 1); bad = String[]
    for j in 0:d-1
        j > 0 && (ψ = col_word(T, ψ, z))
        for (a, n) in enumerate(nodes)
            v = ψ[n]; ok = (j == 0 && n == 1) ? (v !== nothing && v == one(T.A)) : v === nothing
            ok || push!(bad, "E(T_z^$j T_a) ≠ $(j == 0 && n == 1 ? 1 : 0) for a = $(wordstr(T, T.words[n]))")
        end
    end
    testing("E(T_z^j T_a) = δ_(j,0) δ_(a,1) for all j < $d and the $(length(nodes)) words a of A, so t(b T_z^j T_a) = τ_P(b) δ_(j,0) δ_(a,1)",
            isempty(bad); note = isempty(bad) ? "$(d * length(nodes)) identities in H(P)" : "fails $(length(bad)) times", details = bad)
end

# Pairing, central translates (Lemma 4.16 over H(P)): z central, its image permutes the cosets in orbits of length o; A = the first coset of
# each orbit; u_(j,a) = T_z^j x_a, y_(j',b) = rev(x_b) T_z^-j'.  The block (j, j') of M is F_(j-j'),
# F_r = (E(T_z^r x_a rev(x_b)))_(a,b).  Tested: F_r = 0 for 0 < r < o, and F_0 triangular with unit diagonal.
function test_T4_translates(T::Table{S}, z) where {S}
    N = T.N
    σ = [foldl((n, s) -> T.act[n, s], z; init = n) for n in 1:N]
    orbits = Vector{Int}[]; seen = falses(N)
    for n in 1:N
        seen[n] && continue
        o = [n]; while σ[o[end]] != n; push!(o, σ[o[end]]); end
        push!(orbits, o); seen[o] .= true
    end
    o = length(orbits[1]); q = [minimum(x) for x in orbits]; nr = length(q)
    testing("the $N cosets form $nr orbits of $o under z", all(length(x) == o for x in orbits))
    say("x_a: the first coset of each orbit (words of length ≤ $(maximum(length(T.words[n]) for n in q))); y_b = rev(x_b)")
    ψ = [colunit(S, N, 1)]; for r in 1:o-1; push!(ψ, col_word(T, ψ[end], z)); end
    for r in 1:o-1; say("  the form h -> t(h T_z^$r): $(length(support(ψ[r+1]))) coset(s) $(support(ψ[r+1])), $(sum(nterms(h) for h in ψ[r+1] if h !== nothing)) terms"); end
    F = [[Dict{Int,SV{S}}() for _ in 1:nr] for r in 0:o-1]; col = Dict(n => b for (b, n) in enumerate(q))
    wanted = falses(N); for n in q; m = n; while m != 0 && !wanted[m]; wanted[m] = true; m = T.parent[m]; end; end
    for r in 0:o-1
        function walk(m, c)
            b = get(col, m, 0)
            if b != 0
                for (a, n) in enumerate(q); c[n] === nothing || (F[r+1][b][a] = c[n]); end
            end
            for ch in T.children[m]; wanted[ch] && walk(ch, col_gen(T, c, T.letter[ch])); end
        end
        walk(1, ψ[r+1])
    end
    for r in 1:o-1
        nz = sum(length, F[r+1])
        testing("F_$r = 0:  E(T_z^$r x_a rev(x_b)) = 0 for all a, b", nz == 0; note = nz == 0 ? "" : "$nz nonzero entries")
    end
    test_triangular(T, F[1], collect(1:nr), Int[], "F_0 = (E(x_a rev(x_b)))")
end

# Pairing, complementary words: for s_1^(a_1) ... s_l^(a_l) (maximal runs) the word s_l^(k-a_l) ... s_1^(k-a_1)
function complementary(w, k)
    runs = Tuple{Int,Int}[]
    for s in w; (!isempty(runs) && runs[end][1] == s) ? (runs[end] = (s, runs[end][2] + 1)) : push!(runs, (s, 1)); end
    vcat([fill(s, k - a) for (s, a) in reverse(runs)]...)
end
# Pairing below the top: the matrix (E(x_n y_m)), y_m the reversed (order 2) or complementary (order 3) word of x_m
function test_T4_complementary(T::Table{S}) where {S}
    N = T.N; k = T.q.k
    cols = Vector{Dict{Int,SV{S}}}(undef, N)
    for m in 1:N
        ψ = col_word(T, colunit(S, N, 1), complementary(T.words[m], k))
        cols[m] = Dict(n => ψ[n] for n in 1:N if ψ[n] !== nothing)
    end
    test_triangular(T, cols, collect(1:N), Int[], "the pairing matrix (E(x_n y_m)) with the " * (k == 2 ? "reversed" : "complementary") * " words y_m")
end

# ---- Condition (3) directly, for small levels: t(T_β^-1 T_π) = δ_(β,1) t(T_π) on B, through the column ψ_π = M_π e_1 ----
# For β = b x_m: t(x_m^-1 b^-1 T_π) = τ_P(b^-1 E(x_m^-1 T_π)) (T_π central), E(x_m^-1 T_π) = (M_(x_m^-1) ψ_π)_1.
function test_T3_direct(T::Table{S}, π, label; central = false) where {S}
    test_T3_direct_head(T, π, label; central = central)
    ψ = col_word(T, colunit(S, T.N, 1), π)
    tπ = test_T3_direct_values(T, ψ)
    w = colwalk_start(T, ψ); colwalk!(T, w)
    test_T3_direct_tail(T, w, tπ)
end
# test_T3_direct in pieces: direct_head, the column ψ = M_π e_1 (col_letters), direct_values, the walk from ψ
# (colwalk!), direct_tail
test_T3_direct_head(T::Table, π, label; central = false) =
    (central ? say("T_π is central: π = $label is a power of the central element tested above") : test_central(T, π, label); nothing)
function test_T3_direct_values(T::Table{S}, ψ) where {S}
    tπ = ψ[1] === nothing ? zero(S) : tau(T.A, ψ[1])
    say("t(T_π) = $tπ; the form h -> t(h T_π) lives on $(length(support(ψ))) cosets")
    testing("t(T_π) = 1", isone(tπ))
    tπ
end
function test_T3_direct_tail(T::Table{S}, w::ColWalk, tπ) where {S}
    A = T.A; N = T.N; d = A.d; X = w.X
    bad = 0
    for m in 1:N, x in 1:d
        v = X[m] === nothing ? zero(S) : taupair(A, basisinv(A, x), X[m])
        v == ((m == 1 && x == 1) ? tπ : zero(S)) || (bad += 1)
    end
    testing("t(T_β^-1 T_π) = 0 for all β ≠ 1 in B (and = t(T_π) for β = 1) [Malle–Michel, Prop. 2.7]", bad == 0; note = bad == 0 ? "$(N * d) identities" : "fails for $bad elements")
end

# ==== version 2: trees with the central letter z ==============================================================

# the partner of a word without z: the reversed word (order 2) or the complementary word (order 3); both represent
# the inverse in W
partner(w, k) = k == 2 ? reverse(w) : complementary(w, k)
zsplit(T::Table, x) = (filter(!=(T.ngens + 1), x), count(==(T.ngens + 1), x))      # T_x = T_w T_z^i, z = letter ngens+1

# the columns M_(partner(w)) ψ0 for the words w of a prefix-closed set, incrementally:
# rev(w s) = s rev(w); comp(w s) = s^2 comp(w) if w does not end with s, comp(w' s s) = s comp(w')
partner_columns(T::Table{S}, ψ0, ws) where {S} = partner_columns!(Dict{Vector{Int},Any}(Int[] => ψ0), T, partner_order(ws))
partner_order(ws) = sort(collect(ws); by = length)                  # the words in the order of the computation
# the columns of the words ws (in partner_order, their prefixes already in cols) added to cols
function partner_columns!(cols::Dict{Vector{Int},Any}, T::Table{S}, ws) where {S}
    k = T.q.k
    for w in ws
        isempty(w) && continue
        s = w[end]
        cols[w] = k == 2 ? col_gen(T, cols[w[1:end-1]], s) :
                  (length(w) >= 2 && w[end-1] == s) ? col_gen(T, cols[w[1:end-2]], s) :
                  col_gen(T, col_gen(T, cols[w[1:end-1]], s), s)
    end
    cols
end

# Pairing, a family of complementary words (G32): fam[i] = (n_i, m_i, k_i): row i is x_(n_i), column i is
# comp(x_(m_i)) T_Δ^(k_i); the columns h -> E(h T_(comp x_m) T_Δ^k) by partner_columns on the prefixes of the words needed
function test_T4_family_comp(T::Table{S}, fam, Δ, zP; tname = "Δ") where {S}
    N = T.N
    testing("the family lists $N rows, each coset once, with k_i ≥ 0", sort([f[1] for f in fam]) == 1:N && all(f -> f[3] >= 0, fam) && length(fam) == N) || return false
    kmax = maximum(f[3] for f in fam)
    ψ = Vector{Col{S}}(undef, kmax + 1); ψ[1] = colunit(S, N, 1)
    for k in 1:kmax; ψ[k+1] = col_word(T, ψ[k], Δ); end
    cols = [Dict{Int,SV{S}}() for _ in 1:N]
    for k in 0:kmax
        ws = Set{Vector{Int}}()
        for f in fam; f[3] == k || continue; w = T.words[f[2]]; for i in 0:length(w); push!(ws, w[1:i]); end; end
        isempty(ws) && continue
        pc = partner_columns(T, ψ[k+1], ws)
        for (i, f) in enumerate(fam)
            f[3] == k || continue
            c = pc[T.words[f[2]]]; for n in 1:N; c[n] === nothing || (cols[i][n] = c[n]); end
        end
        say("  $tname^$k: $(count(f -> f[3] == k, fam)) columns, from $(length(ws)) complementary words  $(stamp())")
    end
    test_triangular(T, cols, [f[1] for f in fam], zP, "the pairing matrix (E(x_(n_i) comp(x_(m_i)) T_$tname^(k_i)))")
end

# Pairing, the reversed words with blocks (Proposition 5.4; G33, G34): M = (E(x_n rev(x_m)))_(n,m) over H(P).  The
# strongly connected blocks of the support of M: a singleton must be a recognised unit of H(P); a larger block M_C is
# eliminated over H(P) with recognised units as pivots, M_C = L U with L unitriangular and U triangular with unit
# diagonal, so M_C and M are invertible (with the units of alg.jl).
function test_T4_rev(T::Table{S}, zP) where {S}
    T.q.k == 2 || error("test_T4_rev: the reversed word represents the inverse only for reflections of order 2")
    test_T4_rev_tail(T, zP, partner_columns(T, colunit(S, T.N, 1), Set(T.words)))   # h -> E(h T_rev(x_m)), the words are prefix-closed
end
# test_T4_rev in pieces: the columns pc by partner_columns! on slices of partner_order(Set(T.words)), then the tail
function test_T4_rev_tail(T::Table{S}, zP, pc) where {S}
    N = T.N
    cols = [Dict{Int,SV{S}}(n => c[n] for n in 1:N if c[n] !== nothing) for c in (pc[w] for w in T.words)]
    adj = [Int[] for _ in 1:N]
    for j in 1:N, (i, _) in cols[j]; i != j && push!(adj[i], j); end
    comps = scc(adj); big = filter(c -> length(c) > 1, comps); single = [c[1] for c in comps if length(c) == 1]
    say("M: $(sum(length, cols)) nonzero entries of $(N^2) in H(P); strongly connected blocks: $(length(single)) singletons" *
        (isempty(big) ? "" : " and blocks of sizes " * join(sort(length.(big), rev = true), ", ")))
    bad = String[]; forms = Dict{String,Int}()
    for i in single
        dg = get(cols[i], i, nothing); res = dg === nothing ? nothing : recognise_unit(T.A, dg, zP)
        res === nothing ? push!(bad, "entry $i (x_$i = $(wordstr(T, T.words[i]))): " * (dg === nothing ? "zero" : "$(nterms(dg)) terms, not recognised")) :
                          (forms[res[2]] = get(forms, res[2], 0) + 1)
    end
    fl = sort(collect(forms); by = x -> (-x[2], x[1]))
    isempty(fl) || say("the singletons: " * join(["$f" * (m > 1 ? " ×$m" : "") for (f, m) in first(fl, 12)], ", ") * (length(fl) > 12 ? ", ..." : ""))
    testing("the $(length(single)) singletons M_nn are recognised units of H(P)", isempty(bad); details = bad)
    for C in big
        m = length(C); X = [get(cols[C[j]], C[i], zero(T.A)) for i in 1:m, j in 1:m]
        pivots = String[]; ok = true; swaps = 0
        for kk in 1:m
            piv = 0; inv = nothing; desc = ""
            for i in kk:m                                                 # a row with a recognised unit in column kk
                iszero(X[i, kk]) && continue
                res = recognise_unit(T.A, X[i, kk], zP); res === nothing && continue
                piv = i; inv, desc = res; break
            end
            piv == 0 && (ok = false; break)
            if piv != kk
                for j in 1:m; X[kk, j], X[piv, j] = X[piv, j], X[kk, j]; end
                swaps += 1
            end
            push!(pivots, desc)
            for i in kk+1:m
                iszero(X[i, kk]) && continue
                f = mul(T.A, X[i, kk], inv)                               # row_i -= (M_ik u^-1) row_k
                for j in kk+1:m; iszero(X[kk, j]) || (X[i, j] = X[i, j] - mul(T.A, f, X[kk, j])); end
                X[i, kk] = zero(T.A)
            end
        end
        testing("the block of $m cosets $(first(C, 8))$(m > 8 ? "..." : ""): elimination over H(P) with recognised units as pivots (M_C = L U)", ok;
                note = ok ? "pivots " * join(pivots, ", ") * (swaps > 0 ? "; $swaps row swaps" : "") : "no recognised unit in column $(length(pivots) + 1)")
    end
end

# Pairing, the natural pairing of a tree with the letter z: row m is x_m = (w_m with z's) and column m is
# y_m = partner(w_m) T_z^(-i_m), which represents x_m^-1; the group-point matching is the index.
function test_T4_natural(T::Table{S}, zP) where {S}
    N = T.N; k = T.q.k; z = T.ngens + 1
    sp = [zsplit(T, x) for x in T.words]; ws = Set(first.(sp)); is = sort(unique(last.(sp)))
    say("the natural partners y_m = $(k == 2 ? "rev" : "comp")(w_m) T_z^-i for x_m = w_m z^i: $(length(ws)) words w, powers i in $is")
    cols = Vector{Dict{Int,SV{S}}}(undef, N)
    for i in is
        ψi = col_word(T, colunit(S, N, 1), fill(-z, i))                   # h -> E(h T_z^-i)
        pc = partner_columns(T, ψi, ws)
        for m in 1:N
            sp[m][2] == i || continue
            c = pc[sp[m][1]]; cols[m] = Dict(n => c[n] for n in 1:N if c[n] !== nothing)
        end
        say("  i = $i: the columns computed  $(stamp())")
    end
    test_triangular(T, cols, collect(1:N), zP, "the natural pairing M(X, Y), y_m = $(k == 2 ? "rev" : "comp")(w_m) T_z^-i_m")
end

# Pairing, a second tree (Proposition 5.3 with Y_1 ≠ X; G31).  The table lives on X; Y_1 is a breadth-first tree
# with the letter z.  For y = w z^i in Y_1 (w: the letters of y other than z), T_y = T_w T_z^i since z is central, and
# its partner y' = partner(w) T_z^-i represents y^-1; Y_2 = { y' }.  The entry of M = M_X(Y_1, Y_2) at y = w z^i and
# y'_1 = partner(w_1) T_z^-i_1 is E(T_w T_partner(w_1) T_z^r), r = i - i_1: the row T_w against the column
# M_partner(w_1) ψ_r, ψ_r = M_z^r e_1 (h -> E(h T_z^r)).  Ordered by the number of letters z, M is block triangular
# if the entries with r > 0 vanish, and then invertible if every diagonal block (r = 0) is triangular with units on
# the diagonal; the entries with r < 0 are never needed.  Also tested: E(T_y) = δ_(y,1), so t(b T_y) = τ_P(b) δ_(y,1):
# t is the coefficient of 1 on B_P · Y_1 too, which is a basis since M is invertible (Lemma 5.2).
function test_T4_ztree(T::Table{S}, Y, z, zP) where {S}
    N = length(Y); k = T.q.k; sp = [zsplit(T, y) for y in Y]; imax = maximum(last.(sp))
    say("Y_1: $N words, $(count(s -> s[2] > 0, sp)) with z, at most $imax letters z; Y_2: y' = $(k == 2 ? "rev" : "comp")(w) T_z^-i for y = w z^i")
    rows = Dict{Vector{Int},Row{S}}()                                    # T_w on the table, memoised along prefixes
    rowof(w) = isempty(w) ? erow(S, 1) : get!(() -> row_gen(T, rowof(w[1:end-1]), w[end]), rows, w)
    ψ = [colunit(S, T.N, 1)]; for r in 1:imax; push!(ψ, col_word(T, ψ[end], z)); end
    for r in 1:imax; say("  the form h -> E(h T_z^$r) lives on $(length(support(ψ[r+1]))) coset(s)"); end
    bad = [m for m in 1:N if !(m == 1 ? colval(T, rowof(sp[m][1]), ψ[sp[m][2]+1]) == one(T.A) : iszero(colval(T, rowof(sp[m][1]), ψ[sp[m][2]+1])))]
    testing("E(T_y) = δ_(y,1) for the $N words y of Y_1: t(b T_y) = τ_P(b) δ_(y,1), t is the coefficient of 1 on B_P · Y_1", isempty(bad);
            details = ["y = $(wordstr(T, Y[m]))" for m in bad])
    diag = [Dict{Int,SV{S}}() for _ in 1:N]; ncomp = 0; nz = String[]
    for r in 0:imax
        js = [j for j in 1:N if any(i -> sp[i][2] == sp[j][2] + r, 1:N)]   # the columns with a row r letters z higher
        ws = Set{Vector{Int}}(); for j in js, l in 0:length(sp[j][1]); push!(ws, sp[j][1][1:l]); end
        pc = partner_columns(T, ψ[r+1], ws)
        for j in js, i in 1:N
            sp[i][2] == sp[j][2] + r || continue
            v = colval(T, rowof(sp[i][1]), pc[sp[j][1]])
            r > 0 && (ncomp += 1)
            iszero(v) && continue
            r == 0 ? (diag[j][i] = v) : push!(nz, "row $(wordstr(T, Y[i])), column partner of $(wordstr(T, Y[j]))")
        end
        say("  r = $r: $(length(js)) columns  $(stamp())")
    end
    testing("E(T_y T_y'_1) = 0 whenever y has more letters z than y_1 ($ncomp entries): by the number of letters z, M is block triangular",
            isempty(nz); note = isempty(nz) ? "" : "$(length(nz)) nonzero entries", details = nz)
    test_triangular(T, diag, collect(1:N), zP, "M_0 = (E(T_y T_y'_1)), y and y_1 with equally many letters z (the diagonal blocks of M)")
end

# Condition (3) through a central ζ with ζ^2 = π, the form h -> E(h T_ζ) on any number of cosets: on the basis
# { b x_m T_ζ }, condition (3) reads τ_P(E(x_m^-1 T_ζ) b^-1) = τ_P(b ψ_m)^* t(T_π) with ψ = M_ζ e_1.
# E(x_m^-1 T_ζ) = (M_(x_m^-1) ψ)_1: one walk of the tree from ψ, with inverse letters.
function test_T3_general(T::Table{S}, ζ, label, ψ = col_word(T, colunit(S, T.N, 1), ζ)) where {S}
    tπ = test_T3_general_head(T, ζ, label, ψ)
    w = colwalk_start(T, ψ); colwalk!(T, w; prog = progress_printer("columns", T.N))
    test_T3_general_tail(T, ψ, tπ, w)
end

end   # module Tower
