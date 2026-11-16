#############################################################################
##
##  cantrace.jl — the canonical trace τ for the engine tower
##                (G31, G32, G33, G34; bmm.pdf, Section 5)
##
##  The records GNN/3_bmm_proof.txt show that the basis B of each group is
##  quasi-symmetric, so the canonical trace is the coefficient of 1 on B:
##  τ(T_w) = λ_1^B(T_w) (bmm.pdf, Proposition 5.3 (the parabolic criterion)
##  and Theorem 5.6 (the conjecture for all exceptional groups)).  The
##  interface is that of lib/trace.jl for G4..G29:
##      can_trace(T, w)    τ(T_w) in R(W), for a word w (letters 1..n the
##                         generators, n+1 = z, negative = inverse) or a list
##                         of words
##      trace(T, w)        the value in the ring of the computation (R' =
##                         R/(e0 - 1) = Z[e1] for G31, G33, G34,
##                         R/(c0 - 1) = Z[c1, c2] for G32)
##  T = CanTrace(name, n, k, zword, ring, coef1) is returned by build_trace(S)
##  of the engine's driver (lib/tower/driver.jl), which load_trace
##  (lib/trace.jl) calls; coef1(w) is the coefficient of 1 of T_w on B,
##  read off the coordinates of T_w on the completed table.  The record
##  GNN/4_trace_values.txt is written by the driver through lib/report.jl.
##
##  From the ring of the computation to R(W).  R(W) is graded (deg e1 = 1,
##  deg e0 = 2; deg c_j = 3 - j) and τ(T_w) is homogeneous of degree ℓ(w),
##  the exponent sum of w (the homogeneity argument of bmm.pdf of 3 Nov,
##  Lemmas 5.6, 5.7):
##    Z[e1]     T² = e1 T + 1        e1^a (degree a) is the image of e1^a e0^((ℓ-a)/2)
##    Z[c1,c2]  T³ = c2T² + c1T + 1  c1^a c2^b (degree 2a + b) is the image of c1^a c2^b c0^((ℓ-2a-b)/3)
##  Values are Chevie Mvp's in e0, e1 (c0, c1, c2), printed as in the records of G4..G29.
##
#############################################################################

using Chevie

struct CanTrace
    name::String
    ngens::Int
    k::Int                                  # the order of the generators (one class of reflections)
    zword::Vector{Int}                      # the central element z as a word in the generators
    ring::Symbol                            # :e (Z[e1]) or :c (Z[c1,c2])
    coef1::Function                         # w (letters ±1..±n) -> the coefficient of 1 of T_w on B
end
zletter(T::CanTrace) = T.ngens + 1

# the word with z expanded
function expandz(T::CanTrace, w::Vector{Int})
    out = Int[]
    for l in w
        if abs(l) <= T.ngens
            push!(out, l)
        elseif abs(l) == zletter(T)
            append!(out, l > 0 ? T.zword : -reverse(T.zword))
        else
            error("the letter $l is not a generator (1..$(T.ngens)) or z ($(zletter(T)))")
        end
    end
    out
end
wdegree(T::CanTrace, w) = sum(sign, expandz(T, w); init = 0)            # ℓ(w), the degree of τ(T_w)

# τ(T_w) in the ring of the computation
trace(T::CanTrace, w::Vector{Int}) = T.coef1(expandz(T, w))
# THE CANONICAL TRACE τ(T_w) in R(W), for a word or a list of words
can_trace(T::CanTrace, w::Vector{Int}) = lift_to_R(T, trace(T, w), wdegree(T, w))
can_trace(T::CanTrace, ws::Vector{Vector{Int}}) = [can_trace(T, w) for w in ws]

# the default words of the step traces (lib/tower/driver.jl): T_1^j (-2 <= j <= k), T_1 T_2,
# T_1 T_2^-1, T_1^-1 T_2^-1, then the Coxeter element T_1 ... T_n, T_z and T_z^-1
function default_words(n::Int, k::Int)
    ws = [fill(sign(j), abs(j)) for j in vcat(-2:-1, 1:k)]
    append!(ws, [[1, 2], [1, -2], [-1, -2], collect(1:n), [n + 1], [-(n + 1)]])
end

# ---- the lift to R(W) --------------------------------------------------------------------------------------
const E0 = Mvp(:e0); const E1 = Mvp(:e1); const C0 = Mvp(:c0); const C1 = Mvp(:c1); const C2 = Mvp(:c2)
# τ(T_w) in R(W) from its value p of degree D = ℓ(w) (the engine tower has its own method, lib/tower/driver.jl)
function lift_to_R(T::CanTrace, p, D::Int)
    out = zero(E0)
    for (key, c) in p.t                               # terms (packed exponents, coefficient)
        e = exponents(key)
        if T.ring == :e
            a = e[1]; m, r = fldmod(D - a, 2)
            r == 0 || error("lift_to_R: the term e^$a of a value of degree $D")
            out += c * E1^a * E0^m
        else
            a, b = e[1], e[2]; m, r = fldmod(D - 2a - b, 3)
            r == 0 || error("lift_to_R: the term c1^$a c2^$b of a value of degree $D")
            out += c * C1^a * C2^b * C0^m
        end
    end
    out
end
# an element of R(W) as text, as in the records of G4..G29: 3*e0^-2*e1^2 - e0^-1
function pretty(p::Mvp)
    iszero(p) && return "0"
    ts = String[]
    for (mon, c) in pairs(p.d)
        m = join([e == 1 ? string(v) : "$v^$e" for (v, e) in pairs(mon.d)], "*")
        if isempty(m)
            push!(ts, string(c))
        elseif c == 1
            push!(ts, m)
        elseif c == -1
            push!(ts, "-" * m)
        else
            push!(ts, "$c*$m")
        end
    end
    replace(join(ts, " + "), "+ -" => "- ")
end
