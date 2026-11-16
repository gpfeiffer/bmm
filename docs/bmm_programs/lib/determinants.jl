#############################################################################
##
##  determinants.jl — exact determinants of matrices of polynomials
##
##  det_bareiss: fraction-free Bareiss elimination on Chevie polynomials
##  with BigInt coefficients.  Every division is exact by Sylvester's
##  identity, so the result is a polynomial identity; the pivot is the
##  sparsest nonzero entry of the current column.
##
#############################################################################

const RB = Mvp{BigInt,Int64}
maxabs(x::RB) = maximum((abs(c) for (_, c) in pairs(x.d)); init = BigInt(0))      # the largest |coefficient|

# det M (verbose: progress lines and the size of the entries)
function det_bareiss(M::AbstractMatrix; verbose::Bool = false)
    n = size(M, 1); n == size(M, 2) || error("det_bareiss: matrix not square")
    A = Matrix{RB}(M); n == 0 && return one(RB)
    sgn = 1; prev = one(RB); t0 = time()
    maxterms = maximum(x -> length(x.d), A)             # the largest entry and coefficient, for the record
    maxcoeff = maximum(maxabs, A)
    for k in 1:n-1
        piv = 0; best = typemax(Int)                    # the sparsest nonzero entry of column k
        for i in k:n
            iszero(A[i, k]) || length(A[i, k].d) >= best || (best = length(A[i, k].d); piv = i)
        end
        piv == 0 && return zero(RB)
        if piv != k
            for j in k:n; A[k, j], A[piv, j] = A[piv, j], A[k, j]; end
            sgn = -sgn
        end
        pk = A[k, k]
        for i in k+1:n
            aik = A[i, k]
            for j in k+1:n
                A[i, j] = exactdiv(iszero(aik) ? A[i, j] * pk : A[i, j] * pk - aik * A[k, j], prev)
                maxterms = max(maxterms, length(A[i, j].d)); maxcoeff = max(maxcoeff, maxabs(A[i, j]))
            end
            A[i, k] = zero(RB)
        end
        prev = pk
        if verbose && (k % 50 == 0 || k == n-1 || length(pk.d) > 4)
            println("  ... bareiss step $k / $(n-1): pivot has $(length(pk.d)) terms  [$(round(time()-t0, digits=1)) s]")
            flush(stdout)
        end
    end
    verbose && println("  ... bareiss: largest |coefficient| $maxcoeff, largest entry $maxterms terms")
    sgn == 1 ? A[n, n] : -A[n, n]
end
