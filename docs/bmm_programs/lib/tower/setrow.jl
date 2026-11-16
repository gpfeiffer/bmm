#############################################################################
##
##  setrow.jl — the setRow procedure of bmm.pdf §3.3 on a coset table over H(P)
##
##  The engine cyclic (lib/hecke.jl) fills the coset table of A = B_U · T_o over a cyclic parabolic U = <u> by
##  sweeps of setRow commands: a row (n, σ), σ in Σ = S ∪ S^-1 ∪ {z, z^-1}, is e_n T_σ, and it is set only when
##  it can be *evaluated* from rows already known, by one of the rules
##      img   a tree edge (makeEdge), or x_1 T_s = T_s x_1 for s in P;
##      gen   T_g = r_{k-1} + r_{k-2} T_g^-1 + ... + r_0 T_g^-(k-1)        (the inverse rows of g);
##      inv   T_g^-1 = T_g^{k-1} - r_{k-1} T_g^{k-2} - ... - r_1  (r_0 = 1)   (the rows of g);
##      rel   e_n T_σ = e_n T_w for a braid identity σ = w (a rotation of a relator solved for one letter).
##  Nothing is ever solved for: the row being defined always has coefficient 1, so no unit of H(P) is inverted.
##  This file runs the same procedure with coefficients in a flat algebra H(P) (alg.jl) instead of Λ: the
##  columns of the generators and of the defined letters (z) are T.rows, those of their inverses T.invrows.
##  The procedure, the sweep order and the program format (makeEdge / setRow lines) are those of lib/hecke.jl, so
##  the programs cosettableNN.txt of G4–G29 and those written here have one format and one replay.
##
##  This is the procedure of every table of G31–G34, at every level of the tower: the same rules as for G4–G29,
##  with H(P) in place of H(U), U cyclic.
##
##  sr_init!(T)                        tree edges and the rows x T_s = T_s x (s in P, x = 1, z, z^2, ...)
##  sr_enumerate!(T, relators; ...)    sweeps until the table is complete or a sweep sets nothing; returns the
##                                     program lines, whether complete, and per sweep (set, gen, inv, rel, open)
##  sr_replay!(T, lines)               executes a program; errors if a command cannot be executed
##  sr_open(T)                         the open rows (all columns), sr_open_by_column(T) per column
##
#############################################################################

# ---- the columns ---------------------------------------------------------------------------------------------
# the column of the letter l: the rows of T_l (l > 0) or of T_l^-1 (l < 0)
colmats(T::Table, l::Int) = l > 0 ? T.rows[l] : T.invrows[-l]
sr_isopen(T::Table, n::Int, l::Int) = colmats(T, l)[n] === nothing
sr_open(T::Table) = sum(count(isnothing, R) for R in T.rows) + sum(count(isnothing, R) for R in T.invrows)
sr_open_by_column(T::Table) = Dict(l => count(isnothing, colmats(T, l)) for l in vcat(1:T.nletters, -T.nletters:-1))
sr_columns(T::Table) = vcat(1:T.nletters, -T.nletters:-1)              # the sweep order of lib/hecke.jl: 1..n+1, then -(n+1)..-1

# the rows read by the commands, recorded when DEPS[] is a set (exp/prune.jl: the dependency closure of a program)
const DEPS = Ref{Union{Nothing,Set{Tuple{Int,Int}}}}(nothing)
# v T_l read strictly from the table: nothing while a row it needs is open (the setRow semantics)
function sr_mat(T::Table{S}, v::Row{S}, l::Int) where {S}
    R = colmats(T, l)
    for (k, _) in v; R[k] === nothing && return nothing; end
    DEPS[] === nothing || for (k, _) in v; push!(DEPS[], (Int(k), l)); end
    for (k, h) in v, (m, g) in R[k]; radd!(T, m, mul(T.A, h, g)); end
    rcollect!(T)
end
function sr_word(T::Table{S}, v::Row{S}, w) where {S}
    for l in w; v = sr_mat(T, v, l); v === nothing && return nothing; end
    v
end
sr_add(v::Row, w::Row) = isempty(w) ? v : isempty(v) ? w : radd(v, w)

# ---- the rules gen and inv -----------------------------------------------------------------------------------
# e_n T_g = r_{k-1} e_n + r_{k-2} e_n T_g^-1 + ... + r_0 e_n T_g^-(k-1)
function sr_gen(T::Table{S}, n::Int, g::Int) where {S}
    r = T.q.r; k = length(r); v = erow(S, n); out = rscale(v, r[k])
    for j in k-1:-1:1
        v = sr_mat(T, v, -g); v === nothing && return nothing
        out = sr_add(out, rscale(v, r[j]))
    end
    out
end
# e_n T_g^-1 = e_n T_g^{k-1} - r_{k-1} e_n T_g^{k-2} - ... - r_1 e_n     (r_0 = 1)
function sr_inv(T::Table{S}, n::Int, g::Int) where {S}
    r = T.q.r; k = length(r); v = erow(S, n); out = rscale(v, -r[2])
    for j in 3:k
        v = sr_mat(T, v, g); v === nothing && return nothing
        out = sr_add(out, rscale(v, -r[j]))
    end
    v = sr_mat(T, v, g); v === nothing && return nothing
    sr_add(out, v)
end

# ---- setRow and makeEdge -------------------------------------------------------------------------------------
# setRow!(T, n, l, w, rule): row (n, l) := rule(n, l, w); false, setting nothing, if a row it needs is open
function setRow!(T::Table{S}, n::Int, l::Int, w, rule::Symbol) where {S}
    if rule == :img
        v = w
    elseif rule == :rel
        v = sr_word(T, erow(S, n), w)
    elseif rule == :gen
        l > 0 || error("setRow: the rule gen needs a generator column")
        v = sr_gen(T, n, l)
    elseif rule == :inv
        l < 0 || error("setRow: the rule inv needs an inverse column")
        v = sr_inv(T, n, -l)
    else
        error("setRow: unknown rule $rule")
    end
    v === nothing && return false
    R = colmats(T, l)
    R[n] === nothing || error("row ($n, $l) set twice")
    R[n] = v
    true
end
# the tree edge x_m = x_n l: e_n T_l = e_m and e_m T_l^-1 = e_n
function makeEdge!(T::Table{S}, n::Int, m::Int, l::Int) where {S}
    setRow!(T, n, l, erow(S, m), :img)
    setRow!(T, m, -l, erow(S, n), :img)
    nothing
end
# the rows x T_s^±1 = T_s^±1 x for s in P on the cosets x = 1, z, z^2, ... (the engine cyclic sets
# e_1 T_u^±1 = u^±1 e_1 at the construction of the table); implicit in every program
function sr_init_one!(T::Table{S}) where {S}
    for n in zpowers(T), s in T.subset
        sr_isopen(T, n, s) && setRow!(T, n, s, Row{S}([(Int32(n), Tgen(T, s))]), :img)
        sr_isopen(T, n, -s) && setRow!(T, n, -s, Row{S}([(Int32(n), element(T.A, [-T.pindex[s]]))]), :img)
    end
end
# the initialisation: the tree edges and the rows above.  Returns the edges (n, m, l).
function sr_init!(T::Table{S}) where {S}
    edges = Tuple{Int,Int,Int}[]
    for m in 2:T.N
        n = T.parent[m]; l = T.letter[m]
        makeEdge!(T, n, m, l); push!(edges, (n, m, l))
    end
    sr_init_one!(T)
    edges
end

# ---- the identities σ = w used by the rule rel ----------------------------------------------------------------
# every rotation of every relator (and of its inverse), solved for its first letter, freely reduced; shortest first
function sr_relation_words(relators)
    D = Dict{Int,Vector{Vector{Int}}}()
    for r0 in relators, r in (r0, -reverse(r0)), j in eachindex(r)
        ρ = vcat(r[j:end], r[1:j-1]); w = Int[]
        for g in -reverse(ρ[2:end]); (!isempty(w) && w[end] == -g) ? pop!(w) : push!(w, g); end
        isempty(w) || w in get!(D, ρ[1], Vector{Int}[]) || push!(D[ρ[1]], w)
    end
    foreach(L -> sort!(L, by = length), values(D))
    D
end
# the relators of a level: l r^-1 for the relations (l, r) in the letters of the level; with the letter z
# (nletters = ngens + 1): z^-1 zword and z s z^-1 s^-1 for every generator s
function sr_relators(T::Table, relations; central = true)
    rels = [vcat(l, -reverse(r)) for (l, r) in relations]
    if T.nletters > T.ngens
        Z = T.ngens + 1
        push!(rels, vcat([-Z], xword(T, Z)))
        central && for s in 1:T.ngens; push!(rels, [Z, s, -Z, -s]); end
    end
    rels
end

# ---- the sweeps ---------------------------------------------------------------------------------------------
# one sweep (findRows of lib/hecke.jl): on every open row (n, l), in the column order of sr_columns, try gen or
# inv, then the identities l = w; returns the setRow lines applied
function sr_sweep!(T::Table, RW::Dict{Int,Vector{Vector{Int}}})
    lines = String[]; ng = T.ngens
    for l in sr_columns(T), n in 1:T.N
        sr_isopen(T, n, l) || continue
        if 0 < l <= ng && setRow!(T, n, l, 0, :gen)
            push!(lines, "setRow($n, $l, 0, gen)")
        elseif -ng <= l < 0 && setRow!(T, n, l, 0, :inv)
            push!(lines, "setRow($n, $l, 0, inv)")
        else
            for w in get(RW, l, Vector{Int}[])
                setRow!(T, n, l, w, :rel) && (push!(lines, "setRow($n, $l, [$(join(w, ", "))], rel)"); break)
            end
        end
    end
    lines
end
# the procedure of §3.3: the initialisation, then sweeps until the table is complete or a sweep sets nothing.
# Returns the lines of the program (the edges as makeEdge lines, "# sweep N" before each sweep), whether every
# column is complete, and per sweep (rows set, by gen, by inv, by rel, rows still open)
function sr_enumerate!(T::Table, relators; maxpasses = 500, report = nothing, init = true)
    RW = sr_relation_words(relators)
    lines = String[]
    if init
        edges = sr_init!(T)
        append!(lines, ["makeEdge($n, $m, $l)" for (n, m, l) in edges])
    end
    passes = NTuple{5,Int}[]
    for pass in 1:maxpasses
        push!(lines, "# sweep $pass"); new = sr_sweep!(T, RW); append!(lines, new)
        c(s) = count(endswith(s), new)
        push!(passes, (length(new), c("gen)"), c("inv)"), c("rel)"), sr_open(T)))
        report === nothing || report(pass, passes[end])
        (sr_open(T) == 0 || isempty(new)) && return lines, sr_open(T) == 0, passes
    end
    lines, false, passes
end

# ---- the replay --------------------------------------------------------------------------------------------
# a word "1, -2, 3" of a program line
sr_parseword(s) = (s = strip(s); isempty(s) ? Int[] : parse.(Int, split(s, ",")))
# executes a program (the lines of a cosettable file); every command must execute.  Returns the number of
# setRow commands and the tree edges.
function sr_replay!(T::Table, lines; progress = nothing, init_one = true)
    n = 0; edges = Tuple{Int,Int,Int}[]
    init_one && sr_init_one!(T)                           # the rows x T_s = T_s x, implicit in the program
    for ln in lines
        if (m = match(r"^makeEdge\((\d+), (\d+), (-?\d+)\)", ln)) !== nothing
            i, k, g = parse.(Int, m.captures)
            (T.act[i, g] == k && T.parent[k] == i && T.letter[k] == g) || error("$ln: not an edge of the tree")
            makeEdge!(T, i, k, g); push!(edges, (i, k, g))
        elseif (m = match(r"^setRow\((\d+), (-?\d+), \[([-0-9, ]*)\], rel\)", ln)) !== nothing
            i, g = parse.(Int, m.captures[1:2]); w = sr_parseword(m[3])
            setRow!(T, i, g, w, :rel) || error("$ln: a row it needs is open"); n += 1
        elseif (m = match(r"^setRow\((\d+), (-?\d+), 0, (gen|inv)\)", ln)) !== nothing
            i, g = parse.(Int, m.captures[1:2])
            setRow!(T, i, g, 0, Symbol(m[3])) || error("$ln: a row it needs is open"); n += 1
        end
        progress === nothing || progress(n)
    end
    n, edges
end
# the relation words of a replayed program are checked to be identities of the braid group: every rel line's
# word must be one of the rotations of the given relators (so that a program proves spanning on its own)
function sr_check_program(lines, relators)
    RW = sr_relation_words(relators); bad = String[]
    for ln in lines
        m = match(r"^setRow\((\d+), (-?\d+), \[([-0-9, ]*)\], rel\)", ln); m === nothing && continue
        g = parse(Int, m[2]); w = sr_parseword(m[3])
        w in get(RW, g, Vector{Int}[]) || push!(bad, ln)
    end
    bad
end

# the size of the table, all columns
function sr_statistics(T::Table)
    rows = [r for l in sr_columns(T) for r in colmats(T, l) if r !== nothing]; supp = length.(rows)
    terms = [nterms(h) for r in rows for (_, h) in r]
    "rows: $(length(rows)); cosets per row: mean $(round(sum(supp) / length(supp), digits = 2)), max $(maximum(supp)); " *
    "entries: $(sum(supp)); terms per entry: mean $(round(sum(terms) / length(terms), digits = 1)), max $(maximum(terms))"
end
