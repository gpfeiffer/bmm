#############################################################################
##
##  report.jl — the form of the output of the programs
##
##  A record is short: a title and the data of the group, then, for each
##  stage of the computation, a line  ==== <stage> ====, one line
##        testing <identity> ... true
##  per tested identity, the numbers found (progress lines if the stage is
##  long), and the time and peak memory of the stage; at the end the result.
##  What is tested and why follows bmm.pdf: a stage that verifies a statement of bmm.pdf cites it in its
##  title; a stage that checks the implementation or prints data cites nothing.
##  Everything said is printed and, after record(S, "N_name.txt"), also written to the record file
##  GNN/N_name.txt of the group (first line: the command and the date; last line: the exit code, by finish).
##
#############################################################################

using Printf, Dates

const T0 = time()
# a run resumed from a checkpoint (lib/tower/driver.jl): the time spent and the peak memory of the processes before it
const T_BEFORE = Ref(0.0)
const RSS_BEFORE = Ref(UInt64(0))
elapsed() = time() - T0 + T_BEFORE[]                                # the time of the run so far
const WIDTH = 110
const NTESTS = Ref(0); const NFALSE = Ref(0)                  # the tested identities, and those found false

const RECORD = Ref{Union{Nothing,IOStream}}(nothing)
const SILENT = Ref(false)            # true while a run resumed from a checkpoint rebuilds its tables: nothing is said or counted
# a line printed, and written to the record (flushed at once: the record is live)
function say(s = "")
    SILENT[] && return
    println(s)
    RECORD[] === nothing || (println(RECORD[], s); flush(RECORD[]))
    flush(stdout)
end
# the record file of the program: from now on everything said is also written to GNN/name
function record(S, name::AbstractString)
    RECORD[] = open(joinpath(S.dir, name), "w")
    say("# $(Dates.format(now(), "yyyy-mm-dd HH:MM:SS"))  julia programs/$(basename(PROGRAM_FILE)) $(join(ARGS, " "))")
end
# the last line of the record, and the end of the program
function finish(code::Int = 0)
    say("# $(Dates.format(now(), "yyyy-mm-dd HH:MM:SS"))  exit code $code")
    RECORD[] === nothing || close(RECORD[])
    exit(code)
end
# the value of the option --n=... of the command line, d if it is not given
function argval(n, d)
    for a in ARGS
        startswith(a, "--$n=") && return split(a, "=", limit = 2)[2]
    end
    d
end
# a duration as text: 8.6 s, 1 min 02 s, 2 h 05 min
function hms(t)
    t < 60 && return @sprintf("%.1f s", t)
    t < 3600 && return @sprintf("%d min %02d s", floor(Int, t / 60), floor(Int, t % 60))
    @sprintf("%d h %02d min", floor(Int, t / 3600), floor(Int, (t % 3600) / 60))
end
mem() = @sprintf("%.2f GB", max(Sys.maxrss(), RSS_BEFORE[]) / 2^30)   # the peak memory so far
stamp() = "[$(hms(elapsed())), $(mem())]"                          # [time since the start, peak memory]

# a line wrapped at WIDTH (at spaces; "~" is a space at which the line is not broken)
function wrapped(text; rest = "    ")
    line = ""; fresh = true
    for w in split(text, ' '; keepempty = false)
        if !fresh && length(line) + 1 + length(w) > WIDTH
            say(replace(line, "~" => " ")); line = rest * w
        else
            line = fresh ? line * w : line * " " * w
        end
        fresh = false
    end
    say(replace(line, "~" => " "))
end

# one tested identity: "testing <what> ... true (note)"
function testing(what, ok::Bool; note = "")
    SILENT[] && return ok
    NTESTS[] += 1; ok || (NFALSE[] += 1)
    say("testing $what ... $(ok ? "true" : "FALSE")" * (isempty(note) ? "" : " ($note)"))
    ok
end
const STAGE_T = Ref(0.0)                                            # the start of the current stage
# the end of a stage: its time and the peak memory so far
function endstage()
    STAGE_T[] > 0 && say(lpad("[time $(hms(time() - STAGE_T[])), memory $(mem())]", WIDTH))
    STAGE_T[] = 0.0
end
# ==== <text> ======...   a stage begins (and the previous one ends)
function stage(text)
    endstage(); STAGE_T[] = time()
    say("==== $text " * "="^max(4, WIDTH - length(text) - 6))
end
alltrue() = NFALSE[] == 0
# the count of the tests, for the line Result
tests() = NFALSE[] == 0 ? "all $(NTESTS[]) tests true" : "$(NFALSE[]) of $(NTESTS[]) tests FALSE"
# the last lines of a record
function total()
    STAGE_T[] = 0.0                               # the last stage is the result: no time line of its own
    say("="^WIDTH); say(lpad("[total time $(hms(elapsed())), peak memory $(mem())]", WIDTH))
end

# progress inside a long stage: at most one line every PROGRESS_SECONDS (environment, default 30)
const PROGRESS_SECONDS = parse(Float64, get(ENV, "PROGRESS_SECONDS", "30"))
# a function i -> the progress line "label: i / total", printed at most every PROGRESS_SECONDS
function progress_printer(label::AbstractString, total::Integer; t0 = time())   # t0: the start of the count
    last = Ref(time())
    function (i)
        time() - last[] < PROGRESS_SECONDS && return
        last[] = time()
        say("  ... $label: $i / $total  [$(hms(time() - t0)), $(mem())]")
    end
end

# ---- notation ----------------------------------------------------------------------------------------------
const SUPS = Dict(zip("0123456789-", "⁰¹²³⁴⁵⁶⁷⁸⁹⁻"))
sup(n::Integer) = n == 1 ? "" : map(c -> SUPS[c], string(n))      # an exponent as a superscript (none for 1)
letter(S, g) = abs(g) == zletter(S) ? "z" : S.letters[abs(g)]      # the name of the letter ±g
# a braid word in the letters of the group, consecutive equal letters as powers: wordstr gives s t² s⁻¹,
# Tword the element T_s T_t² T_s⁻¹ of H
function wordstr(S, w; T = "")
    isempty(w) && return "1"
    parts = String[]; i = 1
    while i <= length(w)
        j = i; while j < length(w) && w[j+1] == w[i]; j += 1; end
        push!(parts, T * letter(S, w[i]) * sup(sign(w[i]) * (j - i + 1)))
        i = j + 1
    end
    join(parts, " ")
end
Tword(S, w) = wordstr(S, w; T = "T_")
# the Hecke relation of letter g: T_g^k = r_{k-1} T_g^{k-1} + ... + r_0  (prime: over R', where r_0 = 1)
function heckerel(S, g; prime = false)
    p = S.params[S.classes[g]]; k = length(p); T = "T_" * S.letters[g]
    function term(j)                                                    # r_j T_g^j
        c = (prime && j == 0) ? "1" : p[j+1]
        j == 0 ? c : "$c $T$(sup(j))"
    end
    "$T$(sup(k)) = " * join([term(j) for j in k-1:-1:0], " + ")
end
ringR(S) = "Z[$(join(others(S), ", "))][$(join(invertibles(S), "^±1, "))^±1]"   # R = Z[r_j][r_0^±1]
uname(S) = "T_" * S.letters[S.parabolic]                                         # T_u
zk(S) = S.zstep == 1 ? "z" : "z$(sup(S.zstep))"                       # z^k, the central element of the basis
basisname(S) = S.zstep == 1 ? "z-basis" : "z$(sup(S.zstep))-basis"
# the element of A or of B with a given index, in words
function aname(S, i, m)
    um = "$(uname(S))$(sup(m))"                                         # T_u^m
    i == 1 && return m == 0 ? "1" : um
    m == 0 ? "T_(w_$i)" : "$um T_(w_$i)"
end

# the header of a record: what the program does, and the data of the group
function header(S, what, program)
    n = ngens(S)
    left = " H($(S.name)): $what"; right = "$program, $(Dates.format(now(), "yyyy-mm-dd HH:MM")) "
    say("="^WIDTH); say(left * lpad(right, max(length(right) + 2, WIDTH - length(left)))); say("="^WIDTH)
    orders = allequal(S.orders) ? "order $(S.orders[1])" : "orders " * join(S.orders, ", ")
    braids = join([replace(wordstr(S, a) * " = " * wordstr(S, b), " " => "~") for (a, b) in S.braid], "; ")
    wrapped("W = $(S.name), |W| = $(S.order); generators " * join(S.letters, ", ") * " of $orders; $braids")
    rels = String[]
    for g in 1:n
        any(h -> S.classes[h] == S.classes[g], 1:g-1) && continue
        same = [S.letters[h] for h in g+1:n if S.classes[h] == S.classes[g]]
        push!(rels, replace(heckerel(S, g), " " => "~") * (isempty(same) ? "" : " (same for T_" * join(same, ", T_") * ")"))
    end
    wrapped(join(rels, "; "))
    zline = "z~=~$(replace(wordstr(S, S.zword), " " => "~")); π~=~z$(sup(S.pipower))"
    if S.engine == "cyclic"
        wrapped("U = <$(S.letters[S.parabolic])>, e = $(paradeg(S)), $(ncosets(S)) cosets; " * zline)
    else                                         # the tower of parabolics of the group file (engine tower)
        tower = ["<" * join([S.letters[g] for g in parseword(string(L["gens"]))], ", ") * ">" for L in S.levels]
        wrapped("tower 1 < " * join(tower, " < ") * " < W (engine $(S.engine)); " * zline)
    end
end
ordername(S, o = S.bfs) = "(" * join([letter(S, g) for g in o], ", ") * ")"           # an ordering: (s1, s2, z)
# the point of R' of a modular computation, cp the parameters class by class: "d1, d2 = 11, 13; d0 = 1"
function pointline(S, cp)
    vals = ["$(join(S.params[c][2:end], ", ")) = $(join(symm.(cp[c][2:end]), ", "))"
            for c in 1:nclasses(S) if length(cp[c]) > 1]
    join(vals, "; ") * "; " * join(invertibles(S), " = ") * " = 1"
end
# B = { T_z^(2j) T_s^m T_x : j < 5, m < 5, x in X }, |X| = 24
function basisline(S, nX)
    zj = S.zstep == 1 ? "j" : "($(S.zstep)j)"
    "B = { T_z^$zj $(uname(S))^m T_x : j < $(S.zlevels), m < $(paradeg(S)), x in X }, |X| = $nX ($(S.basis))"
end

# a polynomial of R' (or an integer mod p) as text: 3*d1^2*d4 - 1
function pretty(p)
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
