local _dir = debug.getinfo(1, "S").source:sub(2):match("(.*[/\\])") or "./"
local function lrequire(name)
    local key = _dir .. name
    if not package.loaded[key] then
        package.loaded[key] = assert(loadfile(_dir .. name .. ".lua"))()
    end
    return package.loaded[key]
end

local UndoStack  = require("undo_stack")
local Timer      = require("timer")
local Hint       = require("hint")
local grid_utils = require("grid_utils")

local Solver = lrequire("solver")

local shuffle   = grid_utils.shuffle
local emptyGrid = grid_utils.emptyGrid

-- A domino's state, both in the solution and in the player's grid. The
-- numbers 1..3 are also the solver's option indices.
local D_EMPTY   = 0   -- player only: not decided yet
local D_NEUTRAL = 1   -- blank domino, no poles
local D_PLUS    = 2   -- first cell (top / left) +, second cell -
local D_MINUS   = 3   -- first cell -, second cell +

-- What one cell shows, derived from its domino.
local C_EMPTY   = 0
local C_PLUS    = 1
local C_MINUS   = 2
local C_NEUTRAL = 3

local SIZES        = { 6, 8, 10 }
local DEFAULT_N    = 8
local DEFAULT_DIFF = "medium"

local DIR4 = { { -1, 0 }, { 1, 0 }, { 0, -1 }, { 0, 1 } }

-- Per difficulty: the solver tier the puzzle must need (see solver.lua: 1 =
-- bounds on single lines plus "no like poles side by side", 2 = exact line
-- reasoning) and `steps`, the window of line-reasoning steps it must need
-- (Solver.grade: tier-2 deductions on one line each, everything else at
-- tier 1): none on easy, exactly one on medium, at least two on hard.
-- Medium and hard used to differ only by how many clues were hidden, and
-- both mostly needed a single such step. Tier 3 (one-step trial) is never
-- asked for: on paper it plays as guessing.
-- `max_hide` is how many clues may be hidden, as a multiple of n (of the
-- 4n); easy shows every clue. `max_tries` caps how many clue removals are
-- attempted, as a multiple of n: each attempt is a solve. `max_digs` caps,
-- per size, how many candidate grids are dug before the closest one to the
-- window is kept (a measured count, so generation stays well under a
-- second on a Kobo; the share of puzzles inside the window is in the
-- specs). `pre` skips, before digging, a candidate whose full-clue puzzle
-- already needs more steps than medium allows. `full_tier`, when set, only
-- digs candidates that need the level's tier with every clue shown.
local LEVELS = {
    easy   = { tier = 1, neutral = 0.20, steps = { 0, 0 }, max_digs = {},
               max_hide = 0, max_tries = 0 },
    medium = { tier = 2, neutral = 0.20, steps = { 1, 1 }, pre = { 0, 1 },
               max_digs = { [6] = 12, [8] = 8, [10] = 6 },
               max_hide = 0.5, max_tries = 4 },
    hard   = { tier = 2, neutral = 0.20, steps = { 2, math.huge },
               max_digs = { [6] = 30, [8] = 10, [10] = 5 },
               max_hide = 2, max_tries = 2 },
}

-- Candidate grids per puzzle at most (most are rejected before any dig).
local MAX_ATTEMPTS = 160

-- ---------------------------------------------------------------------------
-- Generator
-- ---------------------------------------------------------------------------

-- Random domino tiling of an n x n grid (n even): start from rows of
-- horizontal dominoes and rotate random 2x2 blocks covered by two parallel
-- dominoes. Returns dom_id[r][c] and dominoes[d] = { r1, c1, r2, c2 } with
-- the first cell top or left.
local function makeTiling(n)
    local id = emptyGrid(n, n, 0)
    -- mate[i] = the other half of cell i, cells numbered (r - 1) * n + c
    local mate = {}
    for r = 1, n do
        for c = 1, n, 2 do
            local i = (r - 1) * n + c
            mate[i], mate[i + 1] = i + 1, i
        end
    end
    for _ = 1, n * n * 12 do
        local r, c = math.random(n - 1), math.random(n - 1)
        local i = (r - 1) * n + c
        local m = mate[i]
        if m == i + 1 then
            local j = i + n
            if mate[j] == j + 1 then   -- two horizontals -> verticals
                mate[i], mate[j], mate[i + 1], mate[j + 1] = j, i, j + 1, i + 1
            end
        elseif m == i + n then
            if mate[i + 1] == i + 1 + n then   -- two verticals -> horizontals
                mate[i], mate[i + 1], mate[i + n], mate[i + n + 1] = i + 1, i, i + n + 1, i + n
            end
        end
    end
    local dominoes = {}
    for r = 1, n do
        for c = 1, n do
            if id[r][c] == 0 then
                local m = mate[(r - 1) * n + c] - 1
                local r2, c2 = math.floor(m / n) + 1, m % n + 1
                dominoes[#dominoes + 1] = { r, c, r2, c2 }
                id[r][c], id[r2][c2] = #dominoes, #dominoes
            end
        end
    end
    return id, dominoes
end

-- Sign of cell `which` (1 = first, 2 = second) of a domino in state `k`.
local function cellSign(k, which)
    if k == D_PLUS then return which == 1 and C_PLUS or C_MINUS end
    if k == D_MINUS then return which == 1 and C_MINUS or C_PLUS end
    if k == D_NEUTRAL then return C_NEUTRAL end
    return C_EMPTY
end

-- Tables the solver memoises on, shared between candidate grids whenever
-- they are equal: forbidden-pair tables (by pattern), contribution vectors
-- (by value) and, per (pole, halves on the line), a line's vector.
local SHARED_BAD, SHARED_CONTRIB, LINE_CONTRIB = {}, {}, {}

local function sharedContrib(a, b, c)
    local key = a * 100 + b * 10 + c
    local v = SHARED_CONTRIB[key]
    if not v then
        v = { a, b, c }
        SHARED_CONTRIB[key] = v
    end
    return v
end

-- Forbidden option pairs between neighbouring dominoes: like poles may not
-- touch orthogonally. One table per pair of dominoes, merging every contact.
local function buildPairs(n, dom_id, dominoes)
    local by_key, list = {}, {}
    for d, dm in ipairs(dominoes) do
        for which = 1, 2 do
            local r, c = dm[which * 2 - 1], dm[which * 2]
            for _, dir in ipairs(DIR4) do
                local r2, c2 = r + dir[1], c + dir[2]
                if r2 >= 1 and r2 <= n and c2 >= 1 and c2 <= n then
                    local e = dom_id[r2][c2]
                    if e > d then
                        local em = dominoes[e]
                        local which2 = (em[1] == r2 and em[2] == c2) and 1 or 2
                        local key = d * 10000 + e
                        local p = by_key[key]
                        if not p then
                            p = { a = d, b = e, bad = {} }
                            by_key[key], list[#list + 1] = p, p
                        end
                        for ka = 2, 3 do
                            for kb = 2, 3 do
                                if cellSign(ka, which) == cellSign(kb, which2) then
                                    p.bad[ka] = p.bad[ka] or {}
                                    p.bad[ka][kb] = true
                                end
                            end
                        end
                    end
                end
            end
        end
    end
    -- Equal tables are shared (the solver memoises on them, so its work
    -- carries over from one candidate grid to the next).
    for _, p in ipairs(list) do
        local key = 0
        for ka = 2, 3 do
            for kb = 2, 3 do
                key = key * 2 + ((p.bad[ka] and p.bad[ka][kb]) and 1 or 0)
            end
        end
        if not SHARED_BAD[key] then SHARED_BAD[key] = p.bad end
        p.bad = SHARED_BAD[key]
    end
    return list
end

-- clues = { row_plus = {}, row_minus = {}, col_plus = {}, col_minus = {} };
-- false = hidden.
local CLUE_KINDS = { "row_plus", "row_minus", "col_plus", "col_minus" }

-- The generator builds one problem per candidate grid, with every clue,
-- and hides clues by switching their sums off (P.off): `sum_of[kind][line]`
-- and `blank_of[line key]` give the sums' indices.
local function buildProblem(n, dominoes, clues)
    local P = { nvars = #dominoes, ksize = {}, sums = {}, pairs = nil,
                sum_of = {}, blank_of = {} }
    -- the dominoes on each line, ascending (dom), and which of their
    -- halves lie on it (half: 1 or 2, 0 = both)
    local dom, half = { r = {}, c = {} }, { r = {}, c = {} }
    for line = 1, n do
        dom.r[line], dom.c[line], half.r[line], half.c[line] = {}, {}, {}, {}
    end
    local function add(axis, line, d, h)
        local list = dom[axis][line]
        list[#list + 1] = d
        half[axis][line][#list] = h
    end
    for d = 1, #dominoes do
        P.ksize[d] = 3
        local dm = dominoes[d]
        if dm[1] == dm[3] then add("r", dm[1], d, 0) else add("r", dm[1], d, 1); add("r", dm[3], d, 2) end
        if dm[2] == dm[4] then add("c", dm[2], d, 0) else add("c", dm[2], d, 1); add("c", dm[4], d, 2) end
    end
    for _, kind in ipairs(CLUE_KINDS) do
        local is_row  = kind:sub(1, 3) == "row"
        local want    = kind:sub(-4) == "plus" and C_PLUS or C_MINUS
        P.sum_of[kind] = {}
        for line = 1, n do
            local clue = clues[kind][line]
            if clue then
                local s = { clue = clue, vars = {}, contrib = {} }
                local axis = is_row and "r" or "c"
                local ds, hs = dom[axis][line], half[axis][line]
                for j = 1, #ds do
                    local h = hs[j]
                    local key = want * 3 + h
                    local cc = LINE_CONTRIB[key]
                    if not cc then
                        local x = {}
                        for k = 1, 3 do
                            x[k] = 0
                            if h ~= 2 and cellSign(k, 1) == want then x[k] = x[k] + 1 end
                            if h ~= 1 and cellSign(k, 2) == want then x[k] = x[k] + 1 end
                        end
                        cc = sharedContrib(x[1], x[2], x[3])
                        LINE_CONTRIB[key] = cc
                    end
                    s.vars[j], s.contrib[j] = ds[j], cc
                end
                P.sums[#P.sums + 1] = s
                P.sum_of[kind][line] = #P.sums
            end
        end
    end
    -- A line's cells are +, - or blank, so two visible clues also give its
    -- blank count, n - plus - minus: a third sum, the count players use too
    -- (measured: it turns most 10x10 full-clue grids from "needs trial"
    -- into tier 1). Then all of a line's sums form one group, which tier 2
    -- solves jointly.
    P.groups, P.grouped = {}, {}
    for _, is_row in ipairs({ true, false }) do
        local pk, mk = is_row and "row_plus" or "col_plus", is_row and "row_minus" or "col_minus"
        for line = 1, n do
            local p, m = clues[pk][line], clues[mk][line]
            if p and m then
                local s = { clue = n - p - m, vars = {}, contrib = {} }
                local axis = is_row and "r" or "c"
                local ds, hs = dom[axis][line], half[axis][line]
                for j = 1, #ds do
                    s.vars[j], s.contrib[j] = ds[j], sharedContrib(hs[j] == 0 and 2 or 1, 0, 0)
                end
                P.sums[#P.sums + 1] = s
                local key = (is_row and "r" or "c") .. line
                P.blank_of[key] = #P.sums
                local group = { P.sum_of[pk][line], P.sum_of[mk][line], #P.sums }
                -- The blank count is implied by the other two (every domino
                -- puts as many cells on the line whatever its option), so
                -- tier 2 only has to meet those two jointly.
                P.groups[#P.groups + 1] = { sums = group, implied = { [3] = true } }
                for _, i in ipairs(group) do P.grouped[i] = true end
            end
        end
    end
    return P
end

-- A random valid polarity for every domino (depth-first, random order of
-- options, neutral first with probability `p_neutral`).
local function assignPolarity(n, dom_id, dominoes, p_neutral)
    local sol = {}
    local function ok(d, k)
        if k == D_NEUTRAL then return true end
        local dm = dominoes[d]
        for which = 1, 2 do
            local r, c = dm[which * 2 - 1], dm[which * 2]
            local s = cellSign(k, which)
            for _, dir in ipairs(DIR4) do
                local r2, c2 = r + dir[1], c + dir[2]
                if r2 >= 1 and r2 <= n and c2 >= 1 and c2 <= n then
                    local e = dom_id[r2][c2]
                    if e ~= d and sol[e] then
                        local em = dominoes[e]
                        local which2 = (em[1] == r2 and em[2] == c2) and 1 or 2
                        if cellSign(sol[e], which2) == s then return false end
                    end
                end
            end
        end
        return true
    end
    local function rec(d)
        if d > #dominoes then return true end
        local opts = { D_PLUS, D_MINUS }
        shuffle(opts)
        if math.random() < p_neutral then
            table.insert(opts, 1, D_NEUTRAL)
        else
            opts[#opts + 1] = D_NEUTRAL
        end
        for _, k in ipairs(opts) do
            if ok(d, k) then
                sol[d] = k
                if rec(d + 1) then return true end
                sol[d] = nil
            end
        end
        return false
    end
    rec(1)   -- neutral always fits, so this cannot fail
    return sol
end

local function fullClues(n, dominoes, sol)
    local clues = {}
    for _, kind in ipairs(CLUE_KINDS) do
        clues[kind] = {}
        for i = 1, n do clues[kind][i] = 0 end
    end
    for d, dm in ipairs(dominoes) do
        for which = 1, 2 do
            local r, c = dm[which * 2 - 1], dm[which * 2]
            local s = cellSign(sol[d], which)
            if s == C_PLUS then
                clues.row_plus[r], clues.col_plus[c] = clues.row_plus[r] + 1, clues.col_plus[c] + 1
            elseif s == C_MINUS then
                clues.row_minus[r], clues.col_minus[c] = clues.row_minus[r] + 1, clues.col_minus[c] + 1
            end
        end
    end
    return clues
end

local function copyClues(clues)
    local out = {}
    for _, kind in ipairs(CLUE_KINDS) do
        out[kind] = {}
        for i, v in ipairs(clues[kind]) do out[kind][i] = v end
    end
    return out
end

-- Hides clues (random order) while the puzzle stays solvable within `cap`.
-- `P` is the problem with every clue shown; a try switches the hidden
-- clues' sums off (P.off) instead of building a new problem, and is solved
-- incrementally (Solver.trial) from the clues that stay shown whatever
-- happens next -- those never tried, or tried and kept -- with the same
-- result as a solve from scratch.
-- `window`, optional, is the level's range of line-reasoning steps
-- (Solver.grade). When the dug puzzle falls outside it, hidden clues are
-- shown again one at a time, last hidden first, and the first that brings
-- the puzzle inside the window stays shown (showing a clue never breaks
-- uniqueness, but it does move the steps: a line's clues may be the very
-- ones a step reasons on). Returns clues, tier, steps (nil without window).
local function digClues(n, P, clues, cap, max_hide, max_tries, tier, on_try, window)
    local order = {}
    for kind = 1, 4 do
        for line = 1, n do order[#order + 1] = { CLUE_KINDS[kind], line } end
    end
    shuffle(order)
    local last = math.min(#order, max_tries)
    -- the sums a clue switches off: its own and its line's blank count
    local sums_of = {}
    for t = 1, last do
        local o = order[t]
        local list = { P.sum_of[o[1]][o[2]] }
        list[2] = P.blank_of[(o[1]:sub(1, 3) == "row" and "r" or "c") .. o[2]]
        sums_of[t] = list
    end
    -- With a bounded window (medium), digging goes on past max_hide, up to
    -- twice that, while the puzzle is not inside the window yet.
    local limit = (window and window[2] < math.huge) and 2 * max_hide or max_hide
    local hidden = {}   -- indices into order
    local fits          -- the longest prefix of `hidden` inside the window
    -- the sums switched off by the hidden clues (but `skip`), plus
    -- order[from..last] and order[extra]
    local function offWith(from, extra, skip)
        local off = {}
        for h, t in ipairs(hidden) do
            if h ~= skip then
                for _, i in ipairs(sums_of[t]) do off[i] = true end
            end
        end
        for t = from or last + 1, last do
            for _, i in ipairs(sums_of[t]) do off[i] = true end
        end
        if extra then
            for _, i in ipairs(sums_of[extra]) do off[i] = true end
        end
        return off
    end
    if window then
        P.off = offWith()
        local _, s = Solver.grade(P)
        if s >= window[1] and s <= window[2] then fits = 0 end
    end
    if max_hide > 0 and last >= 1 then
        P.off = offWith(1)
        local base = Solver.newBase(P, cap)
        for t = 1, last do
            if #hidden >= max_hide and (fits == #hidden or #hidden >= limit) then break end
            if on_try then on_try() end
            P.off = offWith(nil, t)   -- this try: the hidden clues and order[t]
            local st, t2 = Solver.trial(P, base)
            if st == "solved" then
                hidden[#hidden + 1] = t
                tier = t2
                if window and window[2] < math.huge then
                    -- (P.off is exactly the puzzle with these clues hidden)
                    local _, s = Solver.grade(P)
                    if s >= window[1] and s <= window[2] then fits = #hidden end
                end
            elseif t < last then
                -- order[t] stays shown: the base gains it
                P.off = offWith(t + 1)
                Solver.extendBase(P, base)
            end
        end
    end
    local steps
    if window then
        if on_try then on_try() end
        P.off = offWith()
        local _
        _, steps = Solver.grade(P)
        if (steps < window[1] or steps > window[2]) and fits then
            for h = #hidden, fits + 1, -1 do hidden[h] = nil end
            P.off = offWith()
            _, steps, tier = Solver.grade(P)
        end
        if steps < window[1] or steps > window[2] then
            for h = #hidden, 1, -1 do
                if on_try then on_try() end
                P.off = offWith(nil, nil, h)
                local st, s, t2 = Solver.grade(P)
                if st == "solved" and s >= window[1] and s <= window[2] then
                    table.remove(hidden, h)
                    steps, tier = s, t2
                    break
                end
            end
        end
    end
    P.off = nil
    local out = copyClues(clues)
    for _, t in ipairs(hidden) do
        local o = order[t]
        out[o[1]][o[2]] = false
    end
    return out, tier, steps
end

-- How far a dug puzzle is from its level: 0 when it needs the level's tier
-- and a number of line-reasoning steps (Solver.grade) inside the level's
-- window; otherwise the gap, a wrong tier counting most.
local function missBy(lv, tier, steps)
    local miss = (lv.tier - tier) * 100
    if steps < lv.steps[1] then miss = miss + lv.steps[1] - steps end
    if steps > lv.steps[2] then miss = miss + steps - lv.steps[2] end
    return miss
end

-- One complete puzzle. The solver must deduce every domino (which proves the
-- solution unique); the first candidate that needs the level's tier and
-- number of line-reasoning steps wins, otherwise the closest seen is kept.
-- `on_progress(fraction)`, optional, is called before every solve. The work
-- has no fixed size (a level may take one candidate or many), so the
-- fraction approaches 1 as solves pile up, against the typical count of one
-- candidate dug to the end.
local function generatePuzzle(n, difficulty, on_progress)
    local lv = LEVELS[difficulty] or LEVELS[DEFAULT_DIFF]
    local max_tries = math.floor(lv.max_tries * n)
    local solves, typical = 0, 2 + max_tries
    local function tick()
        solves = solves + 1
        if on_progress then on_progress(solves / (solves + typical)) end
    end
    local best, digs = nil, 0
    for _ = 1, MAX_ATTEMPTS do
        local dom_id, dominoes = makeTiling(n)
        local pairs_ = buildPairs(n, dom_id, dominoes)
        local sol    = assignPolarity(n, dom_id, dominoes, lv.neutral)
        local clues  = fullClues(n, dominoes, sol)
        local P      = buildProblem(n, dominoes, clues)
        P.pairs      = pairs_
        tick()
        local st, tier = Solver.solve(P, lv.tier)
        if st == "solved" and tier == 2 and lv.pre then
            local _, s0 = Solver.grade(P)
            if s0 < lv.pre[1] or s0 > lv.pre[2] then st = "pre" end
        end
        if st == "solved" and (tier == lv.tier or not lv.full_tier) then
            local steps
            clues, tier, steps = digClues(n, P, clues, lv.tier, math.floor(lv.max_hide * n),
                                          max_tries, tier, tick, lv.steps)
            local miss = missBy(lv, tier, steps)
            if not best or miss < best.miss then
                best = { dom_id = dom_id, dominoes = dominoes, solution = sol, clues = clues,
                         tier = tier, miss = miss }
            end
            digs = digs + 1
            if miss == 0 then break end
            -- past the cap, the closest puzzle is kept, but never one
            -- easier than the level's tier
            if digs >= (lv.max_digs[n] or MAX_ATTEMPTS) and best.tier == lv.tier then break end
        end
    end
    return best
end

-- ---------------------------------------------------------------------------
-- MagnetsBoard
-- ---------------------------------------------------------------------------

local MagnetsBoard = {}
MagnetsBoard.__index = MagnetsBoard

function MagnetsBoard:new(opts)
    opts = opts or {}
    local obj = setmetatable({
        n          = opts.n or DEFAULT_N,
        difficulty = opts.difficulty or DEFAULT_DIFF,
        undo       = UndoStack:new{ max_size = 500 },
        timer      = Timer:new(),
        hints_used = 0,
    }, self)
    if opts.generate ~= false then obj:generate() end
    return obj
end

-- `on_progress(fraction)`: optional, for the screen's progress bar.
function MagnetsBoard:generate(n, difficulty, on_progress)
    self.n          = n or self.n
    self.difficulty = difficulty or self.difficulty
    -- No puzzle can come back nil: every attempt with all clues shown is at
    -- worst "stuck", and 160 stuck attempts in a row have not been observed;
    -- loop anyway rather than hand the screen a nil.
    local p
    repeat p = generatePuzzle(self.n, self.difficulty, on_progress) until p
    self.dom_id   = p.dom_id
    self.dominoes = p.dominoes
    self.solution = p.solution
    self.clues    = p.clues
    self.tier     = p.tier
    self:_reset()
end

function MagnetsBoard:_reset()
    self.state = {}
    for d = 1, #self.dominoes do self.state[d] = D_EMPTY end
    self.wrong      = {}
    self.won        = false
    self.revealed   = false
    self.hints_used = 0
    self.undo:clear()
    self.timer:reset()
    self.timer:start()
end

function MagnetsBoard:getProblem()
    local P = buildProblem(self.n, self.dominoes, self.clues)
    P.pairs = buildPairs(self.n, self.dom_id, self.dominoes)
    return P
end

-- Which half of its domino a cell is: 1 (top/left) or 2.
function MagnetsBoard:whichHalf(r, c)
    local dm = self.dominoes[self.dom_id[r][c]]
    return (dm[1] == r and dm[2] == c) and 1 or 2
end

function MagnetsBoard:partner(r, c)
    local dm = self.dominoes[self.dom_id[r][c]]
    if dm[1] == r and dm[2] == c then return dm[3], dm[4] end
    return dm[1], dm[2]
end

function MagnetsBoard:cellValue(r, c)
    return cellSign(self.state[self.dom_id[r][c]], self:whichHalf(r, c))
end

function MagnetsBoard:solutionValue(r, c)
    return cellSign(self.solution[self.dom_id[r][c]], self:whichHalf(r, c))
end

-- ---------------------------------------------------------------------------
-- Moves
-- ---------------------------------------------------------------------------

function MagnetsBoard:setDomino(d, k)
    if self.won then return false end
    local old = self.state[d]
    if old == k then return false end
    self.undo:push{ d = d, old = old }
    self.state[d] = k
    self.wrong[d] = nil
    self:_checkWin()
    return true
end

-- Domino state that puts `v` (a cell value) on cell (r, c).
function MagnetsBoard:_stateFor(r, c, v)
    if v == C_EMPTY then return D_EMPTY end
    if v == C_NEUTRAL then return D_NEUTRAL end
    local first = self:whichHalf(r, c) == 1
    if v == C_PLUS then return first and D_PLUS or D_MINUS end
    return first and D_MINUS or D_PLUS
end

-- Tap cycles the tapped cell: empty -> + -> - -> neutral -> empty (its
-- partner always takes the opposite pole).
local NEXT_CELL = { [C_EMPTY] = C_PLUS, [C_PLUS] = C_MINUS, [C_MINUS] = C_NEUTRAL, [C_NEUTRAL] = C_EMPTY }

function MagnetsBoard:cycle(r, c)
    local v = NEXT_CELL[self:cellValue(r, c)]
    return self:setDomino(self.dom_id[r][c], self:_stateFor(r, c, v))
end

-- Long-press marks the domino neutral, or clears it if it already is.
function MagnetsBoard:toggleNeutral(r, c)
    local d = self.dom_id[r][c]
    return self:setDomino(d, self.state[d] == D_NEUTRAL and D_EMPTY or D_NEUTRAL)
end

function MagnetsBoard:setCell(r, c, v)
    return self:setDomino(self.dom_id[r][c], self:_stateFor(r, c, v))
end

function MagnetsBoard:undoMove()
    if self.won then return false end
    local e = self.undo:pop()
    if not e then return false end
    self.state[e.d] = e.old
    self.wrong[e.d] = nil
    return true
end

function MagnetsBoard:canUndo()
    return not self.won and self.undo:canUndo()
end

-- ---------------------------------------------------------------------------
-- State queries
-- ---------------------------------------------------------------------------

-- How many cells of a line show `sign` (C_PLUS / C_MINUS).
function MagnetsBoard:lineCount(is_row, line, sign)
    local k = 0
    for i = 1, self.n do
        local r, c = line, i
        if not is_row then r, c = i, line end
        if self:cellValue(r, c) == sign then k = k + 1 end
    end
    return k
end

-- Cells with a like pole on an orthogonal neighbour: conflicts[r][c] = true.
function MagnetsBoard:getConflicts()
    local n = self.n
    local out = emptyGrid(n, n, false)
    for r = 1, n do
        for c = 1, n do
            local v = self:cellValue(r, c)
            if v == C_PLUS or v == C_MINUS then
                for _, dir in ipairs(DIR4) do
                    local r2, c2 = r + dir[1], c + dir[2]
                    if r2 >= 1 and r2 <= n and c2 >= 1 and c2 <= n
                        and self:cellValue(r2, c2) == v then
                        out[r][c] = true
                    end
                end
            end
        end
    end
    return out
end

-- Dominoes decided by the player (neutral included), for the status line.
function MagnetsBoard:decidedCount()
    local k = 0
    for d = 1, #self.dominoes do
        if self.state[d] ~= D_EMPTY then k = k + 1 end
    end
    return k
end

function MagnetsBoard:hiddenCount()
    local k = 0
    for _, kind in ipairs(CLUE_KINDS) do
        for i = 1, self.n do
            if not self.clues[kind][i] then k = k + 1 end
        end
    end
    return k
end

-- Won once every magnet is in place: a domino left undecided counts as
-- neutral, so marking the blanks is optional (the solution is unique, so
-- matching it is the same as satisfying every clue).
function MagnetsBoard:_checkWin()
    for d = 1, #self.dominoes do
        local u, s = self.state[d], self.solution[d]
        if u == D_EMPTY then u = D_NEUTRAL end
        if u ~= s then
            self.won = false
            return false
        end
    end
    self.won = true
    self.timer:stop()
    return true
end

-- Flags every decided domino that differs from the solution.
function MagnetsBoard:check()
    local count = 0
    self.wrong = {}
    for d = 1, #self.dominoes do
        local u = self.state[d]
        if u ~= D_EMPTY and u ~= self.solution[d] then
            self.wrong[d] = true
            count = count + 1
        end
    end
    return count
end

function MagnetsBoard:isWrong(r, c)
    return self.wrong[self.dom_id[r][c]] == true
end

function MagnetsBoard:reveal()
    for d = 1, #self.dominoes do self.state[d] = self.solution[d] end
    self.wrong    = {}
    self.revealed = true
    self.won      = true
    self.timer:stop()
end

-- ---------------------------------------------------------------------------
-- Hint: per cell. A neutral domino is real information (it is a deduction,
-- not a default), so it is offered like a pole; a wrong domino is cleared.
-- ---------------------------------------------------------------------------

Hint.install(MagnetsBoard, {
    getUser     = function(b, r, c) return b:cellValue(r, c) end,
    getSolution = function(b, r, c) return b:solutionValue(r, c) end,
    isEmpty     = function(v) return v == C_EMPTY end,
    setCell     = function(b, r, c, v) return b:setCell(r, c, v) end,
    blank       = C_EMPTY,
})

-- ---------------------------------------------------------------------------
-- Persistence
-- ---------------------------------------------------------------------------

function MagnetsBoard:serialize()
    local n = self.n
    -- Timer:serialize() stops the clock; a save mid-game must not.
    local running = self.timer:isRunning()
    local timer   = self.timer:serialize()
    if running then self.timer:start() end
    local doms = {}
    for d, dm in ipairs(self.dominoes) do
        doms[d] = { dm[1], dm[2], dm[3], dm[4] }
    end
    local clues = {}
    for _, kind in ipairs(CLUE_KINDS) do
        clues[kind] = {}
        for i = 1, n do clues[kind][i] = self.clues[kind][i] or -1 end
    end
    local sol, state = {}, {}
    for d = 1, #self.dominoes do sol[d], state[d] = self.solution[d], self.state[d] end
    return {
        n          = n,
        difficulty = self.difficulty,
        dominoes   = doms,
        solution   = sol,
        state      = state,
        clues      = clues,
        tier       = self.tier,
        won        = self.won,
        revealed   = self.revealed,
        hints_used = self.hints_used,
        timer      = timer,
    }
end

function MagnetsBoard:load(data)
    if type(data) ~= "table" or type(data.dominoes) ~= "table"
        or type(data.solution) ~= "table" or type(data.clues) ~= "table" then
        return false
    end
    local n = tonumber(data.n)
    if not n or #data.dominoes * 2 ~= n * n or #data.solution ~= #data.dominoes then
        return false
    end
    self.n          = n
    self.difficulty = data.difficulty or DEFAULT_DIFF
    self.dominoes   = {}
    self.dom_id     = emptyGrid(n, n, 0)
    for d, dm in ipairs(data.dominoes) do
        self.dominoes[d] = { dm[1], dm[2], dm[3], dm[4] }
        self.dom_id[dm[1]][dm[2]], self.dom_id[dm[3]][dm[4]] = d, d
    end
    self.solution = {}
    for d = 1, #self.dominoes do self.solution[d] = data.solution[d] end
    self.clues = {}
    for _, kind in ipairs(CLUE_KINDS) do
        self.clues[kind] = {}
        local src = data.clues[kind] or {}
        for i = 1, n do
            local v = src[i]
            self.clues[kind][i] = (type(v) == "number" and v >= 0) and v or false
        end
    end
    self.tier = data.tier
    self:_reset()
    if type(data.state) == "table" then
        for d = 1, #self.dominoes do self.state[d] = data.state[d] or D_EMPTY end
    end
    self.won        = data.won and true or false
    self.revealed   = data.revealed and true or false
    self.hints_used = data.hints_used or 0
    self.timer:load(data.timer)
    if self.won then self.timer:stop() else self.timer:start() end
    return true
end

MagnetsBoard.D_EMPTY   = D_EMPTY
MagnetsBoard.D_NEUTRAL = D_NEUTRAL
MagnetsBoard.D_PLUS    = D_PLUS
MagnetsBoard.D_MINUS   = D_MINUS
MagnetsBoard.C_EMPTY   = C_EMPTY
MagnetsBoard.C_PLUS    = C_PLUS
MagnetsBoard.C_MINUS   = C_MINUS
MagnetsBoard.C_NEUTRAL = C_NEUTRAL
MagnetsBoard.SIZES        = SIZES
MagnetsBoard.DEFAULT_N    = DEFAULT_N
MagnetsBoard.DEFAULT_DIFF = DEFAULT_DIFF
MagnetsBoard.LEVELS       = LEVELS
MagnetsBoard.CLUE_KINDS   = CLUE_KINDS
MagnetsBoard._cellSign    = cellSign
-- Generator internals, exposed for the specs and measurement scripts.
MagnetsBoard._makeTiling     = makeTiling
MagnetsBoard._buildPairs     = buildPairs
MagnetsBoard._assignPolarity = assignPolarity
MagnetsBoard._fullClues      = fullClues
MagnetsBoard._buildProblem   = buildProblem

return MagnetsBoard
