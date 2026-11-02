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
-- reasoning) and how many of the 4n clues may be hidden. Tier 3 (one-step
-- trial) is never asked for: on paper it plays as guessing, so hard is harder
-- through more hidden clues instead.
-- Easy shows every clue. `max_tries` caps how many clue removals are
-- attempted, as a multiple of n: each attempt is a full solve, and at tier 3
-- an unbounded dig cost seconds on 10x10. `full_tier` only digs candidates
-- that already need the level's tier with every clue shown: digging a
-- tier-2 candidate at tier 3 mostly ended at tier 2 again, and that wasted
-- dig was the worst case (1 s on 10x10 here).
local LEVELS = {
    easy   = { tier = 1, neutral = 0.20, max_hide = function()  return 0 end, max_tries = 0 },
    medium = { tier = 2, neutral = 0.20, max_hide = function(n) return math.floor(n / 2) end, max_tries = 4 },
    hard   = { tier = 2, neutral = 0.20, max_hide = function(n) return 3 * n end, max_tries = 4 },
}

local MAX_ATTEMPTS = 40

-- ---------------------------------------------------------------------------
-- Generator
-- ---------------------------------------------------------------------------

-- Random domino tiling of an n x n grid (n even): start from rows of
-- horizontal dominoes and rotate random 2x2 blocks covered by two parallel
-- dominoes. Returns dom_id[r][c] and dominoes[d] = { r1, c1, r2, c2 } with
-- the first cell top or left.
local function makeTiling(n)
    local id = emptyGrid(n, n, 0)
    local mate = {}   -- mate[r][c] = { r, c } of the other half
    for r = 1, n do
        mate[r] = {}
        for c = 1, n, 2 do
            mate[r][c], mate[r][c + 1] = { r, c + 1 }, { r, c }
        end
    end
    local function pairUp(r1, c1, r2, c2)
        mate[r1][c1], mate[r2][c2] = { r2, c2 }, { r1, c1 }
    end
    for _ = 1, n * n * 12 do
        local r, c = math.random(n - 1), math.random(n - 1)
        local m = mate[r][c]
        if m[1] == r and m[2] == c + 1 then
            local m2 = mate[r + 1][c]
            if m2[1] == r + 1 and m2[2] == c + 1 then   -- two horizontals -> verticals
                pairUp(r, c, r + 1, c); pairUp(r, c + 1, r + 1, c + 1)
            end
        elseif m[1] == r + 1 and m[2] == c then
            local m2 = mate[r][c + 1]
            if m2[1] == r + 1 and m2[2] == c + 1 then   -- two verticals -> horizontals
                pairUp(r, c, r, c + 1); pairUp(r + 1, c, r + 1, c + 1)
            end
        end
    end
    local dominoes = {}
    for r = 1, n do
        for c = 1, n do
            if id[r][c] == 0 then
                local m = mate[r][c]
                dominoes[#dominoes + 1] = { r, c, m[1], m[2] }
                id[r][c], id[m[1]][m[2]] = #dominoes, #dominoes
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
    return list
end

-- clues = { row_plus = {}, row_minus = {}, col_plus = {}, col_minus = {} };
-- false = hidden.
local CLUE_KINDS = { "row_plus", "row_minus", "col_plus", "col_minus" }

local function buildProblem(n, dominoes, pairs_, clues)
    local P = { nvars = #dominoes, ksize = {}, sums = {}, pairs = pairs_ }
    for d = 1, #dominoes do P.ksize[d] = 3 end
    for _, kind in ipairs(CLUE_KINDS) do
        local is_row  = kind:sub(1, 3) == "row"
        local want    = kind:sub(-4) == "plus" and C_PLUS or C_MINUS
        for line = 1, n do
            local clue = clues[kind][line]
            if clue then
                local s = { clue = clue, vars = {}, contrib = {},
                            line_key = (is_row and "r" or "c") .. line }
                for d, dm in ipairs(dominoes) do
                    local in1 = (is_row and dm[1] or dm[2]) == line
                    local in2 = (is_row and dm[3] or dm[4]) == line
                    if in1 or in2 then
                        local cc = {}
                        for k = 1, 3 do
                            local x = 0
                            if in1 and cellSign(k, 1) == want then x = x + 1 end
                            if in2 and cellSign(k, 2) == want then x = x + 1 end
                            cc[k] = x
                        end
                        s.vars[#s.vars + 1], s.contrib[#s.contrib + 1] = d, cc
                    end
                end
                P.sums[#P.sums + 1] = s
            end
        end
    end
    -- A line's cells are +, - or blank, so two visible clues also give its
    -- blank count, n - plus - minus: a third sum, the count players use too
    -- (measured: it turns most 10x10 full-clue grids from "needs trial"
    -- into tier 1). Then all of a line's sums form one group, which tier 2
    -- solves jointly.
    P.groups, P.grouped = {}, {}
    local line_sums = {}
    for i, s in ipairs(P.sums) do
        local key = s.line_key
        line_sums[key] = line_sums[key] or {}
        table.insert(line_sums[key], i)
    end
    for _, is_row in ipairs({ true, false }) do
        local pk, mk = is_row and "row_plus" or "col_plus", is_row and "row_minus" or "col_minus"
        for line = 1, n do
            local p, m = clues[pk][line], clues[mk][line]
            local key = (is_row and "r" or "c") .. line
            if p and m then
                local s = { clue = n - p - m, vars = {}, contrib = {} }
                for d, dm in ipairs(dominoes) do
                    local k = 0
                    if (is_row and dm[1] or dm[2]) == line then k = k + 1 end
                    if (is_row and dm[3] or dm[4]) == line then k = k + 1 end
                    if k > 0 then
                        s.vars[#s.vars + 1], s.contrib[#s.contrib + 1] = d, { k, 0, 0 }
                    end
                end
                P.sums[#P.sums + 1] = s
                line_sums[key] = line_sums[key] or {}
                table.insert(line_sums[key], #P.sums)
            end
            local group = line_sums[key]
            if group and #group > 1 then
                P.groups[#P.groups + 1] = { sums = group }
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
local function digClues(n, dominoes, pairs_, clues, cap, max_hide, max_tries, tier)
    local order = {}
    for kind = 1, 4 do
        for line = 1, n do order[#order + 1] = { CLUE_KINDS[kind], line } end
    end
    shuffle(order)
    local hidden = 0
    for t, o in ipairs(order) do
        if hidden >= max_hide or t > max_tries then break end
        local trial = copyClues(clues)
        trial[o[1]][o[2]] = false
        local st, t2 = Solver.solve(buildProblem(n, dominoes, pairs_, trial), cap)
        if st == "solved" then
            clues, tier, hidden = trial, t2, hidden + 1
        end
    end
    return clues, tier
end

-- One complete puzzle. The solver must deduce every domino (which proves the
-- solution unique); the first candidate whose hardest step equals the level's
-- tier wins, otherwise the hardest seen is kept.
local function generatePuzzle(n, difficulty)
    local lv = LEVELS[difficulty] or LEVELS[DEFAULT_DIFF]
    local best
    for _ = 1, MAX_ATTEMPTS do
        local dom_id, dominoes = makeTiling(n)
        local pairs_ = buildPairs(n, dom_id, dominoes)
        local sol    = assignPolarity(n, dom_id, dominoes, lv.neutral)
        local clues  = fullClues(n, dominoes, sol)
        local st, tier = Solver.solve(buildProblem(n, dominoes, pairs_, clues), lv.tier)
        if st == "solved" and (tier == lv.tier or not lv.full_tier) then
            clues, tier = digClues(n, dominoes, pairs_, clues, lv.tier, lv.max_hide(n),
                math.floor(lv.max_tries * n), tier)
            if not best or tier > best.tier then
                best = { dom_id = dom_id, dominoes = dominoes, solution = sol, clues = clues, tier = tier }
            end
            if tier == lv.tier then break end
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

function MagnetsBoard:generate(n, difficulty)
    self.n          = n or self.n
    self.difficulty = difficulty or self.difficulty
    -- No puzzle can come back nil: every attempt with all clues shown is at
    -- worst "stuck", and 40 stuck attempts in a row have not been observed;
    -- loop anyway rather than hand the screen a nil.
    local p
    repeat p = generatePuzzle(self.n, self.difficulty) until p
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
    return buildProblem(self.n, self.dominoes, buildPairs(self.n, self.dom_id, self.dominoes), self.clues)
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
