-- Difficulty guarantees for Magnets (see docs/dev/TESTING.md, "Difficulty
-- specs"): every size x level has one solution (independent count) that the
-- game's own solver finds without trial (tier 3), Easy shows every clue and
-- needs tier 1 only, the levels sit in their line-reasoning step windows
-- and rise on average, a seed gives the same puzzle (progress bar or not),
-- generation stays within a time bound and never reads the clock.
local DIR = debug.getinfo(1, "S").source:sub(2):match("(.*[/\\])") or "./"

package.preload["gettext"] = function()
    return setmetatable({}, { __call = function(_, s) return s end })
end
package.path = DIR .. "common/?.lua;" .. DIR .. "?.lua;" .. package.path

-- Runs fn with os.clock/os.time/os.date counted; returns how many times
-- they were read. The play timer (game-common timer.lua, started when a new
-- round begins) is not part of the generator and is left out.
local function clockReads(fn)
    local oc, ot, od = os.clock, os.time, os.date
    local reads = 0
    local function count()
        local src = debug.getinfo(3, "S").source
        if not src:find("timer%.lua$") then reads = reads + 1 end
    end
    os.clock = function(...) count(); return oc(...) end
    os.time  = function(...) count(); return ot(...) end
    os.date  = function(...) count(); return od(...) end
    local ok, err = pcall(fn)
    os.clock, os.time, os.date = oc, ot, od
    if not ok then error(err, 0) end
    return reads
end

describe("Magnets difficulty", function()
    local Board, Solver

    setup(function()
        Board  = require("board")
        Solver = require("solver")
    end)

    local function newBoard(n, diff, seed)
        math.randomseed(seed or 42)
        return Board:new({ n = n or 6, difficulty = diff or "easy" })
    end

    it("the level table is ordered", function()
        local e, m, h = Board.LEVELS.easy, Board.LEVELS.medium, Board.LEVELS.hard
        assert.is_true(e.tier <= m.tier and m.tier <= h.tier)
        assert.is_true(e.steps[2] < m.steps[1] and m.steps[2] < h.steps[1])
        assert.is_true(e.max_hide <= m.max_hide and m.max_hide <= h.max_hide)
        -- trial (tier 3) is never allowed
        assert.is_true(h.tier <= 2)
    end)

    -- moved from test_board_spec.lua
    it("easy shows every clue and needs only tier-1 logic", function()
        for seed = 1, 10 do
            local b = newBoard(8, "easy", seed)
            assert.are.equal(0, b:hiddenCount())
            local st, tier = Solver.solve(b:getProblem(), 1)
            assert.are.equal("solved", st)
            assert.are.equal(1, tier)
        end
    end)

    -- moved from test_board_spec.lua
    -- Trial reasoning (tier 3) plays as guessing on paper: no level may
    -- need it. The levels differ by how many line-reasoning steps
    -- (Solver.grade) they need: none on easy, one on medium, at least
    -- two on hard. A level keeps the closest puzzle when its search cap
    -- runs out, so the windows are checked as shares (1.3.0, over 40
    -- seeds per size: medium 95-100 %, hard 87-97 %), and the averages
    -- of steps and hidden clues must rise from level to level.
    it("levels need 0 / 1 / 2+ line-reasoning steps, never trial", function()
        local seeds = 8
        for _, n in ipairs(Board.SIZES) do
            local prev_steps, prev_hidden = -1, -1
            for _, diff in ipairs({ "easy", "medium", "hard" }) do
                local lv = Board.LEVELS[diff]
                local inside, steps_sum, hidden_sum = 0, 0, 0
                for seed = 1, seeds do
                    local b = newBoard(n, diff, seed * 13 + n)
                    local P = b:getProblem()
                    assert.are.equal("solved", (Solver.solve(P, 2)))
                    local st, steps, tier = Solver.grade(P)
                    assert.are.equal("solved", st)
                    assert.are.equal(lv.tier, tier)
                    if steps >= lv.steps[1] and steps <= lv.steps[2] then inside = inside + 1 end
                    steps_sum, hidden_sum = steps_sum + steps, hidden_sum + b:hiddenCount()
                end
                if diff == "easy" then
                    assert.are.equal(seeds, inside)
                    assert.are.equal(0, hidden_sum)
                else
                    assert.is_true(inside >= seeds - 2, n .. " " .. diff .. ": " .. inside)
                end
                assert.is_true(steps_sum / seeds > prev_steps, n .. " " .. diff)
                assert.is_true(hidden_sum / seeds > prev_hidden, n .. " " .. diff)
                prev_steps, prev_hidden = steps_sum / seeds, hidden_sum / seeds
            end
        end
    end)

    -- moved from test_board_spec.lua
    -- 1.1.0: the progress bar's callback must not change the puzzle a
    -- seed gives (the timer is left out: it reads the clock), and a
    -- generation stays far below the old worst cases (238 ms on 10x10
    -- hard on a desktop; the bound is generous for slow test runs).
    it("reports progress without changing the puzzle, within a time bound", function()
        local function strip(b)
            local d = b:serialize()
            d.timer = nil
            return d
        end
        for _, n in ipairs(Board.SIZES) do
            for _, diff in ipairs({ "medium", "hard" }) do
                for seed = 1, 2 do
                    local plain = newBoard(n, diff, seed * 7 + n)
                    local fractions = {}
                    math.randomseed(seed * 7 + n)
                    local b = Board:new({ n = n, difficulty = diff, generate = false })
                    local t0 = os.clock()
                    b:generate(n, diff, function(f) fractions[#fractions + 1] = f end)
                    assert.is_true(os.clock() - t0 < 10)
                    assert.are.same(strip(plain), strip(b))
                    assert.is_true(#fractions > 0)
                    for i, f in ipairs(fractions) do
                        assert.is_true(f >= 0 and f <= 1)
                        if i > 1 then assert.is_true(f >= fractions[i - 1]) end
                    end
                end
            end
        end
    end)

    -- moved from test_board_spec.lua
    -- What a seed gives (the Daily Challenge relies on it). 1.3.0
    -- changed it once, when levels started to be graded by line-reasoning
    -- steps (math.random differs between LuaJIT and PUC Lua, hence two
    -- sets).
    it("gives the same puzzles per seed as 1.3.0", function()
        local expected = jit and {
            "2.22.2 3.3322 232.3. ..12.3",
            "3434.22. 43432.32 3443133. 34422243",
            "3..4.45.45 ..5..4.535 55445434.5 .455...4.5",
        } or {
            ".1.... .3...1 3..2.1 332211",
            "3332.424 4223423. 44212.43 44213333",
            "4535343..4 ..534.344. 55.13..4.4 555.14.44.",
        }
        local function key(b)
            local out = {}
            for _, k in ipairs({ "row_plus", "row_minus", "col_plus", "col_minus" }) do
                local t = {}
                for i = 1, b.n do
                    t[i] = b.clues[k][i] == false and "." or tostring(b.clues[k][i])
                end
                out[#out + 1] = table.concat(t)
            end
            return table.concat(out, " ")
        end
        for i, c in ipairs({ { 6, "hard", 3 }, { 8, "medium", 5 }, { 10, "hard", 2 } }) do
            assert.are.equal(expected[i], key(newBoard(c[1], c[2], c[3])))
        end
    end)

    -- moved from test_board_spec.lua
    it("every puzzle has exactly one solution (independent count) and the solver finds it", function()
        local cases = { { 6, 10 }, { 8, 6 }, { 10, 3 } }
        for _, case in ipairs(cases) do
            local n, seeds = case[1], case[2]
            for _, diff in ipairs({ "easy", "medium", "hard" }) do
                for seed = 1, seeds do
                    local b = newBoard(n, diff, seed * 17 + n)
                    local P = b:getProblem()
                    local count, exhausted = Solver.count(P, 2, 500000)
                    assert.is_false(exhausted)
                    assert.are.equal(1, count)
                    local st, tier, S = Solver.solve(P, 3)
                    assert.are.equal("solved", st)
                    assert.is_true(tier <= Board.LEVELS[diff].tier)
                    local opt = Solver.assignment(S)
                    for d = 1, #b.dominoes do assert.are.equal(b.solution[d], opt[d]) end
                end
            end
        end
    end)

    it("generation never reads the clock", function()
        for _, n in ipairs(Board.SIZES) do
            for _, diff in ipairs({ "easy", "medium", "hard" }) do
                local reads = clockReads(function()
                    math.randomseed(5 + n)
                    local b = Board:new({ n = n, difficulty = diff, generate = false })
                    b:generate(n, diff)
                end)
                assert.are.equal(0, reads, ("%dx%d %s read the clock"):format(n, n, diff))
            end
        end
    end)
end)
