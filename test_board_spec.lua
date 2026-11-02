local DIR = debug.getinfo(1, "S").source:sub(2):match("(.*[/\\])") or "./"

package.preload["gettext"] = function()
    return setmetatable({}, { __call = function(_, s) return s end })
end
package.path = DIR .. "common/?.lua;" .. DIR .. "?.lua;" .. package.path

describe("MagnetsBoard", function()
    local Board, Solver

    setup(function()
        Board  = require("board")
        Solver = require("solver")
    end)

    local function newBoard(n, diff, seed)
        math.randomseed(seed or 42)
        return Board:new({ n = n or 6, difficulty = diff or "easy" })
    end

    local DIR4 = { { -1, 0 }, { 1, 0 }, { 0, -1 }, { 0, 1 } }

    -- Places every magnet of the solution through taps, leaving blanks open.
    local function playMagnets(b)
        for d, dm in ipairs(b.dominoes) do
            local want = b.solution[d]
            if want ~= Board.D_NEUTRAL then
                local target = Board._cellSign(want, 1)
                for _ = 1, 4 do
                    if b:cellValue(dm[1], dm[2]) == target then break end
                    b:cycle(dm[1], dm[2])
                end
            end
        end
    end

    describe("generator", function()
        it("tiles the grid with dominoes, first half top or left", function()
            local b = newBoard(8, "medium")
            local seen = {}
            assert.are.equal(32, #b.dominoes)
            for d, dm in ipairs(b.dominoes) do
                local dr, dc = dm[3] - dm[1], dm[4] - dm[2]
                assert.is_true((dr == 0 and dc == 1) or (dr == 1 and dc == 0))
                for which = 1, 2 do
                    local key = dm[which * 2 - 1] * 100 + dm[which * 2]
                    assert.is_nil(seen[key])
                    seen[key] = true
                    assert.are.equal(d, b.dom_id[dm[which * 2 - 1]][dm[which * 2]])
                end
            end
        end)

        it("produces both orientations of dominoes", function()
            local b = newBoard(8, "medium")
            local h, v = 0, 0
            for _, dm in ipairs(b.dominoes) do
                if dm[1] == dm[3] then h = h + 1 else v = v + 1 end
            end
            assert.is_true(h > 0 and v > 0)
        end)

        it("solution never puts like poles side by side and matches the shown clues", function()
            for _, diff in ipairs({ "easy", "medium", "hard" }) do
                local b = newBoard(8, diff, 9)
                local n = b.n
                for r = 1, n do
                    for c = 1, n do
                        local v = b:solutionValue(r, c)
                        if v == Board.C_PLUS or v == Board.C_MINUS then
                            for _, d in ipairs(DIR4) do
                                local r2, c2 = r + d[1], c + d[2]
                                if r2 >= 1 and r2 <= n and c2 >= 1 and c2 <= n then
                                    assert.are_not.equal(v, b:solutionValue(r2, c2))
                                end
                            end
                        end
                    end
                end
                for i = 1, n do
                    local counts = { row_plus = 0, row_minus = 0, col_plus = 0, col_minus = 0 }
                    for j = 1, n do
                        local rv, cv = b:solutionValue(i, j), b:solutionValue(j, i)
                        if rv == Board.C_PLUS then counts.row_plus = counts.row_plus + 1 end
                        if rv == Board.C_MINUS then counts.row_minus = counts.row_minus + 1 end
                        if cv == Board.C_PLUS then counts.col_plus = counts.col_plus + 1 end
                        if cv == Board.C_MINUS then counts.col_minus = counts.col_minus + 1 end
                    end
                    for kind, v in pairs(counts) do
                        if b.clues[kind][i] then assert.are.equal(v, b.clues[kind][i]) end
                    end
                end
            end
        end)

        it("easy shows every clue and needs only tier-1 logic", function()
            for seed = 1, 10 do
                local b = newBoard(8, "easy", seed)
                assert.are.equal(0, b:hiddenCount())
                local st, tier = Solver.solve(b:getProblem(), 1)
                assert.are.equal("solved", st)
                assert.are.equal(1, tier)
            end
        end)

        -- Trial reasoning (tier 3) plays as guessing on paper: no level may
        -- need it. Hard is harder through more hidden clues instead.
        it("medium and hard hide clues, need line reasoning but never trial", function()
            for seed = 1, 6 do
                local m = newBoard(8, "medium", seed)
                assert.are.equal(2, m.tier)
                assert.is_true(m:hiddenCount() > 0)
                assert.are.equal("stuck", (Solver.solve(m:getProblem(), 1)))
                local h = newBoard(8, "hard", seed)
                assert.are.equal("solved", (Solver.solve(h:getProblem(), 2)))
                assert.is_true(h:hiddenCount() > m:hiddenCount())
            end
        end)

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
    end)

    describe("moves", function()
        it("tapping a half cycles + / - / blank / open, partner opposite", function()
            local b = newBoard(6, "easy")
            local dm = b.dominoes[1]
            local r, c, pr, pc = dm[1], dm[2], dm[3], dm[4]
            b:cycle(r, c)
            assert.are.equal(Board.C_PLUS, b:cellValue(r, c))
            assert.are.equal(Board.C_MINUS, b:cellValue(pr, pc))
            b:cycle(r, c)
            assert.are.equal(Board.C_MINUS, b:cellValue(r, c))
            assert.are.equal(Board.C_PLUS, b:cellValue(pr, pc))
            b:cycle(r, c)
            assert.are.equal(Board.C_NEUTRAL, b:cellValue(r, c))
            assert.are.equal(Board.C_NEUTRAL, b:cellValue(pr, pc))
            b:cycle(r, c)
            assert.are.equal(Board.C_EMPTY, b:cellValue(r, c))
        end)

        it("the tapped half gets the + first, whichever half it is", function()
            local b = newBoard(6, "easy")
            local dm = b.dominoes[2]
            b:cycle(dm[3], dm[4])
            assert.are.equal(Board.C_PLUS, b:cellValue(dm[3], dm[4]))
            assert.are.equal(Board.C_MINUS, b:cellValue(dm[1], dm[2]))
        end)

        it("long-press toggles blank", function()
            local b = newBoard(6, "easy")
            local dm = b.dominoes[3]
            b:toggleNeutral(dm[1], dm[2])
            assert.are.equal(Board.D_NEUTRAL, b.state[3])
            b:toggleNeutral(dm[3], dm[4])
            assert.are.equal(Board.D_EMPTY, b.state[3])
        end)

        it("undo restores the previous state of the domino", function()
            local b = newBoard(6, "easy")
            local dm = b.dominoes[1]
            b:cycle(dm[1], dm[2])
            b:cycle(dm[1], dm[2])
            assert.is_true(b:undoMove())
            assert.are.equal(Board.D_PLUS, b.state[1])
            assert.is_true(b:undoMove())
            assert.are.equal(Board.D_EMPTY, b.state[1])
            assert.is_false(b:undoMove())
        end)

        it("flags like poles that touch", function()
            local b = newBoard(6, "easy")
            -- find two dominoes side by side across a cell edge
            local n = b.n
            for r = 1, n do
                for c = 1, n - 1 do
                    if b.dom_id[r][c] ~= b.dom_id[r][c + 1] then
                        b:setCell(r, c, Board.C_PLUS)
                        b:setCell(r, c + 1, Board.C_PLUS)
                        local conf = b:getConflicts()
                        assert.is_true(conf[r][c])
                        assert.is_true(conf[r][c + 1])
                        return
                    end
                end
            end
            error("no side-by-side dominoes found")
        end)

        it("counts poles per line", function()
            local b = newBoard(6, "easy")
            playMagnets(b)
            for i = 1, b.n do
                assert.are.equal(b.clues.row_plus[i], b:lineCount(true, i, Board.C_PLUS))
                assert.are.equal(b.clues.col_minus[i], b:lineCount(false, i, Board.C_MINUS))
            end
        end)
    end)

    describe("win, check, reveal", function()
        it("placing every magnet wins, blanks may stay unmarked", function()
            local b = newBoard(8, "medium")
            assert.is_false(b.won)
            playMagnets(b)
            assert.is_true(b.won)
            assert.is_false(b:cycle(1, 1))
            assert.is_false(b:canUndo())
        end)

        it("a magnet on a blank domino prevents the win", function()
            local b = newBoard(6, "easy")
            playMagnets(b)
            assert.is_true(b.won)
            local b2 = newBoard(6, "easy")
            playMagnets(b2)
            b2.won = false
            for d = 1, #b2.dominoes do
                if b2.solution[d] == Board.D_NEUTRAL then
                    b2:setDomino(d, Board.D_PLUS)
                    break
                end
            end
            assert.is_false(b2.won)
        end)

        it("check flags decided dominoes that differ from the solution", function()
            local b = newBoard(6, "easy")
            assert.are.equal(0, b:check())
            local d = 1
            local wrong = b.solution[d] == Board.D_PLUS and Board.D_MINUS or Board.D_PLUS
            b:setDomino(d, wrong)
            assert.are.equal(1, b:check())
            local dm = b.dominoes[d]
            assert.is_true(b:isWrong(dm[1], dm[2]))
        end)

        it("reveal shows the solution and ends the round", function()
            local b = newBoard(6, "easy")
            b:reveal()
            assert.is_true(b.won)
            assert.is_true(b.revealed)
            for d = 1, #b.dominoes do assert.are.equal(b.solution[d], b.state[d]) end
        end)
    end)

    describe("hint", function()
        it("successive hints solve the puzzle", function()
            local b = newBoard(8, "hard")
            for _ = 1, 200 do
                if b.won then break end
                local step = b:findHint()
                if not step then break end
                assert.are.equal("fill", step.kind)
                assert.are.equal(b:solutionValue(step.r, step.c), step.value)
                assert.is_true(b:applyHint(step))
            end
            assert.is_true(b.won)
        end)

        it("reports a wrong domino first and clearing it empties the domino", function()
            local b = newBoard(6, "easy")
            local d
            for i = 1, #b.dominoes do
                if b.solution[i] ~= Board.D_NEUTRAL then d = i; break end
            end
            b:setDomino(d, b.solution[d] == Board.D_PLUS and Board.D_MINUS or Board.D_PLUS)
            local step = b:findHint()
            assert.are.equal("mistake", step.kind)
            assert.are.equal(d, b.dom_id[step.r][step.c])
            assert.is_true(b:applyHint(step))
            assert.are.equal(Board.D_EMPTY, b.state[d])
        end)
    end)

    describe("serialize / load", function()
        it("round-trips dominoes, clues (hidden ones too), solution and state", function()
            local b = newBoard(8, "hard", 3)
            b:cycle(1, 1)
            b:toggleNeutral(4, 4)
            local data = b:serialize()

            local b2 = Board:new({ generate = false })
            assert.is_true(b2:load(data))
            assert.are.equal(b.n, b2.n)
            assert.are.equal(b.difficulty, b2.difficulty)
            assert.are.equal(#b.dominoes, #b2.dominoes)
            for d = 1, #b.dominoes do
                for i = 1, 4 do assert.are.equal(b.dominoes[d][i], b2.dominoes[d][i]) end
                assert.are.equal(b.solution[d], b2.solution[d])
                assert.are.equal(b.state[d], b2.state[d])
            end
            for _, kind in ipairs(Board.CLUE_KINDS) do
                for i = 1, b.n do assert.are.equal(b.clues[kind][i], b2.clues[kind][i]) end
            end
            for r = 1, b.n do
                for c = 1, b.n do assert.are.equal(b.dom_id[r][c], b2.dom_id[r][c]) end
            end
        end)

        it("saving does not stop the clock", function()
            local b = newBoard(6, "easy")
            b:serialize()
            assert.is_true(b.timer:isRunning())
        end)

        it("rejects invalid data", function()
            local b = Board:new({ generate = false })
            assert.is_false(b:load(nil))
            assert.is_false(b:load({}))
            assert.is_false(b:load({ n = 6, dominoes = { { 1, 1, 1, 2 } }, solution = { 1 }, clues = {} }))
        end)
    end)
end)
