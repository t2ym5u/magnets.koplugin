local DIR = debug.getinfo(1, "S").source:sub(2):match("(.*[/\\])") or "./"
package.path = DIR .. "?.lua;" .. package.path

-- solver.lua is shared by copy between aquarium and magnets; this spec is too.
describe("Solver", function()
    local Solver

    setup(function()
        Solver = require("solver")
    end)

    local function domainOf(S, v)
        local out = {}
        for k, ok in ipairs(S.dom[v]) do if ok then out[#out + 1] = k end end
        return out
    end

    it("tier 1 settles a line by bounds alone", function()
        -- two variables, options contribute {0, 1}; clue 2 forces both to 1
        local P = { nvars = 2, ksize = { 2, 2 }, sums = {
            { clue = 2, vars = { 1, 2 }, contrib = { { 0, 1 }, { 0, 1 } } } } }
        local st, tier, S = Solver.solve(P, 1)
        assert.are.equal("solved", st)
        assert.are.equal(1, tier)
        assert.are.same({ 2, 2 }, Solver.assignment(S))
    end)

    it("tier 2 sees what bounds cannot: an odd clue needs the odd variable", function()
        -- x in {0,1}, three y in {0,2}, clue 3: bounds prune nothing, but only
        -- x = 1 can make the sum odd
        local P = { nvars = 4, ksize = { 2, 2, 2, 2 }, sums = {
            { clue = 3, vars = { 1, 2, 3, 4 },
              contrib = { { 0, 1 }, { 0, 2 }, { 0, 2 }, { 0, 2 } } } } }
        local st1, _, S1 = Solver.solve(P, 1)
        assert.are.equal("stuck", st1)
        assert.are.same({ 1, 2 }, domainOf(S1, 1))
        local st2, tier2, S2 = Solver.solve(P, 2)
        assert.are.equal("stuck", st2)     -- which y is the 2 stays open
        assert.are.equal(2, tier2)
        assert.are.same({ 2 }, domainOf(S2, 1))
        assert.are.equal(3, (Solver.count(P, 5)))
    end)

    it("grouped sums are met together", function()
        -- one variable per option contributes to both sums: (1,0), (0,1), (0,0);
        -- two variables; sums a = 1 and b = 1. Separately each var could be
        -- anything; jointly the two must split (1,0)+(0,1).
        local P = { nvars = 2, ksize = { 3, 3 }, sums = {
            { clue = 1, vars = { 1, 2 }, contrib = { { 1, 0, 0 }, { 1, 0, 0 } } },
            { clue = 1, vars = { 1, 2 }, contrib = { { 0, 1, 0 }, { 0, 1, 0 } } } },
            groups = { { sums = { 1, 2 } } }, grouped = { true, true } }
        local _, _, S = Solver.solve(P, 2)
        assert.are.same({ 1, 2 }, domainOf(S, 1))
        assert.are.same({ 1, 2 }, domainOf(S, 2))
        assert.are.equal(2, (Solver.count(P, 5)))
    end)

    it("pair constraints remove unsupported options", function()
        -- v1 forced to option 1 by its sum; option 1 of v2 clashes with it
        local P = { nvars = 2, ksize = { 2, 2 }, sums = {
            { clue = 1, vars = { 1 }, contrib = { { 1, 0 } } } },
            pairs = { { a = 1, b = 2, bad = { [1] = { [1] = true } } } } }
        local st, _, S = Solver.solve(P, 1)
        assert.are.equal("solved", st)
        assert.are.same({ 1, 2 }, Solver.assignment(S))
    end)

    it("reports a contradiction", function()
        local P = { nvars = 1, ksize = { 2 }, sums = {
            { clue = 5, vars = { 1 }, contrib = { { 0, 1 } } } } }
        assert.are.equal("contradiction", (Solver.solve(P, 3)))
        assert.are.equal(0, (Solver.count(P, 2)))
    end)
end)
