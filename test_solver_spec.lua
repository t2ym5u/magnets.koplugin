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

    -- Since 1.1.0 the solver works on bit masks with memoised propagators.
    -- Against a plain enumeration of every assignment on small random
    -- problems: no deduction may drop an option that some solution uses,
    -- "solved" must mean exactly one solution (the one returned),
    -- "contradiction" none, and count() must agree. (The new solver was also
    -- cross-checked against the 1.0.x one, same statuses, tiers and domains.)
    it("agrees with brute force on random small problems", function()
        local function randomProblem()
            local nv = math.random(2, 5)
            local P = { nvars = nv, ksize = {}, sums = {}, pairs = {} }
            for v = 1, nv do P.ksize[v] = math.random(2, 4) end
            local sol = {}
            for v = 1, nv do sol[v] = math.random(P.ksize[v]) end
            for _ = 1, math.random(1, 3) do
                local s = { vars = {}, contrib = {}, clue = 0 }
                for v = 1, nv do
                    if math.random() < 0.6 then
                        local c = {}
                        for k = 1, P.ksize[v] do c[k] = math.random(0, 2) end
                        s.vars[#s.vars + 1], s.contrib[#s.contrib + 1] = v, c
                        s.clue = s.clue + c[sol[v]]
                    end
                end
                if math.random() < 0.15 then s.clue = s.clue + 1 end
                if #s.vars > 0 then P.sums[#P.sums + 1] = s end
            end
            if #P.sums >= 2 and math.random() < 0.5 then
                P.groups, P.grouped = { { sums = { 1, 2 } } }, { true, true }
            end
            for _ = 1, math.random(0, 2) do
                local a, b = math.random(nv), math.random(nv)
                if a ~= b then
                    local bad = {}
                    for ka = 1, P.ksize[a] do
                        for kb = 1, P.ksize[b] do
                            if math.random() < 0.3 and not (ka == sol[a] and kb == sol[b]) then
                                bad[ka] = bad[ka] or {}
                                bad[ka][kb] = true
                            end
                        end
                    end
                    P.pairs[#P.pairs + 1] = { a = a, b = b, bad = bad }
                end
            end
            return P
        end
        local function solutions(P)
            local out, cur = {}, {}
            local function rec(v)
                if v > P.nvars then
                    for _, s in ipairs(P.sums) do
                        local t = 0
                        for j, w in ipairs(s.vars) do t = t + s.contrib[j][cur[w]] end
                        if t ~= s.clue then return end
                    end
                    for _, p in ipairs(P.pairs) do
                        if p.bad[cur[p.a]] and p.bad[cur[p.a]][cur[p.b]] then return end
                    end
                    local c = {}
                    for w = 1, P.nvars do c[w] = cur[w] end
                    out[#out + 1] = c
                    return
                end
                for k = 1, P.ksize[v] do cur[v] = k; rec(v + 1) end
            end
            rec(1)
            return out
        end
        math.randomseed(7)
        for _ = 1, 400 do
            local P = randomProblem()
            local sols = solutions(P)
            assert.are.equal(math.min(#sols, 3), (Solver.count(P, 3)))
            for cap = 1, 3 do
                local st, _, S = Solver.solve(P, cap)
                if st == "contradiction" then
                    assert.are.equal(0, #sols)
                else
                    for _, sol in ipairs(sols) do
                        for v = 1, P.nvars do assert.is_true(S.dom[v][sol[v]]) end
                    end
                    if st == "solved" then
                        assert.are.equal(1, #sols)
                        assert.are.same(sols[1], Solver.assignment(S))
                    end
                end
            end
        end
    end)
    -- 1.2.0: the generators hide clues by switching sums off (P.off) and
    -- solve each try incrementally from a base (Solver.trial). Both must
    -- give exactly what a solve from scratch of the smaller problem gives.
    -- (Cross-checked in development against the 1.1.0 solver on 36,000
    -- generator-shaped instances, 0 mismatches.)
    it("switched-off sums and incremental trials agree with solving from scratch", function()
        local function randomProblem()
            local nv = math.random(3, 7)
            local P = { nvars = nv, ksize = {}, sums = {}, pairs = {} }
            for v = 1, nv do P.ksize[v] = math.random(2, 4) end
            local sol = {}
            for v = 1, nv do sol[v] = math.random(P.ksize[v]) end
            for _ = 1, math.random(2, 6) do
                local s = { vars = {}, contrib = {}, clue = 0 }
                for v = 1, nv do
                    if math.random() < 0.6 then
                        local c = {}
                        for k = 1, P.ksize[v] do c[k] = math.random(0, 2) end
                        s.vars[#s.vars + 1], s.contrib[#s.contrib + 1] = v, c
                        s.clue = s.clue + c[sol[v]]
                    end
                end
                if #s.vars > 0 then P.sums[#P.sums + 1] = s end
            end
            if #P.sums >= 2 and math.random() < 0.5 then
                P.groups, P.grouped = { { sums = { 1, 2 } } }, { true, true }
            end
            for _ = 1, math.random(0, 3) do
                local a, b = math.random(nv), math.random(nv)
                if a ~= b then
                    local bad = {}
                    for ka = 1, P.ksize[a] do
                        for kb = 1, P.ksize[b] do
                            if math.random() < 0.3 and not (ka == sol[a] and kb == sol[b]) then
                                bad[ka] = bad[ka] or {}
                                bad[ka][kb] = true
                            end
                        end
                    end
                    P.pairs[#P.pairs + 1] = { a = a, b = b, bad = bad }
                end
            end
            return P
        end
        -- the same problem with the sums in `off` left out
        local function without(P, off)
            local Q = { nvars = P.nvars, ksize = P.ksize, sums = {}, pairs = P.pairs }
            local map = {}
            for i, s in ipairs(P.sums) do
                if not off[i] then Q.sums[#Q.sums + 1] = s; map[i] = #Q.sums end
            end
            if P.groups and map[1] and map[2] then
                Q.groups, Q.grouped = { { sums = { map[1], map[2] } } }, {}
                Q.grouped[map[1]], Q.grouped[map[2]] = true, true
            end
            return Q
        end
        local function randomOff(P, keep)
            local off = {}
            for i = 1, #P.sums do
                if keep[i] == nil and math.random() < 0.4 then off[i] = true end
            end
            return off
        end
        math.randomseed(11)
        for _ = 1, 300 do
            local P = randomProblem()
            local off = randomOff(P, {})
            for cap = 1, 2 do
                local st1, t1, S1 = Solver.solve(without(P, off), cap)
                P.off = off
                local st2, t2, S2 = Solver.solve(P, cap)
                assert.are.equal(st1, st2)
                assert.are.equal(t1, t2)
                for v = 1, P.nvars do assert.are.same(S1.dom[v], S2.dom[v]) end
                -- a base with more sums off, moved on part-way, then a trial
                local boff = {}
                for i in pairs(off) do boff[i] = true end
                for i = 1, #P.sums do
                    if math.random() < 0.5 then boff[i] = true end
                end
                P.off = boff
                local base = Solver.newBase(P, cap)
                local mid = {}
                for i in pairs(boff) do
                    if off[i] or math.random() < 0.5 then mid[i] = true end
                end
                P.off = mid
                Solver.extendBase(P, base)
                P.off = off
                local st3, t3 = Solver.trial(P, base)
                assert.are.equal(st1, st3)
                if st1 == "solved" then assert.are.equal(t1, t3) end
                P.off = nil
            end
        end
    end)

    -- A group whose sums but two are implied (magnets' blank count) runs a
    -- faster DP on those two: it must agree with the general group DP.
    it("an implied group deduces exactly what the full group does", function()
        math.randomseed(5)
        for _ = 1, 300 do
            local nv = math.random(2, 6)
            local P = { nvars = nv, ksize = {}, sums = {} }
            local A = { vars = {}, contrib = {}, clue = 0 }
            local B = { vars = {}, contrib = {}, clue = 0 }
            local C = { vars = {}, contrib = {}, clue = 0 }
            for v = 1, nv do
                local ks = math.random(2, 4)
                P.ksize[v] = ks
                local a, b, c, total = {}, {}, {}, math.random(2, 3)
                for k = 1, ks do
                    a[k] = math.random(0, 2)
                    b[k] = math.random(0, total - math.min(a[k], total))
                    a[k] = math.min(a[k], total)
                    c[k] = total - a[k] - b[k]
                end
                local pick = math.random(ks)
                A.vars[v], B.vars[v], C.vars[v] = v, v, v
                A.contrib[v], B.contrib[v], C.contrib[v] = a, b, c
                A.clue, B.clue, C.clue = A.clue + a[pick], B.clue + b[pick], C.clue + c[pick]
            end
            if math.random() < 0.2 then A.clue = A.clue + 1; C.clue = C.clue - 1 end
            P.sums = { A, B, C }
            P.grouped = { true, true, true }
            local function solveWith(implied)
                P.groups = { { sums = { 1, 2, 3 }, implied = implied } }
                P._cons, P._of_var = nil, nil
                for _, s in ipairs(P.sums) do s._xs = nil end
                return Solver.solve(P, 2)
            end
            local st1, t1, S1 = solveWith(nil)
            local st2, t2, S2 = solveWith({ [3] = true })
            assert.are.equal(st1, st2)
            assert.are.equal(t1, t2)
            if st1 ~= "contradiction" then
                for v = 1, nv do assert.are.same(S1.dom[v], S2.dom[v]) end
            end
        end
    end)
end)
