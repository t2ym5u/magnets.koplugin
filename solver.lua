-- ---------------------------------------------------------------------------
-- solver.lua — small finite-domain logic solver shared (by copy) between
-- aquarium.koplugin and magnets.koplugin.
--
-- Both puzzles reduce to the same shape: a handful of variables, each picking
-- one of a few options (a tank's water level; a domino's polarity), tied
-- together by
--
--   * sum constraints  -- "the options chosen along this row add up to the
--                         clue": each variable on the line contributes a
--                         fixed amount per option;
--   * pair constraints -- "these two variables may not take this combination
--                         of options" (two like poles side by side).
--
-- The solver deduces like a person would, in three tiers, and reports the
-- highest tier it needed. That number IS the difficulty grade:
--
--   tier 1  bounds: an option is impossible if, even with every other
--           variable on the line at its smallest (or largest) contribution,
--           the clue cannot be met; plus direct pair eliminations.
--   tier 2  line reasoning: an option survives only if SOME combination of
--           the other variables' remaining options makes the line add up
--           exactly (a subset-sum over the whole line; sums grouped on one
--           line are met together, not one at a time).
--   tier 3  one-step trial: assume an option, run tier 1; if that
--           contradicts, the option is impossible. (Propagating the trial
--           with tier 2 as well was measured: it solved the same puzzles
--           at four times the cost.)
--
-- Every elimination is sound, so a run that leaves each variable with one
-- option has proven the solution unique -- the generator relies on that
-- instead of a separate solution count. count() is a plain backtracking
-- counter, kept for the tests to cross-check that claim independently.
--
-- Problem table:
--   nvars          number of variables
--   ksize[v]       number of options of variable v
--   sums[i]        { clue = int, vars = { v, ... }, contrib = { {x_opt1, x_opt2, ...}, ... } }
--                  (contrib[j] belongs to vars[j]); a hidden clue is simply
--                  not listed
--   pairs[i]       { a = v1, b = v2, bad = { [ka] = { [kb] = true } } }
--   groups[i]      optional: { sums = { i1, i2, ... } } -- sums on one line
--                  that tier 2 solves jointly; grouped[i] = true for each
--                  sum index that belongs to a group
-- ---------------------------------------------------------------------------

local Solver = {}

local HUGE = math.huge

-- Domains are dom[v][k] = true/false plus size[v] = number of trues.
function Solver.fullDomains(P)
    local dom, size = {}, {}
    for v = 1, P.nvars do
        local d = {}
        for k = 1, P.ksize[v] do d[k] = true end
        dom[v], size[v] = d, P.ksize[v]
    end
    return { dom = dom, size = size }
end

local function copyState(S, nvars)
    local dom, size = {}, {}
    for v = 1, nvars do
        local src, d = S.dom[v], {}
        for k = 1, #src do d[k] = src[k] end
        dom[v], size[v] = d, S.size[v]
    end
    return { dom = dom, size = size }
end

local function remove(S, v, k)
    S.dom[v][k] = false
    S.size[v] = S.size[v] - 1
    return S.size[v] > 0
end

-- Tier 1, sum part: bounds pruning. Returns ok, changed.
local function boundsSum(s, S)
    local dom = S.dom
    local vars, contrib, clue = s.vars, s.contrib, s.clue
    local mins, maxs = {}, {}
    local lo, hi = 0, 0
    for i = 1, #vars do
        local d, c = dom[vars[i]], contrib[i]
        local mn, mx = HUGE, -HUGE
        for k = 1, #c do
            if d[k] then
                local x = c[k]
                if x < mn then mn = x end
                if x > mx then mx = x end
            end
        end
        mins[i], maxs[i] = mn, mx
        lo, hi = lo + mn, hi + mx
    end
    if lo > clue or hi < clue then return false, false end
    local changed = false
    for i = 1, #vars do
        local v = vars[i]
        local d, c = dom[v], contrib[i]
        local rest_lo, rest_hi = lo - mins[i], hi - maxs[i]
        for k = 1, #c do
            if d[k] then
                local x = c[k]
                if x + rest_lo > clue or x + rest_hi < clue then
                    if not remove(S, v, k) then return false, true end
                    changed = true
                end
            end
        end
    end
    return true, changed
end

-- Tier 1, pair part: arc consistency on one forbidden-combination table.
local function revisePair(p, S)
    local dom = S.dom
    local da, db, bad = dom[p.a], dom[p.b], p.bad
    local changed = false
    for ka = 1, #da do
        if da[ka] then
            local row, supported = bad[ka], false
            for kb = 1, #db do
                if db[kb] and not (row and row[kb]) then supported = true; break end
            end
            if not supported then
                if not remove(S, p.a, ka) then return false, true end
                changed = true
            end
        end
    end
    for kb = 1, #db do
        if db[kb] then
            local supported = false
            for ka = 1, #da do
                if da[ka] and not (bad[ka] and bad[ka][kb]) then supported = true; break end
            end
            if not supported then
                if not remove(S, p.b, kb) then return false, true end
                changed = true
            end
        end
    end
    return true, changed
end

-- Tier 2: exact subset-sum over the line. Returns ok, changed.
local function exactSum(s, S)
    local dom = S.dom
    local vars, contrib, clue = s.vars, s.contrib, s.clue
    local m = #vars
    -- fwd[i][t] : sum t reachable using vars 1..i (t >= 0, capped at clue)
    local fwd = { [0] = { [0] = true } }
    for i = 1, m do
        local prev, cur = fwd[i - 1], {}
        local d, c = dom[vars[i]], contrib[i]
        for t in pairs(prev) do
            for k = 1, #c do
                if d[k] then
                    local u = t + c[k]
                    if u <= clue then cur[u] = true end
                end
            end
        end
        fwd[i] = cur
    end
    if not fwd[m][clue] then return false, false end
    local bwd = {}
    bwd[m + 1] = { [0] = true }
    for i = m, 1, -1 do
        local nxt, cur = bwd[i + 1], {}
        local d, c = dom[vars[i]], contrib[i]
        for t in pairs(nxt) do
            for k = 1, #c do
                if d[k] then
                    local u = t + c[k]
                    if u <= clue then cur[u] = true end
                end
            end
        end
        bwd[i] = cur
    end
    local changed = false
    for i = 1, m do
        local v = vars[i]
        local d, c, before, after = dom[v], contrib[i], fwd[i - 1], bwd[i + 1]
        for k = 1, #c do
            if d[k] then
                local need, ok = clue - c[k], false
                if need >= 0 then
                    for a in pairs(before) do
                        if a <= need and after[need - a] then ok = true; break end
                    end
                end
                if not ok then
                    if not remove(S, v, k) then return false, true end
                    changed = true
                end
            end
        end
    end
    return true, changed
end

-- Tier 2 on a group of sums sharing one line (magnets: a row's + count, -
-- count and blank count). The sums are solved jointly: the DP state is the
-- vector of partial sums packed into one integer, digit j in base `base`.
-- `base` leaves room for one more contribution above any clue, so adding a
-- packed option never carries, and `valid[key]` (every digit within its
-- clue) is all a step has to check. All of that only depends on the problem,
-- so it is built once per group.
local function prepareGroup(g, P)
    if g.vars then return end
    local m = #g.sums
    local clue, maxclue, maxx = {}, 0, 0
    for j = 1, m do
        local s = P.sums[g.sums[j]]
        clue[j] = s.clue
        if s.clue > maxclue then maxclue = s.clue end
        for _, c in ipairs(s.contrib) do
            for k = 1, #c do if c[k] > maxx then maxx = c[k] end end
        end
    end
    local base = maxclue + maxx + 1
    local mul = {}
    for j = 1, m do mul[j] = (j == 1) and 1 or mul[j - 1] * base end
    local vars, xkey, slot_of = {}, {}, {}
    for j = 1, m do
        local s = P.sums[g.sums[j]]
        for i, v in ipairs(s.vars) do
            local slot = slot_of[v]
            if not slot then
                slot = #vars + 1
                vars[slot], slot_of[v], xkey[slot] = v, slot, {}
                for k = 1, P.ksize[v] do xkey[slot][k] = 0 end
            end
            for k = 1, #s.contrib[i] do
                xkey[slot][k] = xkey[slot][k] + s.contrib[i][k] * mul[j]
            end
        end
    end
    -- every packed vector whose digits stay within the clues
    local valid, target = { [0] = true }, 0
    for j = 1, m do
        target = target + clue[j] * mul[j]
        local nxt = {}
        for key in pairs(valid) do
            for x = 0, clue[j] do nxt[key + x * mul[j]] = true end
        end
        valid = nxt
    end
    g.vars, g.xkey, g.valid, g.target = vars, xkey, valid, target
end

local function exactGroup(g, P, S)
    prepareGroup(g, P)
    local dom = S.dom
    local vars, xkey, valid, target = g.vars, g.xkey, g.valid, g.target
    local nv = #vars
    local function step(prev, slot)
        local cur, d, xk = {}, dom[vars[slot]], xkey[slot]
        for key in pairs(prev) do
            for k = 1, #d do
                if d[k] then
                    local u = key + xk[k]
                    if valid[u] then cur[u] = true end
                end
            end
        end
        return cur
    end
    local fwd = { [0] = { [0] = true } }
    for i = 1, nv do fwd[i] = step(fwd[i - 1], i) end
    if not fwd[nv][target] then return false, false end
    local bwd = { [nv + 1] = { [0] = true } }
    for i = nv, 1, -1 do bwd[i] = step(bwd[i + 1], i) end
    local changed = false
    for i = 1, nv do
        local v = vars[i]
        local d, xk, before, after = dom[v], xkey[i], fwd[i - 1], bwd[i + 1]
        for k = 1, #d do
            if d[k] then
                local ok = false
                for key in pairs(before) do
                    local u = key + xk[k]
                    if valid[u] and after[target - u] then ok = true; break end
                end
                if not ok then
                    if not remove(S, v, k) then return false, true end
                    changed = true
                end
            end
        end
    end
    return true, changed
end

-- Constraint index, built once per problem: every tier-1 constraint (sums
-- first, then pairs) and, per variable, the constraints it appears in.
local function index(P)
    if P._cons then return end
    local cons, of_var = {}, {}
    for v = 1, P.nvars do of_var[v] = {} end
    for _, s in ipairs(P.sums) do
        cons[#cons + 1] = { sum = s, vars = s.vars }
        for _, v in ipairs(s.vars) do table.insert(of_var[v], #cons) end
    end
    for _, p in ipairs(P.pairs or {}) do
        cons[#cons + 1] = { pair = p, vars = { p.a, p.b } }
        table.insert(of_var[p.a], #cons)
        table.insert(of_var[p.b], #cons)
    end
    P._cons, P._of_var = cons, of_var
end

-- Runs tier 1 to a fixpoint with a work queue: when a constraint narrows a
-- domain, only the constraints sharing one of its variables are revisited.
-- `seed_var`, when given, starts the queue from that variable's constraints
-- alone -- valid when the state was at a fixpoint before that variable was
-- narrowed (a trial). Returns ok.
local function fix1(P, S, seed_var)
    index(P)
    local cons, of_var = P._cons, P._of_var
    local queue, queued, head = {}, {}, 1
    local function push(ci)
        if not queued[ci] then queued[ci] = true; queue[#queue + 1] = ci end
    end
    if seed_var then
        for _, ci in ipairs(of_var[seed_var]) do push(ci) end
    else
        for ci = 1, #cons do push(ci) end
    end
    local size, before = S.size, {}
    while head <= #queue do
        local ci = queue[head]
        head = head + 1
        queued[ci] = nil
        local con = cons[ci]
        local vars = con.vars
        for i = 1, #vars do before[i] = size[vars[i]] end
        local ok, ch
        if con.sum then ok, ch = boundsSum(con.sum, S) else ok, ch = revisePair(con.pair, S) end
        if not ok then return false end
        if ch then
            for i = 1, #vars do
                local v = vars[i]
                if size[v] ~= before[i] then
                    for _, cj in ipairs(of_var[v]) do
                        if cj ~= ci then push(cj) end
                    end
                end
            end
            -- bounds pruning is not idempotent: run this one again too
            push(ci)
        end
    end
    return true
end

-- One tier-2 sweep: grouped sums jointly, the rest one by one.
-- Returns ok, changed.
local function sweep2(P, S)
    local changed = false
    local grouped = P.grouped or {}
    if P.groups then
        for _, g in ipairs(P.groups) do
            local ok, ch = exactGroup(g, P, S)
            if not ok then return false, true end
            if ch then changed = true end
        end
    end
    for i = 1, #P.sums do
        if not grouped[i] then
            local ok, ch = exactSum(P.sums[i], S)
            if not ok then return false, true end
            if ch then changed = true end
        end
    end
    return true, changed
end

-- Tiers 1 and 2 to a fixpoint. Returns ok, used_tier2.
local function fix12(P, S)
    local used2 = false
    while true do
        if not fix1(P, S) then return false, used2 end
        local ok, ch = sweep2(P, S)
        if not ok then return false, true end
        if not ch then return true, used2 end
        used2 = true
    end
end

local function isSolved(P, S)
    for v = 1, P.nvars do
        if S.size[v] ~= 1 then return false end
    end
    return true
end

-- Tier 3 sweep: one-step trial (tier-1 propagation) on every open option.
-- Returns ok, changed.
local function sweep3(P, S)
    local changed = false
    for v = 1, P.nvars do
        if S.size[v] > 1 then
            local d = S.dom[v]
            for k = 1, #d do
                if d[k] and S.size[v] > 1 then
                    local T = copyState(S, P.nvars)
                    local td = T.dom[v]
                    for j = 1, #td do td[j] = (j == k) end
                    T.size[v] = 1
                    if not fix1(P, T, v) then
                        if not remove(S, v, k) then return false, true end
                        changed = true
                        if not fix12(P, S) then return false, true end
                    end
                end
            end
        end
    end
    return true, changed
end

-- Deduces as far as `cap` (1..3) allows.
-- Returns status ("solved" | "stuck" | "contradiction"), tier_used, state.
function Solver.solve(P, cap, S)
    S = S or Solver.fullDomains(P)
    cap = cap or 3
    local tier = 1
    while true do
        if not fix1(P, S) then return "contradiction", tier, S end
        if isSolved(P, S) then return "solved", tier, S end
        local progressed = false
        if cap >= 2 then
            local ok, ch = sweep2(P, S)
            if not ok then return "contradiction", math.max(tier, 2), S end
            if ch then tier = math.max(tier, 2); progressed = true end
        end
        if not progressed and cap >= 3 then
            local ok, ch = sweep3(P, S)
            if not ok then return "contradiction", 3, S end
            if ch then tier = 3; progressed = true end
        end
        if not progressed then return "stuck", tier, S end
    end
end

-- The option chosen for each variable in a solved state.
function Solver.assignment(S)
    local out = {}
    for v = 1, #S.dom do
        local d = S.dom[v]
        for k = 1, #d do
            if d[k] then out[v] = k; break end
        end
    end
    return out
end

-- Backtracking solution counter (tier-1 propagation, smallest domain first).
-- Returns count (capped at limit), exhausted (node budget ran out).
function Solver.count(P, limit, budget)
    limit, budget = limit or 2, budget or 200000
    local found, nodes, exhausted = 0, 0, false
    local function rec(S)
        if found >= limit or exhausted then return end
        nodes = nodes + 1
        if nodes > budget then exhausted = true; return end
        if not fix1(P, S) then return end
        local best, best_size = nil, HUGE
        for v = 1, P.nvars do
            local sz = S.size[v]
            if sz > 1 and sz < best_size then best, best_size = v, sz end
        end
        if not best then
            found = found + 1
            return
        end
        local d = S.dom[best]
        for k = 1, #d do
            if d[k] then
                local T = copyState(S, P.nvars)
                local td = T.dom[best]
                for j = 1, #td do td[j] = (j == k) end
                T.size[best] = 1
                rec(T)
                if found >= limit or exhausted then return end
            end
        end
    end
    rec(Solver.fullDomains(P))
    return found, exhausted
end

return Solver
