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
--                  (a group may also carry `shared`, a table in which
--                  tier 2 keeps its per-group data for other problems with
--                  the very same sums on that line)
-- ---------------------------------------------------------------------------
--
-- Inside, a domain is a bit mask (bit k-1 set = option k still possible) so
-- that each propagator works on whole domains at once; what a propagator
-- derives from a mask is memoised on the constraint. The state handed
-- back by solve() also offers the public form, dom[v][k] = boolean.
-- ---------------------------------------------------------------------------

local bit = require("bit")
local band, bor, lshift = bit.band, bit.bor, bit.lshift

local Solver = {}

local HUGE = math.huge

-- BIT[k] = mask of option k; POP[mask] = number of options in it.
local MAX_OPTIONS = 12
local BIT, POP, LOW = {}, { [0] = 0 }, {}
for k = 1, 31 do BIT[k] = lshift(1, k - 1) end
for m = 1, BIT[MAX_OPTIONS + 1] - 1 do
    POP[m] = POP[math.floor(m / 2)] + m % 2
end
for k = 1, MAX_OPTIONS do LOW[BIT[k]] = k end   -- option of a one-option mask

local function fullMask(ks)
    assert(ks <= MAX_OPTIONS, "solver: too many options")
    return BIT[ks + 1] - 1
end

-- Public form, kept for callers and tests: dom[v][k] = true/false plus
-- size[v] = number of trues.
function Solver.fullDomains(P)
    local dom, size = {}, {}
    for v = 1, P.nvars do
        local d = {}
        for k = 1, P.ksize[v] do d[k] = true end
        dom[v], size[v] = d, P.ksize[v]
    end
    return { dom = dom, size = size }
end

local function fullState(P)
    local m, size = {}, {}
    for v = 1, P.nvars do m[v], size[v] = fullMask(P.ksize[v]), P.ksize[v] end
    return { m = m, size = size }
end

local function fromPublic(S, P)
    if S.m then return S end
    local m, size = {}, {}
    for v = 1, P.nvars do
        local x = 0
        for k = 1, P.ksize[v] do
            if S.dom[v][k] then x = x + BIT[k] end
        end
        m[v], size[v] = x, POP[x]
    end
    return { m = m, size = size }
end

-- The public form is only built when someone reads S.dom (the generator
-- only looks at the status and tier).
local Public = {
    __index = function(S, key)
        if key ~= "dom" then return nil end
        local dom, ksize = {}, rawget(S, "_ksize")
        for v = 1, #ksize do
            local d, x = {}, S.m[v]
            for k = 1, ksize[v] do d[k] = band(x, BIT[k]) ~= 0 end
            dom[v] = d
        end
        rawset(S, "dom", dom)
        return dom
    end,
}

local function toPublic(S, P)
    S._ksize = P.ksize
    return setmetatable(S, Public)
end

local function copyState(S, nvars)
    local m, size, sm, ss = {}, {}, S.m, S.size
    for v = 1, nvars do m[v], size[v] = sm[v], ss[v] end
    return { m = m, size = size }
end

-- fix1's work queue while it runs (nil otherwise): narrowing a variable
-- queues every other constraint it appears in.
local q_list, q_in, q_tail, q_of_var, q_cur

-- Narrows v to `x` (a strict subset of its mask). A state made by
-- fullState also stamps every change (`tick` counts them, vt[v] = tick of
-- v's last one) so sweep2 can skip a line none of whose variables moved
-- since its last run. Returns false when the domain is empty.
local function narrow(S, v, x)
    S.m[v] = x
    local sz = POP[x]
    S.size[v] = sz
    local vt = S.vt
    if vt then
        local t = S.tick + 1
        S.tick, vt[v] = t, t
    end
    if q_list then
        local list = q_of_var[v]
        for j = 1, #list do
            local cj = list[j]
            if cj ~= q_cur and not q_in[cj] then
                q_in[cj] = true
                q_tail = q_tail + 1
                q_list[q_tail] = cj
            end
        end
    end
    return sz > 0
end

local function stamped(S, nvars)
    if S.vt then return end
    local vt = {}
    for v = 1, nvars do vt[v] = 0 end
    S.vt, S.tick, S.ran = vt, 0, {}
end

-- Per-variable memo tables of a sum (built once; the solver never changes
-- a sum's clue, vars or contrib, so callers may share sums between
-- problems).
local function sumMemo(s, name)
    local t = s[name]
    if not t then
        t = {}
        for i = 1, #s.vars do t[i] = {} end
        s[name] = t
    end
    return t
end

-- Smallest and largest contribution of the options in mask x.
local function spread(c, x)
    local mn, mx = HUGE, -HUGE
    for k = 1, #c do
        if band(x, BIT[k]) ~= 0 then
            local v = c[k]
            if v < mn then mn = v end
            if v > mx then mx = v end
        end
    end
    return mn, mx
end

-- Tier 1, sum part: bounds pruning. Returns ok, changed.
local b_min, b_max = {}, {}   -- scratch (no call re-enters boundsSum)

local function boundsSum(s, S)
    local sm = S.m
    local vars, contrib, clue = s.vars, s.contrib, s.clue
    local mins, maxs = s._min or sumMemo(s, "_min"), s._max or sumMemo(s, "_max")
    local nv = #vars
    local lo, hi, span = 0, 0, 0
    for i = 1, nv do
        local x = sm[vars[i]]
        local mn = mins[i][x]
        local mx
        if mn then
            mx = maxs[i][x]
        else
            mn, mx = spread(contrib[i], x)
            mins[i][x], maxs[i][x] = mn, mx
        end
        b_min[i], b_max[i] = mn, mx
        lo, hi = lo + mn, hi + mx
        if mx - mn > span then span = mx - mn end
    end
    if lo > clue or hi < clue then return false, false end
    -- An option x of variable i goes when x + (lo - min_i) > clue or
    -- x + (hi - max_i) < clue; as min_i <= x <= max_i, no option can go
    -- while every variable's spread fits in both slacks -- the usual case.
    if span <= clue - lo and span <= hi - clue then return true, false end
    local changed = false
    for i = 1, nv do
        local v = vars[i]
        local x, c = sm[v], contrib[i]
        local rest_lo, rest_hi = lo - b_min[i], hi - b_max[i]
        local keep = x
        for k = 1, #c do
            if band(x, BIT[k]) ~= 0 then
                local y = c[k]
                if y + rest_lo > clue or y + rest_hi < clue then keep = keep - BIT[k] end
            end
        end
        if keep ~= x then
            if not narrow(S, v, keep) then return false, true end
            changed = true
        end
    end
    return true, changed
end

-- Options of one side that keep a partner among the other side's mask
-- `y`, memoised by y. `bad_of(k1, k2)` says whether the combination is
-- forbidden with k1 on this side.
local function pairSupport(memo, y, n_this, n_other, bad, flip)
    local r = memo[y]
    if r then return r end
    r = 0
    for k1 = 1, n_this do
        for k2 = 1, n_other do
            if band(y, BIT[k2]) ~= 0 then
                local ka, kb = k1, k2
                if flip then ka, kb = k2, k1 end
                local row = bad[ka]
                if not (row and row[kb]) then r = r + BIT[k1]; break end
            end
        end
    end
    memo[y] = r
    return r
end

-- Tier 1, pair part: arc consistency on one forbidden-combination table.
local function revisePair(p, S, P)
    local sm = S.m
    local a, b = p.a, p.b
    local ra, rb = p._ra, p._rb
    if not ra then ra, rb = {}, {}; p._ra, p._rb = ra, rb end
    local na, nb = P.ksize[a], P.ksize[b]
    local xa, xb = sm[a], sm[b]
    local changed = false
    local ka = band(xa, pairSupport(ra, xb, na, nb, p.bad, false))
    if ka ~= xa then
        if not narrow(S, a, ka) then return false, true end
        changed = true
    end
    local kb = band(xb, pairSupport(rb, ka, nb, na, p.bad, true))
    if kb ~= xb then
        if not narrow(S, b, kb) then return false, true end
        changed = true
    end
    return true, changed
end

-- Distinct contributions of the options in mask x, memoised per variable.
local function distinct(memo, c, x)
    local r = memo[x]
    if r then return r end
    r = {}
    local seen = {}
    for k = 1, #c do
        if band(x, BIT[k]) ~= 0 and not seen[c[k]] then
            seen[c[k]] = true
            r[#r + 1] = c[k]
        end
    end
    memo[x] = r
    return r
end

-- Tier 2: exact subset-sum over the line. Returns ok, changed.
-- Contributions are >= 0, so the reachable partial sums are 0..clue; with
-- clue <= 29 a set of them fits one bit mask (bit t = sum t reachable).
local function exactSum(s, S)
    local sm = S.m
    local vars, contrib, clue = s.vars, s.contrib, s.clue
    if clue < 0 then return false, false end
    assert(clue <= 29, "solver: clue too large")
    local xs = s._xs or sumMemo(s, "_xs")
    local m = #vars
    local limit = BIT[clue + 2] - 1
    local fwd, bwd = { [0] = 1 }, { [m + 1] = 1 }
    for i = 1, m do
        local prev, cur = fwd[i - 1], 0
        local d = distinct(xs[i], contrib[i], sm[vars[i]])
        for j = 1, #d do
            local y = d[j]
            if y <= clue then cur = bor(cur, lshift(prev, y)) end
        end
        fwd[i] = band(cur, limit)
    end
    if band(fwd[m], BIT[clue + 1]) == 0 then return false, false end
    for i = m, 1, -1 do
        local nxt, cur = bwd[i + 1], 0
        local d = distinct(xs[i], contrib[i], sm[vars[i]])
        for j = 1, #d do
            local y = d[j]
            if y <= clue then cur = bor(cur, lshift(nxt, y)) end
        end
        bwd[i] = band(cur, limit)
    end
    local changed = false
    for i = 1, m do
        local v = vars[i]
        -- every total the other variables can reach together
        local before, after, both = fwd[i - 1], bwd[i + 1], 0
        for t = 0, clue do
            if band(after, BIT[t + 1]) ~= 0 then both = bor(both, lshift(before, t)) end
        end
        local x, c = sm[v], contrib[i]
        local keep = x
        for k = 1, #c do
            if band(x, BIT[k]) ~= 0 then
                local need = clue - c[k]
                if need < 0 or band(both, BIT[need + 1]) == 0 then keep = keep - BIT[k] end
            end
        end
        if keep ~= x then
            if not narrow(S, v, keep) then return false, true end
            changed = true
        end
    end
    return true, changed
end

-- Packed vectors whose digits stay within the clues, by (base, clues). Only
-- depends on those numbers, and digging hides one clue at a time, so most
-- lines repeat from one solve to the next; the cache is dropped when it
-- grows (it is a pure function of its key, so results never depend on it).
local valid_cache, valid_count = {}, 0

local function validKeys(clue, mul, base)
    local key = base .. ":" .. table.concat(clue, ",")
    local valid = valid_cache[key]
    if valid then return valid end
    valid = { [0] = true }
    for j = 1, #clue do
        local nxt = {}
        for k in pairs(valid) do
            for x = 0, clue[j] do nxt[k + x * mul[j]] = true end
        end
        valid = nxt
    end
    if valid_count >= 256 then valid_cache, valid_count = {}, 0 end
    valid_cache[key], valid_count = valid, valid_count + 1
    return valid
end

-- Tier 2 on a group of sums sharing one line (magnets: a row's + count, -
-- count and blank count). The sums are solved jointly: the DP state is the
-- vector of partial sums packed into one integer, digit j in base `base`.
-- `base` leaves room for one more contribution above any clue, so adding a
-- packed option never carries, and `valid[key]` (every digit within its
-- clue) is all a step has to check. All of that only depends on the problem,
-- so it is built once per group -- or once per `g.shared` table, which a
-- caller may pass to share it between problems whose group holds the very
-- same sums (a dig re-solving one tiling with one clue fewer each time).
local function prepareGroup(g, P)
    if g.vars then return end
    local sh = g.shared
    if sh and sh.vars then
        g.vars, g.xkey, g.valid, g.target, g.xs = sh.vars, sh.xkey, sh.valid, sh.target, sh.xs
        return
    end
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
    local target = 0
    for j = 1, m do target = target + clue[j] * mul[j] end
    local xs = {}
    for slot = 1, #vars do xs[slot] = {} end
    g.vars, g.xkey, g.valid, g.target, g.xs = vars, xkey, validKeys(clue, mul, base), target, xs
    if sh then
        sh.vars, sh.xkey, sh.valid, sh.target, sh.xs = g.vars, g.xkey, g.valid, g.target, g.xs
    end
end

-- One DP layer is a list of the reachable packed keys plus a set of them.
local function groupStep(prev, d, valid)
    local list, set = {}, {}
    local n = 0
    local plist = prev.list
    for i = 1, #plist do
        local key = plist[i]
        for j = 1, #d do
            local u = key + d[j]
            if valid[u] and not set[u] then
                set[u] = true
                n = n + 1
                list[n] = u
            end
        end
    end
    return { list = list, set = set }
end

-- Variables already down to one option are folded into the start key
-- (contributions are >= 0 and only the total matters, so the order the
-- variables are added in changes nothing); the DP runs over the open ones.
local function exactGroup(g, P, S)
    prepareGroup(g, P)
    local sm, size = S.m, S.size
    local vars, xkey, valid, target, xs = g.vars, g.xkey, g.valid, g.target, g.xs
    local open, start = {}, 0
    for i = 1, #vars do
        local v = vars[i]
        if size[v] == 1 then
            start = start + xkey[i][LOW[sm[v]]]
        else
            open[#open + 1] = i
        end
    end
    if not valid[start] then return false, false end
    local nv = #open
    local fwd = { [0] = { list = { start }, set = { [start] = true } } }
    for j = 1, nv do
        local i = open[j]
        fwd[j] = groupStep(fwd[j - 1], distinct(xs[i], xkey[i], sm[vars[i]]), valid)
    end
    if not fwd[nv].set[target] then return false, false end
    local bwd = { [nv + 1] = { list = { 0 }, set = { [0] = true } } }
    for j = nv, 1, -1 do
        local i = open[j]
        bwd[j] = groupStep(bwd[j + 1], distinct(xs[i], xkey[i], sm[vars[i]]), valid)
    end
    local changed = false
    for j = 1, nv do
        local i = open[j]
        local v = vars[i]
        local x, xk, before, after = sm[v], xkey[i], fwd[j - 1].list, bwd[j + 1].set
        local keep = x
        for k = 1, #xk do
            if band(x, BIT[k]) ~= 0 then
                local ok, y = false, xk[k]
                for t = 1, #before do
                    local u = before[t] + y
                    if valid[u] and after[target - u] then ok = true; break end
                end
                if not ok then keep = keep - BIT[k] end
            end
        end
        if keep ~= x then
            if not narrow(S, v, keep) then return false, true end
            changed = true
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
-- (The queue lives in the q_* upvalues so that narrow() can feed it; fix1
-- never runs inside another fix1.)
local function fix1(P, S, seed_var)
    index(P)
    local cons, of_var = P._cons, P._of_var
    local queue, queued, tail, head = {}, {}, 0, 1
    if seed_var then
        local list = of_var[seed_var]
        for i = 1, #list do
            local ci = list[i]
            if not queued[ci] then queued[ci] = true; tail = tail + 1; queue[tail] = ci end
        end
    else
        for ci = 1, #cons do queued[ci] = true; queue[ci] = ci end
        tail = #cons
    end
    q_list, q_in, q_tail, q_of_var = queue, queued, tail, of_var
    local ok = true
    while head <= q_tail do
        local ci = queue[head]
        head = head + 1
        queued[ci] = nil
        q_cur = ci
        local con = cons[ci]
        local ch
        if con.sum then ok, ch = boundsSum(con.sum, S) else ok, ch = revisePair(con.pair, S, P) end
        if not ok then break end
        -- bounds pruning is not idempotent: run this one again too
        if ch and not queued[ci] then
            queued[ci] = true; q_tail = q_tail + 1; queue[q_tail] = ci
        end
    end
    q_list, q_in, q_of_var, q_cur = nil, nil, nil, nil
    return ok
end

-- One tier-2 sweep: grouped sums jointly, the rest one by one.
-- Both propagators are exact (every option they keep has a full support),
-- so a second run on unchanged domains is a no-op: a line whose variables
-- have not moved since its last run is skipped.
local function moved(S, key, vars)
    local last = S.ran[key]
    if not last then return true end
    local vt = S.vt
    for i = 1, #vars do
        if vt[vars[i]] > last then return true end
    end
    return false
end

-- Returns ok, changed.
local function sweep2(P, S)
    stamped(S, P.nvars)
    local changed = false
    local grouped = P.grouped or {}
    if P.groups then
        for _, g in ipairs(P.groups) do
            prepareGroup(g, P)
            if moved(S, g, g.vars) then
                local ok, ch = exactGroup(g, P, S)
                if not ok then return false, true end
                if ch then changed = true end
                S.ran[g] = S.tick
            end
        end
    end
    for i = 1, #P.sums do
        if not grouped[i] then
            local s = P.sums[i]
            if moved(S, s, s.vars) then
                local ok, ch = exactSum(s, S)
                if not ok then return false, true end
                if ch then changed = true end
                S.ran[s] = S.tick
            end
        end
    end
    return true, changed
end

-- The tier-2 code stays in LuaJIT's interpreter: its many short,
-- data-dependent loops made the JIT compile trace after trace until its
-- trace cache filled up and was flushed, again and again -- most of a hard
-- generation went into the compiler (measured: twice as fast without).
-- Tier 1 compiles fine and stays compiled.
if jit then
    for _, f in ipairs({ exactSum, exactGroup, groupStep, distinct, prepareGroup, validKeys, sweep2 }) do
        jit.off(f)
    end
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
            for k = 1, P.ksize[v] do
                local x = S.m[v]
                if band(x, BIT[k]) ~= 0 and S.size[v] > 1 then
                    local T = copyState(S, P.nvars)
                    T.m[v], T.size[v] = BIT[k], 1
                    if not fix1(P, T, v) then
                        if not narrow(S, v, x - BIT[k]) then return false, true end
                        changed = true
                        if not fix12(P, S) then return false, true end
                    end
                end
            end
        end
    end
    return true, changed
end

-- Deduces as far as `cap` (1..3) allows. `S`, optional, is a starting state
-- in the public form (fullDomains).
-- Returns status ("solved" | "stuck" | "contradiction"), tier_used, state.
function Solver.solve(P, cap, S)
    S = S and fromPublic(S, P) or fullState(P)
    cap = cap or 3
    local tier = 1
    while true do
        if not fix1(P, S) then return "contradiction", tier, toPublic(S, P) end
        if isSolved(P, S) then return "solved", tier, toPublic(S, P) end
        local progressed = false
        if cap >= 2 then
            local ok, ch = sweep2(P, S)
            if not ok then return "contradiction", math.max(tier, 2), toPublic(S, P) end
            if ch then tier = math.max(tier, 2); progressed = true end
        end
        if not progressed and cap >= 3 then
            local ok, ch = sweep3(P, S)
            if not ok then return "contradiction", 3, toPublic(S, P) end
            if ch then tier = 3; progressed = true end
        end
        if not progressed then return "stuck", tier, toPublic(S, P) end
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
        local x = S.m[best]
        for k = 1, P.ksize[best] do
            if band(x, BIT[k]) ~= 0 then
                local T = copyState(S, P.nvars)
                T.m[best], T.size[best] = BIT[k], 1
                rec(T)
                if found >= limit or exhausted then return end
            end
        end
    end
    rec(fullState(P))
    return found, exhausted
end

return Solver
