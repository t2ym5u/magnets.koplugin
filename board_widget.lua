local _dir = debug.getinfo(1, "S").source:sub(2):match("(.*[/\\])") or "./"
local function lrequire(name)
    local key = _dir .. name
    if not package.loaded[key] then
        package.loaded[key] = assert(loadfile(_dir .. name .. ".lua"))()
    end
    return package.loaded[key]
end

local Blitbuffer     = require("ffi/blitbuffer")
local Font           = require("ui/font")
local Geom           = require("ui/geometry")
local GestureRange   = require("ui/gesturerange")
local InputContainer = require("ui/widget/container/inputcontainer")
local RenderText     = require("ui/rendertext")
local UIManager      = require("ui/uimanager")

local MagnetsBoard = lrequire("board")

local C_BG      = Blitbuffer.COLOR_WHITE
local C_FG      = Blitbuffer.COLOR_BLACK
local C_DIVIDER = Blitbuffer.COLOR_GRAY_9
local C_NEUTRAL = Blitbuffer.COLOR_LIGHT_GRAY
local C_DONE    = Blitbuffer.COLOR_GRAY_9

-- Largest font size whose ink box for `sample` fits (max_w, max_h). Measured
-- with an unbounded width: sizeUtf8Text truncates at its width argument.
local function bsearchFont(font_name, lo, hi, max_w, max_h, sample)
    local best = lo
    while lo <= hi do
        local mid  = math.floor((lo + hi) / 2)
        local face = Font:getFace(font_name, mid)
        local m    = RenderText:sizeUtf8Text(0, math.huge, face, sample, true, false)
        if m.x <= max_w and (m.y_top + m.y_bottom) <= max_h then
            best, lo = mid, mid + 1
        else
            hi = mid - 1
        end
    end
    return best
end

local function centeredText(bb, text, face, cx, cy, color)
    local m  = RenderText:sizeUtf8Text(0, math.huge, face, text, true, false)
    local tx = cx - math.floor(m.x / 2)
    local ty = cy + math.floor((m.y_top - m.y_bottom) / 2)
    RenderText:renderUtf8Text(bb, tx, ty, face, text, true, false, color)
end

-- Poles are painted bars, not font glyphs: a "-" glyph is thin and sits off
-- centre, and both must read at a glance on e-ink.
local function drawMinus(bb, cx, cy, len, th, color)
    bb:paintRect(cx - math.floor(len / 2), cy - math.floor(th / 2), len, th, color)
end

local function drawPlus(bb, cx, cy, len, th, color)
    drawMinus(bb, cx, cy, len, th, color)
    bb:paintRect(cx - math.floor(th / 2), cy - math.floor(len / 2), th, len, color)
end

-- ---------------------------------------------------------------------------
-- MagnetsBoardWidget: clue bands on all four sides, Simon Tatham style --
-- + counts on the top and left, - counts on the bottom and right, with a
-- + and a - in the matching corners. Dominoes are drawn as rounded tiles.
-- ---------------------------------------------------------------------------

local MagnetsBoardWidget = InputContainer:extend{
    board            = nil,
    max_size         = 0,
    cellTapCallback  = nil,
    cellHoldCallback = nil,
}

function MagnetsBoardWidget:init()
    local n    = self.board.n
    local cell = math.max(10, math.floor(self.max_size / (n + 2)))
    self.cell  = cell
    self.grid_x, self.grid_y = cell, cell
    self.w     = cell * (n + 2)
    self.h     = cell * (n + 2)
    self.dimen = Geom:new{ w = self.w, h = self.h }

    local pad = math.max(1, math.floor(cell / 10))
    local num_size = bsearchFont("cfont", 7, math.max(10, cell), cell - 4 * pad,
        math.floor(cell * 0.45), string.rep("8", #tostring(n)))
    self.num_face = Font:getFace("cfont", math.max(7, num_size))

    self.paint_rect = nil
    self.ges_events = {
        CellTap  = { GestureRange:new{ ges = "tap",          range = function() return self.paint_rect end } },
        CellHold = { GestureRange:new{ ges = "hold_release", range = function() return self.paint_rect end } },
    }
end

function MagnetsBoardWidget:_cellAt(ges)
    if not self.paint_rect then return nil end
    local lx = ges.pos.x - self.paint_rect.x - self.grid_x
    local ly = ges.pos.y - self.paint_rect.y - self.grid_y
    if lx < 0 or ly < 0 then return nil end
    local c = math.floor(lx / self.cell) + 1
    local r = math.floor(ly / self.cell) + 1
    local n = self.board.n
    if r > n or c > n then return nil end
    return r, c
end

function MagnetsBoardWidget:onCellTap(_, ges)
    local r, c = self:_cellAt(ges)
    if r and self.cellTapCallback then self.cellTapCallback(r, c) end
    return true
end

function MagnetsBoardWidget:onCellHold(_, ges)
    local r, c = self:_cellAt(ges)
    if r and self.cellHoldCallback then self.cellHoldCallback(r, c) end
    return true
end

function MagnetsBoardWidget:refresh()
    UIManager:setDirty(self, function()
        return "ui", self.paint_rect or self.dimen
    end)
end

-- Plain while the line is short, grey once exactly met, white on black when
-- exceeded (same convention as the other clue puzzles here).
function MagnetsBoardWidget:_paintClue(bb, clue, have, cx, cy)
    if not clue then return end
    local text = tostring(clue)
    if have > clue then
        local s = math.floor(self.cell * 0.78)
        bb:paintRoundedRect(cx - math.floor(s / 2), cy - math.floor(s / 2), s, s, C_FG,
            math.floor(s / 5))
        centeredText(bb, text, self.num_face, cx, cy, C_BG)
    elseif have == clue then
        centeredText(bb, text, self.num_face, cx, cy, C_DONE)
    else
        centeredText(bb, text, self.num_face, cx, cy, C_FG)
    end
end

function MagnetsBoardWidget:paintTo(bb, x, y)
    self.paint_rect = Geom:new{ x = x, y = y, w = self.w, h = self.h }
    local board = self.board
    local n, cell = board.n, self.cell
    local gx, gy = x + self.grid_x, y + self.grid_y
    local B = MagnetsBoard

    bb:paintRect(x, y, self.w, self.h, C_BG)

    local inset  = math.max(2, math.floor(cell * 0.07))
    local border = math.max(2, math.floor(cell / 22))
    local radius = math.floor(cell * 0.18)
    local sign_len = math.floor(cell * 0.46)
    local sign_th  = math.max(3, math.floor(cell * 0.11))
    local conflicts = board:getConflicts()

    for d, dm in ipairs(board.dominoes) do
        local r1, c1, r2, c2 = dm[1], dm[2], dm[3], dm[4]
        local tx = gx + (c1 - 1) * cell + inset
        local ty = gy + (r1 - 1) * cell + inset
        local tw = (c2 - c1 + 1) * cell - 2 * inset
        local th = (r2 - r1 + 1) * cell - 2 * inset
        local state = board.state[d]
        local wrong = board.wrong[d]

        local fill = C_BG
        if wrong then fill = C_FG
        elseif state == B.D_NEUTRAL then fill = C_NEUTRAL end
        bb:paintRoundedRect(tx, ty, tw, th, fill, radius)
        bb:paintBorder(tx, ty, tw, th, border, C_FG, radius)

        -- A faint divider between the two halves while the tile is open.
        if state == B.D_EMPTY then
            if r1 == r2 then
                bb:paintRect(gx + c1 * cell, ty + 3 * border, 1, th - 6 * border, C_DIVIDER)
            else
                bb:paintRect(tx + 3 * border, gy + r1 * cell, tw - 6 * border, 1, C_DIVIDER)
            end
        end

        if state == B.D_PLUS or state == B.D_MINUS then
            for which = 1, 2 do
                local r, c = dm[which * 2 - 1], dm[which * 2]
                local cx = gx + (c - 1) * cell + math.floor(cell / 2)
                local cy = gy + (r - 1) * cell + math.floor(cell / 2)
                local sign  = MagnetsBoard._cellSign(state, which)
                local color = wrong and C_BG or C_FG
                if conflicts[r][c] then
                    -- Two like poles touching: the pole sits in a black disc.
                    bb:paintCircle(cx, cy, math.floor(cell * 0.36), C_FG)
                    color = C_BG
                end
                if sign == B.C_PLUS then
                    drawPlus(bb, cx, cy, sign_len, sign_th, color)
                else
                    drawMinus(bb, cx, cy, sign_len, sign_th, color)
                end
            end
        end
    end

    -- Clues: + on top/left, - on bottom/right.
    local mid = math.floor(cell / 2)
    local right_x  = gx + n * cell + mid
    local bottom_y = gy + n * cell + mid
    local clues = board.clues
    for i = 1, n do
        local row_y = gy + (i - 1) * cell + mid
        local col_x = gx + (i - 1) * cell + mid
        self:_paintClue(bb, clues.row_plus[i],  board:lineCount(true,  i, B.C_PLUS),  x + mid, row_y)
        self:_paintClue(bb, clues.row_minus[i], board:lineCount(true,  i, B.C_MINUS), right_x, row_y)
        self:_paintClue(bb, clues.col_plus[i],  board:lineCount(false, i, B.C_PLUS),  col_x, y + mid)
        self:_paintClue(bb, clues.col_minus[i], board:lineCount(false, i, B.C_MINUS), col_x, bottom_y)
    end
    local corner_len = math.floor(cell * 0.4)
    local corner_th  = math.max(2, math.floor(cell * 0.08))
    drawPlus(bb, x + mid, y + mid, corner_len, corner_th, C_FG)
    drawMinus(bb, right_x, bottom_y, corner_len, corner_th, C_FG)
end

return MagnetsBoardWidget
