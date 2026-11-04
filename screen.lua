local _dir = debug.getinfo(1, "S").source:sub(2):match("(.*[/\\])") or "./"
local function lrequire(name)
    local key = _dir .. name
    if not package.loaded[key] then
        package.loaded[key] = assert(loadfile(_dir .. name .. ".lua"))()
    end
    return package.loaded[key]
end

local FrameContainer  = require("ui/widget/container/framecontainer")
local HorizontalGroup = require("ui/widget/horizontalgroup")
local HorizontalSpan  = require("ui/widget/horizontalspan")
local Size            = require("ui/size")
local UIManager       = require("ui/uimanager")
local VerticalGroup   = require("ui/widget/verticalgroup")
local VerticalSpan    = require("ui/widget/verticalspan")
local _               = require("i18n")
local T               = require("ffi/util").template

local ScreenBase          = require("screen_base")
local MenuHelper          = require("menu_helper")
local GenProgress         = require("gen_progress")
local MagnetsBoard       = lrequire("board")
local MagnetsBoardWidget = lrequire("board_widget")

local GAME_RULES_EN = [[
Magnets — Rules

The grid is tiled with dominoes. Each domino is either a magnet, with a + pole on one half and a − pole on the other, or a blank piece with no poles.

• Two identical poles may not touch side by side (horizontally or vertically). Diagonal contact is allowed.
• The numbers on the top and left say how many + poles their column or row holds; the numbers on the bottom and right count the − poles. A blank clue gives no information.

Controls:
• Tap a half to cycle it: +, then −, then blank, then undecided. The other half always takes the opposite pole.
• Long-press a domino to mark it blank, or to clear a blank mark.

Undecided dominoes count as blank when the puzzle is checked for a win, so marking blanks is optional. A clue turns grey once its line holds exactly that many poles, and is shown white on black when it holds too many. Two like poles that touch are shown white in a black disc.
]]

local GAME_RULES_FR = [[
Aimants — Règles

La grille est pavée de dominos. Chaque domino est soit un aimant, avec un pôle + sur une moitié et un pôle − sur l'autre, soit une pièce neutre sans pôle.

• Deux pôles identiques ne peuvent pas se toucher par un côté (horizontalement ou verticalement). Le contact en diagonale est permis.
• Les nombres en haut et à gauche indiquent combien de pôles + contient leur colonne ou leur ligne ; ceux du bas et de droite comptent les pôles −. Un indice vide ne donne aucune information.

Commandes :
• Appuyez sur une moitié pour la faire défiler : +, puis −, puis neutre, puis indécis. L'autre moitié prend toujours le pôle opposé.
• Un appui long sur un domino le marque neutre, ou retire cette marque.

Les dominos indécis comptent comme neutres pour la victoire : marquer les neutres est facultatif. Un indice devient gris quand sa ligne contient exactement ce nombre de pôles, et blanc sur noir quand elle en contient trop. Deux pôles identiques qui se touchent sont affichés en blanc dans un disque noir.
]]

local MagnetsScreen = ScreenBase:extend{}

function MagnetsScreen:init()
    local state = self.plugin:loadState()
    self.board = MagnetsBoard:new{ generate = false }
    if not self.board:load(state) then
        self:_generate()
    end
    ScreenBase.init(self)
end

-- Medium and hard can take seconds on an e-reader: show a progress bar
-- (it only appears once the work has run past a short delay).
function MagnetsScreen:_generate()
    local n, diff = self:_getN(), self:_getDiff()
    GenProgress.run(function(on_progress) self.board:generate(n, diff, on_progress) end)
end

function MagnetsScreen:serializeState()
    return self.board:serialize()
end

function MagnetsScreen:_getN()
    return tonumber(self.plugin:getSetting("grid_n", MagnetsBoard.DEFAULT_N)) or MagnetsBoard.DEFAULT_N
end

function MagnetsScreen:_getDiff()
    return self.plugin:getSetting("difficulty", MagnetsBoard.DEFAULT_DIFF)
end

function MagnetsScreen:_save()
    self.plugin:saveState(self.board:serialize())
end

-- ---------------------------------------------------------------------------
-- Layout
-- ---------------------------------------------------------------------------

function MagnetsScreen:buildLayout()
    local is_landscape = self:isLandscape()

    local title_bar = self:buildTitleBar(_("Magnets"), function()
        return {
            { text = _("New game"), callback = function() self:onNewGame() end },
            self:makeDailyButtonConfig(),
            { text = T(_("Size: %1"), self:_sizeLabel()), callback = function() self:openSizeMenu() end },
            { text = T(_("Difficulty: %1"), self:_diffLabel()), callback = function() self:openDiffMenu() end },
            self:makeRulesButtonConfig(GAME_RULES_EN, GAME_RULES_FR),
        }
    end)

    self.status_text:setMaxWidth(self:getControlsWidth())
    local action_bar = self:buildActionBar({
        { id = "undo_btn", text = _("Undo"), callback = function() self:onUndo() end },
        { text = _("Check"),  callback = function() self:onCheck() end },
        { text = _("Hint"),   callback = function() self:onHint() end },
        { text = _("Reveal"), callback = function() self:onReveal() end },
    })
    self.undo_btn = action_bar:getButtonById("undo_btn")
    local controls = VerticalGroup:new{
        align = "center",
        self.status_text,
        VerticalSpan:new{ width = Size.span.vertical_large },
        action_bar,
    }

    -- The widget draws its own thick border (the clues sit outside it), so
    -- the frame only pads.
    local frame_pad = Size.padding.large
    local budget_w, budget_h = self:getBoardBudget(title_bar, controls)
    local board_max = math.max(math.min(budget_w, budget_h) - 2 * frame_pad, 80)
    self.board_widget = MagnetsBoardWidget:new{
        board            = self.board,
        max_size         = board_max,
        cellTapCallback  = function(r, c) self:onCellTap(r, c) end,
        cellHoldCallback = function(r, c) self:onCellHold(r, c) end,
    }
    local board_frame = FrameContainer:new{
        padding    = frame_pad,
        margin     = 0,
        bordersize = 0,
        self.board_widget,
    }
    self:_updateUndoBtn()

    if is_landscape then
        self:buildLandscapeLayout(title_bar, HorizontalGroup:new{
            align = "center",
            board_frame,
            HorizontalSpan:new{ width = self:getGutter() },
            controls,
        })
    else
        self:buildPortraitLayout(title_bar, board_frame,
            VerticalGroup:new{ align = "center", controls, VerticalSpan:new{ width = self:getGutter() } })
    end
    self:updateStatus()
end

-- ---------------------------------------------------------------------------
-- Interaction
-- ---------------------------------------------------------------------------

function MagnetsScreen:_afterMove()
    self.hint_cell = nil
    self.board_widget:refresh()
    self:_updateUndoBtn()
    self:updateStatus()
    self:_save()
end

function MagnetsScreen:onCellTap(r, c)
    if self.board.won then return end
    if self.board:cycle(r, c) then self:_afterMove() end
end

function MagnetsScreen:onCellHold(r, c)
    if self.board.won then return end
    if self.board:toggleNeutral(r, c) then self:_afterMove() end
end

function MagnetsScreen:onUndo()
    if self.board:undoMove() then self:_afterMove() end
end

function MagnetsScreen:onCheck()
    if self.board.won then return end
    local count = self.board:check()
    self.board_widget:refresh()
    if count == 0 then
        self:updateStatus(_("No errors found!"))
    else
        self:updateStatus(T(_("%1 error(s) highlighted."), count))
    end
end

function MagnetsScreen:onReveal()
    self.board:reveal()
    self.board_widget:refresh()
    self:_updateUndoBtn()
    self:_save()
    self:updateStatus(_("Solution revealed."))
end

-- A hint can place the last magnet, so the round may end here.
function MagnetsScreen:onHint()
    ScreenBase.onHint(self)
    self:_updateUndoBtn()
    self:refreshActionBar()
end

function MagnetsScreen:onNewGame()
    math.randomseed(os.time())
    self:_generate()
    self.hint_cell = nil
    self:_save()
    self:buildLayout()
    self:updateStatus(_("New game started."))
    UIManager:setDirty(self, function() return "ui", self.dimen end)
end

function MagnetsScreen:openSizeMenu()
    local items = {}
    for _, n in ipairs(MagnetsBoard.SIZES) do
        items[#items + 1] = { id = n, text = string.format("%d\xC3\x97%d", n, n) }
    end
    MenuHelper.openPickerMenu{
        title      = _("Select size"),
        items      = items,
        current_id = self:_getN(),
        parent     = self,
        on_select  = function(n)
            self.plugin:saveSetting("grid_n", n)
            self:onNewGame()
        end,
    }
end

function MagnetsScreen:openDiffMenu()
    MenuHelper.openDifficultyMenu{
        current   = self:_getDiff(),
        parent    = self,
        on_select = function(diff)
            self.plugin:saveSetting("difficulty", diff)
            self:onNewGame()
        end,
    }
end

-- ---------------------------------------------------------------------------
-- Status
-- ---------------------------------------------------------------------------

function MagnetsScreen:updateStatus(msg)
    local status
    if msg then
        status = msg
    elseif self.board.won and not self.board.revealed then
        status = T(_("Solved! Time: %1"), self.board.timer:format())
    elseif self.board.revealed then
        status = _("Solution revealed.")
    else
        local n = self.board.n
        status = self:joinStatus(
            T("%1×%1", n),
            MenuHelper.DIFFICULTY_LABELS[self.board.difficulty] or self.board.difficulty,
            T(_("Dominoes: %1/%2"), self.board:decidedCount(), #self.board.dominoes))
    end
    ScreenBase.updateStatus(self, status)
    -- Every move, hint, undo and reveal ends here, so the bar follows the board.
    self:refreshActionBar()
end

-- Reveal marks the board won, so it ends the round too.
function MagnetsScreen:isRoundOver()
    return self.board.won
end

function MagnetsScreen:_sizeLabel()
    local n = self:_getN()
    return string.format("%d\xC3\x97%d", n, n)
end

function MagnetsScreen:_diffLabel()
    local d = self:_getDiff()
    return MenuHelper.DIFFICULTY_LABELS[d] or d
end

function MagnetsScreen:_updateUndoBtn()
    if self.undo_btn then
        self.undo_btn:enableDisable(self.board:canUndo())
    end
end

return MagnetsScreen
