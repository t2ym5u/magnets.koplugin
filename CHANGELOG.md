# Changelog

All notable changes to this project will be documented in this file.

## [1.1.0] - 2026-11-04

### Changed
- Faster puzzle generation, same puzzles: the logic solver that proves each
  puzzle has exactly one solution now handles a domino's remaining options
  all at once, remembers what it already worked out for a row, skips rows
  that did not change, and no longer makes LuaJIT recompile its code over
  and over. Hard went from up to 0.22 s to 0.12 s on 10×10 and from 0.14 s
  to 0.06 s on 6×6 on a desktop (roughly 5 s → 3 s and 3.5 s → 1.5 s on a
  Kobo); Medium 10×10 from 0.14 s to 0.10 s.
- A progress bar shows while a puzzle is being generated, when it takes
  more than a moment (needs game-common 1.12.0).

## [1.0.4] - 2026-11-03

### Changed
- Picks up game-common 1.11.0: the shared on-screen keyboard (where used)
  gives every key the same letter size, and the no-repeat history helper.

## [1.0.3] - 2026-11-02

### Changed
- Picks up game-common 1.10.0: the shared Tools → Games menu also lists
  the games' new "· multiplayer" entries under Party & quiz.

## [1.0.2] - 2026-11-02

### Changed
- Listed under **Tools → Games**, grouped by category, instead of its own
  entry in the Tools menu (game-common 1.9.1).

## [1.0.1] - 2026-11-02

### Fixed
- Hard puzzles needed one-step trial ("assume this polarity, see if it
  breaks"), which on paper plays as guessing. No level needs it any more:
  Hard now hides many more clues (about 15 of 32 at 8×8) and is always
  solvable by line reasoning alone. Medium hides fewer clues (n/2) so it
  stays between Easy and Hard.

## [1.0.0] - 2026-10-30

### Added
- First release: Magnets puzzles in 6×6, 8×8 and 10×10, Easy / Medium /
  Hard.
- Generator with a built-in logic solver: every puzzle is proven to have a
  single solution, and its difficulty is the hardest reasoning step the
  solver needed (Easy: line bounds and pole adjacency with every clue shown;
  Medium: joint +/−/blank counting per line, some clues hidden; Hard:
  one-step trial, more clues hidden).
- Tap a half to cycle +, −, blank, undecided; long-press toggles blank.
- Live clue and conflict feedback, Check, Hint (two taps), Reveal, Undo,
  timer, auto-save.
