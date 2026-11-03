# Changelog

All notable changes to this project will be documented in this file.

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
