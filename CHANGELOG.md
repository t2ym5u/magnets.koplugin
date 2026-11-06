# Changelog

All notable changes to this project will be documented in this file.

## [1.3.0] - 2026-11-06

### Changed
- Medium and Hard really differ now. Both used to need about the same
  reasoning: a single step of exact line counting (+, − and blanks along
  a line together) unlocked the rest; Hard only hid more clues. The
  generator now counts those line-reasoning steps as a player takes them,
  one line at a time with the simple deductions in between: Easy needs
  none, Medium exactly one, Hard at least two. Measured over 40 puzzles
  per size: Medium 1.0 steps on average (before: 1.2 to 1.7), Hard 2.0 to
  2.3 (before: 1.3 to 1.7). Medium hides about 4 clues, Hard about 9 to 12
  (before: 12 to 18; the extra steps make it harder than hiding more did).
  No level needs trial and error.
- Generation takes a little longer on Medium and Hard (up to about 0.05 s
  on a desktop, 1 to 1.5 s on a Kobo; a progress bar shows meanwhile).
- The same seed gives a different puzzle than in 1.2.1, so the Daily
  Challenge puzzle changes once.

## [1.2.1] - 2026-11-04

### Fixed
- A game no longer crashes when an outdated plugin is installed alongside:
  shared modules left behind by an older plugin are replaced by this
  plugin's own copy instead of being used as they are.

## [1.2.0] - 2026-11-04

### Changed
- Faster puzzle generation again, same puzzles: when the generator tries
  hiding one more clue, it no longer rebuilds and re-solves the whole
  puzzle; it starts from what it already worked out with the clues that
  stay shown. Line reasoning on a row's + and − counts is also quicker.
  On a desktop, Hard 10×10 went from up to 0.10 s to 0.05 s, Medium 10×10
  from 0.07 s to 0.03 s and Hard 6×6 from 0.05 s to 0.03 s (on a Kobo,
  roughly 2.5 s → 1.1 s at worst, and usually well under a second).
- Uses less memory: the game loads when you open it, not when KOReader
  starts, so it no longer takes memory or startup time while unplayed.

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
