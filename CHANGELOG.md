# Changelog

All notable changes to this project will be documented in this file.

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
