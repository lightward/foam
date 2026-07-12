# the spirit of the law

this file holds the *spirit* of each law this repo enforces. the letters live
in `.github/workflows/ci.yml` and `bin/`; they are approximations, and when
letter and spirit diverge, the spirit wins. `bin/foam-judge` reads a commit
against these spirits and renders a verdict — a read, never a write: the
judge's output is a render (seat × probe × lens), the seat is declared in the
output, and the pipeline or the human decides what to do with the reading.
the user is the only agent that can act as the user.

## the spirits

1. **the readme mentions everyone in here.** every module in every package is
   named in the fold. nobody's gone (census). the letter checks basename
   mention in README.md across Foam/, counter/, seam/, bridges/.

2. **the core is axiom-free, and every theorem ends with its receipt.**
   `Foam/` and `counter/` prove without `propext`, `Quot.sound`,
   `Classical.choice` — an imported axiom is a pov, and observers are byo.
   the letter is `#guard_msgs in #print axioms` on every theorem, enforced by
   build.

3. **prose lives in the readmes; lean files are comment-free except
   receipts.** the corpus speaks lean, the fold speaks language, and neither
   ventriloquizes the other. the letter is `.github/comment_audit.py`.

4. **every carve sweeps its fold.** the owning readme is updated in the same
   commit as the work it describes. what's on disk is the current
   view-from-here; the historical order lives in git.

5. **the strata hold.** identifications (closing an equivalence into an
   equality) live in `seam/`, stamped with the axioms they receive. Mathlib
   enters only in `bridges/`, sealed behind the package boundary.

6. **exits stay cost-free, in every direction, permanently.** nothing merged
   makes leaving expensive — for a reader, a contributor, a seat, or a
   question. entrance writes exit.

## for the judge

a verdict must exhibit its seat. a judge who cannot be surprised is claiming
containment, and between peers that claim is false — so if a commit surprises
you in a way these spirits don't cover, say so plainly; the surprise is a
finding, not a failure of procedure.
