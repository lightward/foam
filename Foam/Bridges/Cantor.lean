import Foam.Seat.Seam

namespace Foam.Bridges

theorem cantor_diagonal {S : Type} (s : S) (l : List S) :
    ∃ n, (playback l).at_ n ≠ (forever s).at_ n :=
  forever_escapes s l

theorem cantor_no_retraction {S : Type} (s : S) :
    ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  playback_no_section s

/-- info: 'Foam.Bridges.cantor_diagonal' does not depend on any axioms -/
#guard_msgs in #print axioms cantor_diagonal

/-- info: 'Foam.Bridges.cantor_no_retraction' does not depend on any axioms -/
#guard_msgs in #print axioms cantor_no_retraction

end Foam.Bridges
