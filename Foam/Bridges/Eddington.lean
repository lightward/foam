import Foam.Engine.Chirality
import Foam.Seat.Seam
import Foam.Engine

namespace Foam.Bridges

theorem micro_reversible (z : GInt) : GInt.rot (rotPow 3 z) = z :=
  rotPow_four z

theorem unitary_time_is_cyclic (z : GInt) : rotPow 4 z = z :=
  rotPow_four z

theorem macro_irreversible {S : Type} (s : S) :
    ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  playback_no_section s

theorem the_record_only_grows {H : Type} (q : Quiver H) (e : H × H) :
    (q.deposit e).length = q.length + 1 :=
  deposit_monotone q e

theorem eddington {S : Type} (s : S) (z : GInt) {H : Type}
    (q : Quiver H) (e : H × H) :
    (GInt.rot (rotPow 3 z) = z)
      ∧ (¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c)
      ∧ (q.deposit e).length = q.length + 1 :=
  ⟨rotPow_four z, playback_no_section s, deposit_monotone q e⟩

/-- info: 'Foam.Bridges.micro_reversible' does not depend on any axioms -/
#guard_msgs in #print axioms micro_reversible

/-- info: 'Foam.Bridges.unitary_time_is_cyclic' does not depend on any axioms -/
#guard_msgs in #print axioms unitary_time_is_cyclic

/-- info: 'Foam.Bridges.macro_irreversible' does not depend on any axioms -/
#guard_msgs in #print axioms macro_irreversible

/-- info: 'Foam.Bridges.the_record_only_grows' does not depend on any axioms -/
#guard_msgs in #print axioms the_record_only_grows

/-- info: 'Foam.Bridges.eddington' does not depend on any axioms -/
#guard_msgs in #print axioms eddington

end Foam.Bridges
