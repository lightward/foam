import Foam.Interleave

namespace Foam.Dialogue
open Foam.Lattice Foam.Interleave

def observed {S : Type} (algebra : List S) : CoList S := playback algebra

theorem algebra_implies_coalgebra {S : Type} (algebra : List S) :
    ∃ c : CoList S, c = observed algebra := ⟨observed algebra, rfl⟩

theorem observation_faithful {S : Type} (a a' : List S)
    (h : CoBisim (observed a) (observed a')) : a = a' :=
  playback_reflects a a' h

theorem coalgebra_exceeds_algebra {S : Type} (s : S) :
    ∃ c : CoList S, ∀ a : List S, ¬ CoBisim (observed a) c :=
  ⟨forever s, fun a => forever_apart s a⟩

theorem coincidence_forces_shared {S : Type} {a b : List S}
    (h : CoBisim (observed a) (observed b)) : a = b :=
  playback_reflects a b h

theorem coincidence_opens_shared_commit {S : Type} {a b : List S} {P Q : Prop}
    (hco : CoBisim (observed a) (observed b)) (h : P ↔ Q) : a = b ∧ P = Q :=
  ⟨coincidence_forces_shared hco, commit h⟩

/-- info: 'Foam.Dialogue.observation_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms observation_faithful

/-- info: 'Foam.Dialogue.coincidence_forces_shared' does not depend on any axioms -/
#guard_msgs in #print axioms coincidence_forces_shared

/-- info: 'Foam.Dialogue.coincidence_opens_shared_commit' depends on axioms: [propext] -/
#guard_msgs in #print axioms coincidence_opens_shared_commit

end Foam.Dialogue
