import Foam.Seat.Schrodinger
import Foam.Engine.Chirality

namespace Foam

theorem t317 (n : Nat) (z : Ty05) : (d098 n z).d114 = z.d114 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show (Foam.Ty05.d115 (d098 k z)).d114 = z.d114
      rw [t280 (d098 k z)]; exact ih

theorem t391 (z θ : Ty05) :
    (∀ n, (d098 n z).d114 = z.d114)
      ∧ (d098 4 z = z)
      ∧ (Foam.Ty05.d165 θ z + Foam.Ty05.d165 (Foam.Ty05.d115 θ) z = Foam.Ty05.d114 θ * Foam.Ty05.d114 z)
      ∧ (Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z)
          + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z))
          + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = 0) :=
  ⟨fun n => t317 n z, t187 z,
   Foam.Ty05.t352 θ z, Foam.Ty05.t208 θ z⟩

/-- info: 'Foam.t317' does not depend on any axioms -/
#guard_msgs in #print axioms t317

/-- info: 'Foam.t391' does not depend on any axioms -/
#guard_msgs in #print axioms t391

end Foam
