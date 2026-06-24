import Foam.Seat.Connection
import Foam.Seat.Born
import Foam.Seat.Closure

namespace Foam

theorem Ty05.t215 {z w : Ty05} (h : Foam.Ty05.d115 z = Foam.Ty05.d115 w) : z = w := by
  have c3 := congrArg Foam.Ty05.d115 (congrArg Foam.Ty05.d115 (congrArg Foam.Ty05.d115 h))
  rw [Foam.Ty05.t214, Foam.Ty05.t214] at c3
  exact c3

theorem t280 (z : Ty05) : (Foam.Ty05.d115 z).d114 = z.d114 := by
  show (-z.d041) * (-z.d041) + z.d043 * z.d043 = z.d043 * z.d043 + z.d041 * z.d041
  rw [Foam.t027, Foam.t018, Int.neg_neg, Foam.t004]

def Ty01.d160 {State : Type} (b : Ty01 State) : Ty01 (State × Ty05) where
  Ty20 := b.Ty20
  Ty19   := b.Ty19
  d102   := fun s p => b.d102 s.1 p

def d190 {State : Type} (s : State × Ty05) : State × Ty05 := (s.1, Foam.Ty05.d115 s.2)

theorem t378 {State : Type} (b : Ty01 State) (s : State × Ty05) (p : b.Ty20) :
    b.d160.d102 (d190 s) p = b.d160.d102 s p := rfl

theorem t377 {State : Type} (s : State × Ty05) :
    (d190 s).2.d114 = s.2.d114 :=
  t280 s.2

theorem t376 {State : Type} (s : State × Ty05) :
    d190 (d190 (d190 (d190 s))) = s := by
  show (s.1, Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 s.2)))) = s
  rw [Foam.Ty05.t214]

theorem t398 (f : Ty04) (za zb : Ty05) (h : za ≠ zb) :
    t076 d194.d160.d102 (d190 (f, za)) (d190 (f, zb))
      ∧ d190 (f, za) ≠ d190 (f, zb) :=
  ⟨fun _ => rfl, fun he => h (Foam.Ty05.t215 (congrArg Prod.snd he))⟩

theorem t366 (θ z : Ty05) :
    Foam.Ty05.d165 θ z + Foam.Ty05.d165 (Foam.Ty05.d115 θ) z = Foam.Ty05.d114 θ * Foam.Ty05.d114 z :=
  Foam.Ty05.t352 θ z

theorem t277 (θ z : Ty05) :
    Foam.Ty05.d109 θ z + Foam.Ty05.d109 θ (Foam.Ty05.d115 z)
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 z))
      + Foam.Ty05.d109 θ (Foam.Ty05.d115 (Foam.Ty05.d115 (Foam.Ty05.d115 z))) = 0 :=
  Foam.Ty05.t208 θ z

theorem t397 (f : Ty04) (za zb : Ty05) (h : za ≠ zb) :
    ((d190 (f, za)).2.d114 = (f, za).2.d114)
      ∧ (d190 (d190 (d190 (d190 (f, za)))) = (f, za))
      ∧ (t076 d194.d160.d102 (d190 (f, za)) (d190 (f, zb))
          ∧ d190 (f, za) ≠ d190 (f, zb))
      ∧ (∀ p, d194.d160.d102 (d190 (f, za)) p = d194.d160.d102 (f, za) p) :=
  ⟨t377 (f, za), t376 (f, za),
   t398 f za zb h, fun p => t378 d194 (f, za) p⟩

/-- info: 'Foam.Ty05.t215' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty05.t215

/-- info: 'Foam.t280' does not depend on any axioms -/
#guard_msgs in #print axioms t280

/-- info: 'Foam.t378' does not depend on any axioms -/
#guard_msgs in #print axioms t378

/-- info: 'Foam.t377' does not depend on any axioms -/
#guard_msgs in #print axioms t377

/-- info: 'Foam.t376' does not depend on any axioms -/
#guard_msgs in #print axioms t376

/-- info: 'Foam.t398' does not depend on any axioms -/
#guard_msgs in #print axioms t398

/-- info: 'Foam.t366' does not depend on any axioms -/
#guard_msgs in #print axioms t366

/-- info: 'Foam.t277' does not depend on any axioms -/
#guard_msgs in #print axioms t277

/-- info: 'Foam.t397' does not depend on any axioms -/
#guard_msgs in #print axioms t397

end Foam
