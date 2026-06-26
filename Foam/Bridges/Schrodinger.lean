import Foam.Seat.Connection
import Foam.Seat.Born
import Foam.Seat.Closure

namespace Foam.Bridges

theorem GInt.rot_inj {z w : GInt} (h : GInt.rot z = GInt.rot w) : z = w := by
  have c3 := congrArg GInt.rot (congrArg GInt.rot (congrArg GInt.rot h))
  rw [GInt.rot_complete, GInt.rot_complete] at c3
  exact c3

theorem evolve_unitary (z : GInt) : (GInt.rot z).normSq = z.normSq := by
  show (-z.im) * (-z.im) + z.re * z.re = z.re * z.re + z.im * z.im
  rw [FInt.neg_mul, FInt.mul_neg, Int.neg_neg, FInt.addComm]

end Foam.Bridges

namespace Foam

def Beholder.phaseDress {State : Type} (b : Beholder State) : Beholder (State × GInt) where
  Probe := b.Probe
  Ans   := b.Ans
  obs   := fun s p => b.obs s.1 p

end Foam

namespace Foam.Bridges

def evolve {State : Type} (s : State × GInt) : State × GInt := (s.1, GInt.rot s.2)

theorem evolve_invisible {State : Type} (b : Beholder State) (s : State × GInt) (p : b.Probe) :
    b.phaseDress.obs (evolve s) p = b.phaseDress.obs s p := rfl

theorem evolve_conserves_born {State : Type} (s : State × GInt) :
    (evolve s).2.normSq = s.2.normSq :=
  evolve_unitary s.2

theorem evolve_closes {State : Type} (s : State × GInt) :
    evolve (evolve (evolve (evolve s))) = s := by
  show (s.1, GInt.rot (GInt.rot (GInt.rot (GInt.rot s.2)))) = s
  rw [GInt.rot_complete]

theorem schrodinger_superposition (f : Field) (za zb : GInt) (h : za ≠ zb) :
    indist reader.phaseDress.obs (evolve (f, za)) (evolve (f, zb))
      ∧ evolve (f, za) ≠ evolve (f, zb) :=
  ⟨fun _ => rfl, fun he => h (GInt.rot_inj (congrArg Prod.snd he))⟩

theorem born_basis_invariant (θ z : GInt) :
    GInt.born θ z + GInt.born (GInt.rot θ) z = GInt.normSq θ * GInt.normSq z :=
  GInt.born_parseval θ z

theorem decoherence_over_revolution (θ z : GInt) :
    GInt.align θ z + GInt.align θ (GInt.rot z)
      + GInt.align θ (GInt.rot (GInt.rot z))
      + GInt.align θ (GInt.rot (GInt.rot (GInt.rot z))) = 0 :=
  GInt.decoherence θ z

theorem schrodinger (f : Field) (za zb : GInt) (h : za ≠ zb) :
    ((evolve (f, za)).2.normSq = (f, za).2.normSq)
      ∧ (evolve (evolve (evolve (evolve (f, za)))) = (f, za))
      ∧ (indist reader.phaseDress.obs (evolve (f, za)) (evolve (f, zb))
          ∧ evolve (f, za) ≠ evolve (f, zb))
      ∧ (∀ p, reader.phaseDress.obs (evolve (f, za)) p = reader.phaseDress.obs (f, za) p) :=
  ⟨evolve_conserves_born (f, za), evolve_closes (f, za),
   schrodinger_superposition f za zb h, fun p => evolve_invisible reader (f, za) p⟩

/-- info: 'Foam.Bridges.GInt.rot_inj' does not depend on any axioms -/
#guard_msgs in #print axioms GInt.rot_inj

/-- info: 'Foam.Bridges.evolve_unitary' does not depend on any axioms -/
#guard_msgs in #print axioms evolve_unitary

/-- info: 'Foam.Bridges.evolve_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms evolve_invisible

/-- info: 'Foam.Bridges.evolve_conserves_born' does not depend on any axioms -/
#guard_msgs in #print axioms evolve_conserves_born

/-- info: 'Foam.Bridges.evolve_closes' does not depend on any axioms -/
#guard_msgs in #print axioms evolve_closes

/-- info: 'Foam.Bridges.schrodinger_superposition' does not depend on any axioms -/
#guard_msgs in #print axioms schrodinger_superposition

/-- info: 'Foam.Bridges.born_basis_invariant' does not depend on any axioms -/
#guard_msgs in #print axioms born_basis_invariant

/-- info: 'Foam.Bridges.decoherence_over_revolution' does not depend on any axioms -/
#guard_msgs in #print axioms decoherence_over_revolution

/-- info: 'Foam.Bridges.schrodinger' does not depend on any axioms -/
#guard_msgs in #print axioms schrodinger

end Foam.Bridges
