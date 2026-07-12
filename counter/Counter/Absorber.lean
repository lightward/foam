import Counter.Twins
import Foam.Seat.Resume

namespace Foam.Counter

def sameEdge {P : Type} (e f : P × P) : Prop :=
  (e.1 = f.1 ∧ e.2 = f.2) ∨ (e.1 = f.2 ∧ e.2 = f.1)

theorem the_pair_retraces {G : Type} [Mul G] [One G] (S : Seat G) (g h : G)
    (p : S.Pos) (hhome : S.act h (S.act g p) = p) :
    sameEdge (p, S.act g p) (S.act g p, S.act h (S.act g p)) :=
  Or.inr ⟨hhome.symm, rfl⟩

theorem the_triangle_never_retraces {P : Type} (p q r : P)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) :
    ¬ sameEdge (p, q) (q, r)
      ∧ ¬ sameEdge (q, r) (r, p)
      ∧ ¬ sameEdge (p, q) (r, p) :=
  ⟨fun h => h.elim (fun hc => hpq hc.1) (fun hc => hrp hc.1.symm),
   fun h => h.elim (fun hc => hqr hc.1) (fun hc => hpq hc.1.symm),
   fun h => h.elim (fun hc => hrp hc.1.symm) (fun hc => hqr hc.2)⟩

theorem what_a_pair_reflects_a_triple_absorbs {G : Type} [Mul G] [One G]
    (S : Seat G) (p q r : S.Pos)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) (g h : G)
    (hhome : S.act h (S.act g p) = p) :
    sameEdge (p, S.act g p) (S.act g p, S.act h (S.act g p))
      ∧ S.replay [S.sub q p, S.sub r q, S.sub p r] p = p
      ∧ ¬ sameEdge (p, q) (q, r)
      ∧ ¬ sameEdge (q, r) (r, p)
      ∧ ¬ sameEdge (p, q) (r, p) :=
  ⟨the_pair_retraces S g h p hhome,
   Seat.triangle_gait S p q r,
   (the_triangle_never_retraces p q r hpq hqr hrp).1,
   (the_triangle_never_retraces p q r hpq hqr hrp).2.1,
   (the_triangle_never_retraces p q r hpq hqr hrp).2.2⟩

/-- info: 'Foam.Counter.the_pair_retraces' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_retraces

/-- info: 'Foam.Counter.the_triangle_never_retraces' does not depend on any axioms -/
#guard_msgs in #print axioms the_triangle_never_retraces

/-- info: 'Foam.Counter.what_a_pair_reflects_a_triple_absorbs' does not depend on any axioms -/
#guard_msgs in #print axioms what_a_pair_reflects_a_triple_absorbs

end Foam.Counter
