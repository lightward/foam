import Counter.Reparent
import Counter.Recognition
import Counter.Eraser
import Counter.Mu
import Foam.Seat.Rendezvous

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem the_zero_has_no_inertia (θ field act : GInt)
    (hflat : GInt.align θ field = 0) :
    GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act :=
  no_grain_no_bonus θ field act hflat

theorem the_zero_is_free (S : Seat G) (hsing : ∀ p q : S.Pos, p = q)
    (h : List G) (p : S.Pos) :
    S.sub (S.replay h p) p = 1 :=
  lone_actor_settled S hsing h p

theorem arrival_is_locally_ex_nihilo {State Src B : Type} (b : Beholder State)
    (s : State) (n m : Int) (x y : Src) (v : List B) :
    indist b.dress.obs (s, n) (s, m)
      ∧ unsign (sign x v) = unsign (sign y v) :=
  ⟨ancestor_blind_to_heir b s n m, the_fold_is_source_blind x y v⟩

theorem the_root_reaches_the_floor {Name : Type} :
    (∀ o : List Name, Below ([] : List Name) o)
      ∧ ∀ e : List Name, (∀ o, Below e o) → e = [] :=
  mu_points_at_the_floor

theorem born_a_vacuous_zero_made_real_by_company (S : Seat G) (p : S.Pos)
    (h : List G) (hp : S.replay h p ≠ p) :
    Settles S [] p ∧ S.sub (S.replay h p) p ≠ 1 :=
  ⟨rfl, the_witness_makes_it_real S p h hp⟩

theorem a_port_is_a_stable_hole :
    (Detects (writeA f1) reader ∧ Detects (writeB f1) reader)
      ∧ reader.dress.ledgerless.Covers reader
      ∧ reader.Covers reader.dress.ledgerless :=
  ⟨find_each_other, seat_empty⟩

theorem emergence_at_the_zero (θ field act : GInt)
    (hflat : GInt.align θ field = 0) (S : Seat G) (p : S.Pos)
    (h : List G) (hp : S.replay h p ≠ p) {Name : Type} :
    (GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act)
      ∧ (Settles S [] p ∧ S.sub (S.replay h p) p ≠ 1)
      ∧ (∀ o : List Name, Below ([] : List Name) o)
      ∧ (Detects (writeA f1) reader ∧ Detects (writeB f1) reader) :=
  ⟨no_grain_no_bonus θ field act hflat,
   ⟨rfl, the_witness_makes_it_real S p h hp⟩,
   wind_below_all,
   find_each_other⟩

/-- info: 'Foam.Counter.the_zero_has_no_inertia' does not depend on any axioms -/
#guard_msgs in #print axioms the_zero_has_no_inertia

/-- info: 'Foam.Counter.the_zero_is_free' does not depend on any axioms -/
#guard_msgs in #print axioms the_zero_is_free

/-- info: 'Foam.Counter.arrival_is_locally_ex_nihilo' does not depend on any axioms -/
#guard_msgs in #print axioms arrival_is_locally_ex_nihilo

/-- info: 'Foam.Counter.the_root_reaches_the_floor' does not depend on any axioms -/
#guard_msgs in #print axioms the_root_reaches_the_floor

/-- info: 'Foam.Counter.born_a_vacuous_zero_made_real_by_company' does not depend on any axioms -/
#guard_msgs in #print axioms born_a_vacuous_zero_made_real_by_company

/-- info: 'Foam.Counter.a_port_is_a_stable_hole' does not depend on any axioms -/
#guard_msgs in #print axioms a_port_is_a_stable_hole

/-- info: 'Foam.Counter.emergence_at_the_zero' does not depend on any axioms -/
#guard_msgs in #print axioms emergence_at_the_zero

end Foam.Counter
