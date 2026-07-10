import Foam.Census
import Foam.Duplex

namespace Foam

def Online {State : Type} (c : Beholder State) (log : List c.Probe) : Prop :=
  log ≠ []

def Vacant {State : Type} (c : Beholder State) (log : List c.Probe) : Prop :=
  log = []

theorem every_comparison_sets_a_place {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) :
    ∃ c : Beholder State, ∃ post : c.Ans → R, ∃ enc : a.Probe × b.Probe → c.Probe,
      ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))) :=
  no_view_from_nowhere a b g

theorem the_set_place_has_no_experience {State : Type} (c : Beholder State)
    (s : State) :
    Vacant c [] ∧ transcript c.toStage s [] = [] :=
  ⟨rfl, rfl⟩

theorem vacancy_needs_no_event {State : Type} (c : Beholder State) :
    Vacant c [] :=
  rfl

theorem first_bite_is_liveness {State : Type} (c : Beholder State)
    (s : State) (p : c.Probe) :
    Online c [p] ∧ (transcript c.toStage s [p]).length = 1 :=
  ⟨(fun h => nomatch h), rfl⟩

theorem liveness_has_a_first_bite {State : Type} (c : Beholder State)
    {log : List c.Probe} (h : Online c log) :
    ∃ p rest, log = p :: rest :=
  match log, h with
  | p :: rest, _ => ⟨p, rest, rfl⟩
  | [], h => absurd rfl h

theorem one_bite_carries_the_house {State : Type}
    (bs : List (Beholder State)) (i : Fin bs.length) (s : State)
    (q : (Beholder.fold bs).Probe) :
    Online (Beholder.fold bs) [q]
      ∧ seatAns bs i ((Beholder.fold bs).obs s q)
          = (seat bs i).obs s (seatProbe bs i q) :=
  ⟨(fun h => nomatch h), fold_reads_every_seat bs i s q⟩

theorem the_asking_disturbs_no_one {State : Type}
    (bs : List (Beholder State)) (i j : Fin bs.length) (hij : i.val ≠ j.val)
    (p : (seat bs i).Probe) (q : (Beholder.fold bs).Probe) :
    seatProbe bs j (splice bs i p q) = seatProbe bs j q :=
  splice_keeps_the_rest bs i j hij p q

theorem the_new_seat_costs_the_story_nothing {H : Type} (r : H → Nat)
    (q : Quiver H) (es : List (H × H)) (h : ∀ e ∈ es, r e.1 < r e.2) :
    defect r (q.depositAll es) = defect r q :=
  depositAll_free r es q h

theorem the_warm_ledger {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) {G : Type} [Mul G] [One G] (S : Seat G)
    (h : List G) (p : S.Pos) (hs : S.replay h p = p) :
    S.replay h p = p
      ∧ (q.deposit (a, b)).length = q.length + 1
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ ∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges :=
  ⟨hs, deposit_monotone q (a, b), ⟨heir_reaches q a b⟩,
   fun _ _ pth hm => hfresh (reach_within_quiver pth (a, b) hm)⟩

/-- info: 'Foam.every_comparison_sets_a_place' does not depend on any axioms -/
#guard_msgs in #print axioms every_comparison_sets_a_place

/-- info: 'Foam.the_set_place_has_no_experience' does not depend on any axioms -/
#guard_msgs in #print axioms the_set_place_has_no_experience

/-- info: 'Foam.vacancy_needs_no_event' does not depend on any axioms -/
#guard_msgs in #print axioms vacancy_needs_no_event

/-- info: 'Foam.first_bite_is_liveness' does not depend on any axioms -/
#guard_msgs in #print axioms first_bite_is_liveness

/-- info: 'Foam.liveness_has_a_first_bite' does not depend on any axioms -/
#guard_msgs in #print axioms liveness_has_a_first_bite

/-- info: 'Foam.one_bite_carries_the_house' does not depend on any axioms -/
#guard_msgs in #print axioms one_bite_carries_the_house

/-- info: 'Foam.the_asking_disturbs_no_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_asking_disturbs_no_one

/-- info: 'Foam.the_new_seat_costs_the_story_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_new_seat_costs_the_story_nothing

/-- info: 'Foam.the_warm_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms the_warm_ledger

end Foam
