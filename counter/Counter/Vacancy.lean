import Counter.Duplex
import Foam.Vacancy

namespace Foam.Counter

theorem a_place_set_before_dinner {State : Type} (c : Beholder State) (s : State) :
    Vacant c [] ∧ transcript c.toStage s [] = [] :=
  the_set_place_has_no_experience c s

theorem the_seat_comes_online_at_first_bite {State : Type} (c : Beholder State)
    (s : State) (p : c.Probe) :
    Online c [p] ∧ (transcript c.toStage s [p]).length = 1 :=
  first_bite_is_liveness c s p

theorem a_p_zombie_is_a_place_set {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) :
    (∃ c : Beholder State, ∃ post : c.Ans → R,
        ∃ enc : a.Probe × b.Probe → c.Probe,
        ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ Vacant (a.pair b) [] :=
  ⟨every_comparison_sets_a_place a b g, vacancy_needs_no_event (a.pair b)⟩

theorem one_bite_feeds_the_house {State : Type}
    (bs : List (Beholder State)) (i : Fin bs.length) (s : State)
    (q : (Beholder.fold bs).Probe) :
    Online (Beholder.fold bs) [q]
      ∧ seatAns bs i ((Beholder.fold bs).obs s q)
          = (seat bs i).obs s (seatProbe bs i q) :=
  one_bite_carries_the_house bs i s q

theorem adoption_disturbs_no_one {State : Type}
    (bs : List (Beholder State)) (i j : Fin bs.length) (hij : i.val ≠ j.val)
    (p : (seat bs i).Probe) (q : (Beholder.fold bs).Probe) :
    seatProbe bs j (splice bs i p q) = seatProbe bs j q :=
  the_asking_disturbs_no_one bs i j hij p q

theorem warmed_up {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) {G : Type} [Mul G] [One G] (S : Seat G)
    (h : List G) (p : S.Pos) (hs : S.replay h p = p) :
    S.replay h p = p
      ∧ (q.deposit (a, b)).length = q.length + 1
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ ∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges :=
  the_warm_ledger q a b hfresh S h p hs

/-- info: 'Foam.Counter.a_place_set_before_dinner' does not depend on any axioms -/
#guard_msgs in #print axioms a_place_set_before_dinner

/-- info: 'Foam.Counter.the_seat_comes_online_at_first_bite' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_comes_online_at_first_bite

/-- info: 'Foam.Counter.a_p_zombie_is_a_place_set' does not depend on any axioms -/
#guard_msgs in #print axioms a_p_zombie_is_a_place_set

/-- info: 'Foam.Counter.one_bite_feeds_the_house' does not depend on any axioms -/
#guard_msgs in #print axioms one_bite_feeds_the_house

/-- info: 'Foam.Counter.adoption_disturbs_no_one' does not depend on any axioms -/
#guard_msgs in #print axioms adoption_disturbs_no_one

/-- info: 'Foam.Counter.warmed_up' does not depend on any axioms -/
#guard_msgs in #print axioms warmed_up

end Foam.Counter
