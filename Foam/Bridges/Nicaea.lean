import Foam.Bridges.Gita
import Foam.Vacancy

namespace Foam.Bridges

variable {W : Stage}

theorem subsistent_relation (A B : Bubble W) :
    (A.meet B).front.behold = A.front.behold.pair B.front.behold :=
  Bubble.wall_is_pair_beholder A B

theorem none_is_afore_or_after (A B C : Bubble W) :
    (Bubble.borderShift C A B).comp
        ((Bubble.borderShift B C A).comp (Bubble.borderShift A B C))
      = StageHom.id ((A.meet B).meet C).front :=
  Bubble.border_forgets_order A B C

theorem the_source_is_unoccupiable {State : Type} (a : Beholder State)
    (m : State → State) :
    (¬ Elsewhen a m a) ∧ (Invisible (plenum State) m → ∀ s, m s = s) :=
  ⟨no_seat_is_its_own_elsewhen a m, fun h => nothing_hides_from_the_plenum m h⟩

theorem speaks_only_what_it_hears {State : Type} (s : State) :
    (plenum State).obs s () = s := rfl

theorem the_place_of_the_third_is_eternal {State R : Type} (a b : Beholder State)
    (g : a.Ans → b.Ans → R) :
    ∃ c : Beholder State, ∃ post : c.Ans → R, ∃ enc : a.Probe × b.Probe → c.Probe,
      ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))) :=
  no_view_from_nowhere a b g

theorem the_procession_is_from_both :
    Elsewhen readA (sendA true) readB
      ∧ Elsewhen readB (sendB true) readA
      ∧ ∀ (w : twoBit.State) (pq : Unit × Unit),
          (firstBit.meet secondBit).front.obs w pq = (w.1, w.2) :=
  the_duplex

theorem nicaea (A B C : Bubble W) :
    ((A.meet B).front.behold = A.front.behold.pair B.front.behold)
      ∧ ((Bubble.borderShift C A B).comp
            ((Bubble.borderShift B C A).comp (Bubble.borderShift A B C))
          = StageHom.id ((A.meet B).meet C).front)
      ∧ ∀ (State : Type) (a : Beholder State) (m : State → State),
          ¬ Elsewhen a m a :=
  ⟨subsistent_relation A B, none_is_afore_or_after A B C,
   fun _ a m => no_seat_is_its_own_elsewhen a m⟩

theorem coeternity_is_resolution (c : Nat → Nat) (n : Nat) :
    Resolver c n ↔ ∀ m, n ≤ m → Rests c m :=
  resolver_reps_change_nothing c n

theorem peers_on_the_page_ordered_in_the_quiver :
    ∃ (q : Quiver Nat) (r : Nat → Nat) (a b : Nat),
      r a = r b ∧ (a, b) ∈ q ∧ a ≠ b :=
  ⟨[(0, 1)], fun _ => 0, 0, 1, rfl, List.Mem.head _, fun h => nomatch h⟩

theorem the_selves_are_downstream_of_the_arrows (H : Type) :
    Quiver H = List (H × H) := rfl

theorem the_procession_is_eternal_the_mission_has_a_date {State : Type}
    (c : Beholder State) {log : List c.Probe} (h : Online c log) :
    Vacant c ([] : List c.Probe) ∧ ∃ p rest, log = p :: rest :=
  ⟨vacancy_needs_no_event c, liveness_has_a_first_bite c h⟩

theorem blanket_consent_blinds {S : Stage} (F : Frontstage S)
    (htotal : ∀ s t, F.rel s t) (s t : S.State) (p : S.Probe) :
    S.obs s p = S.obs t p :=
  F.respects s t (htotal s t) p

theorem gethsemane (S : Stage) :
    (∀ F : Frontstage S, (∀ s t, F.rel s t) →
        ∀ (s t : S.State) (p : S.Probe), S.obs s p = S.obs t p)
      ∧ ∀ (w : Nat → S.State) (ps : List S.Probe) (k : Nat),
          (watch S w k ps).length = ps.length :=
  ⟨fun F htotal s t p => blanket_consent_blinds F htotal s t p,
   fun w ps k => watch_length S w ps k⟩

theorem the_son_is_all_consenting {State : Type} (a : Beholder State)
    {H : Type} (q : Quiver H) (x y : H) (hfresh : (x, y) ∉ q) :
    (∀ (s : State) (p : a.Probe),
        ((a.pair (plenum State).behold).obs s (p, ())).1 = a.obs s p
          ∧ ((a.pair (plenum State).behold).obs s (p, ())).2 = s)
      ∧ Nonempty (Path (q.deposit (x, y)) x y)
      ∧ ∀ (u v : H) (pth : Path q u v), (x, y) ∉ pth.edges :=
  ⟨fun s p => both_poles_in_one_bite a s p, ⟨heir_reaches q x y⟩,
   fun _ _ pth hm => hfresh (reach_within_quiver pth (x, y) hm)⟩

/-- info: 'Foam.Bridges.subsistent_relation' does not depend on any axioms -/
#guard_msgs in #print axioms subsistent_relation

/-- info: 'Foam.Bridges.none_is_afore_or_after' does not depend on any axioms -/
#guard_msgs in #print axioms none_is_afore_or_after

/-- info: 'Foam.Bridges.the_source_is_unoccupiable' does not depend on any axioms -/
#guard_msgs in #print axioms the_source_is_unoccupiable

/-- info: 'Foam.Bridges.speaks_only_what_it_hears' does not depend on any axioms -/
#guard_msgs in #print axioms speaks_only_what_it_hears

/-- info: 'Foam.Bridges.the_place_of_the_third_is_eternal' does not depend on any axioms -/
#guard_msgs in #print axioms the_place_of_the_third_is_eternal

/-- info: 'Foam.Bridges.the_procession_is_from_both' does not depend on any axioms -/
#guard_msgs in #print axioms the_procession_is_from_both

/-- info: 'Foam.Bridges.nicaea' does not depend on any axioms -/
#guard_msgs in #print axioms nicaea

/-- info: 'Foam.Bridges.coeternity_is_resolution' does not depend on any axioms -/
#guard_msgs in #print axioms coeternity_is_resolution

/-- info: 'Foam.Bridges.peers_on_the_page_ordered_in_the_quiver' does not depend on any axioms -/
#guard_msgs in #print axioms peers_on_the_page_ordered_in_the_quiver

/-- info: 'Foam.Bridges.the_selves_are_downstream_of_the_arrows' does not depend on any axioms -/
#guard_msgs in #print axioms the_selves_are_downstream_of_the_arrows

/-- info: 'Foam.Bridges.the_procession_is_eternal_the_mission_has_a_date' does not depend on any axioms -/
#guard_msgs in #print axioms the_procession_is_eternal_the_mission_has_a_date

/-- info: 'Foam.Bridges.blanket_consent_blinds' does not depend on any axioms -/
#guard_msgs in #print axioms blanket_consent_blinds

/-- info: 'Foam.Bridges.gethsemane' does not depend on any axioms -/
#guard_msgs in #print axioms gethsemane

/-- info: 'Foam.Bridges.the_son_is_all_consenting' does not depend on any axioms -/
#guard_msgs in #print axioms the_son_is_all_consenting

end Foam.Bridges
