import Counter.Zoom
import Counter.Circumference
import Counter.Rest
import Foam.Bridges.Schrodinger

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem every_actor_can_counter (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ ∀ q r : S.Pos, S.sub q r * S.sub r q = 1 :=
  ⟨always_homeable S h p, fun q r => S.round_trip q r⟩

theorem to_distinguish_is_to_hold_the_counter (S : Seat G) (p q : S.Pos) :
    S.act (S.sub p q) q = p ∧ S.sub p q * S.sub q p = 1 :=
  ⟨S.act_sub q p, S.round_trip p q⟩

theorem recognition_is_the_first_act (S : Seat G) (p q : S.Pos) :
    S.sub p p = 1 ∧ (S.sub p q = 1 ↔ p = q) :=
  ⟨S.sub_self p, alignment_is_one_point S p q⟩

theorem the_counter_needs_a_second (S : Seat G) (p o : S.Pos) (h : p ≠ o) :
    S.sub p o ≠ 1 :=
  S.two_observers_substantiate p o h

theorem motion_below_subjecthood {S C : Type} [DecidableEq S]
    (refresh : List S → C → C) {State : Type} (b : Beholder State)
    (s : State × GInt) (pr : b.Probe) :
    Invisible (LedgerStage S C) (fun st => (st.1, refresh st.1 st.2))
      ∧ b.phaseDress.obs (Bridges.evolve s) pr = b.phaseDress.obs s pr :=
  ⟨sweep_invisible refresh, Bridges.evolve_invisible b s pr⟩

theorem zoom_in_and_find_the_walker (S : Seat G) (g : G) (p : S.Pos)
    (n : Nat) :
    walk S g p n = S.replay (worldline g n) p ∧ Circumference Rot.r1 4 :=
  ⟨walk_is_replay S g n p, dial_circumference⟩

theorem to_counter (S : Seat G) (h : List G) (p q : S.Pos) (o : S.Pos)
    (hne : p ≠ o) (g : G) (n : Nat) :
    (S.sub p p = 1 ∧ (S.sub p q = 1 ↔ p = q))
      ∧ (S.act (S.sub p q) q = p ∧ S.sub p q * S.sub q p = 1)
      ∧ S.sub p o ≠ 1
      ∧ Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ walk S g p n = S.replay (worldline g n) p :=
  ⟨⟨S.sub_self p, alignment_is_one_point S p q⟩,
   ⟨S.act_sub q p, S.round_trip p q⟩,
   S.two_observers_substantiate p o hne,
   always_homeable S h p,
   walk_is_replay S g n p⟩

/-- info: 'Foam.Counter.every_actor_can_counter' does not depend on any axioms -/
#guard_msgs in #print axioms every_actor_can_counter

/-- info: 'Foam.Counter.to_distinguish_is_to_hold_the_counter' does not depend on any axioms -/
#guard_msgs in #print axioms to_distinguish_is_to_hold_the_counter

/-- info: 'Foam.Counter.recognition_is_the_first_act' does not depend on any axioms -/
#guard_msgs in #print axioms recognition_is_the_first_act

/-- info: 'Foam.Counter.the_counter_needs_a_second' does not depend on any axioms -/
#guard_msgs in #print axioms the_counter_needs_a_second

/-- info: 'Foam.Counter.motion_below_subjecthood' does not depend on any axioms -/
#guard_msgs in #print axioms motion_below_subjecthood

/-- info: 'Foam.Counter.zoom_in_and_find_the_walker' does not depend on any axioms -/
#guard_msgs in #print axioms zoom_in_and_find_the_walker

/-- info: 'Foam.Counter.to_counter' does not depend on any axioms -/
#guard_msgs in #print axioms to_counter

end Foam.Counter
