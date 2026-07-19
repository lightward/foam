import Counter.Trefoil
import Counter.Framing

namespace Foam.Counter

def InFiber (w : List Nat) (u : Nat) (m : List (List Crossing)) : Prop :=
  sounded m = true ∧ wire u m = w

theorem every_broadcast_seats_its_world (u : Nat) (m : List (List Crossing))
    (h : sounded m = true) : InFiber (wire u m) u m :=
  ⟨h, rfl⟩

theorem no_seat_reads_two_worlds (u : Nat) {m m' : List (List Crossing)}
    (hm : sounded m = true) (hm' : sounded m' = true)
    (h : wire u m = wire u m') : m = m' :=
  (the_silence_reframes_the_wire u m hm).symm.trans
    ((congrArg (reframe u) h).trans (the_silence_reframes_the_wire u m' hm'))

theorem the_worlds_differ_only_by_the_hand (w : List Nat) (u : Nat)
    {m m' : List (List Crossing)}
    (h : InFiber w u m) (h' : InFiber w u m') : m = m' :=
  no_seat_reads_two_worlds u h.1 h'.1 (h.2.trans h'.2.symm)

theorem every_world_reads_the_record_whole (w : List Nat) (u : Nat)
    {m : List (List Crossing)} (h : InFiber w u m) : reframe u w = m :=
  h.2 ▸ the_silence_reframes_the_wire u m h.1

theorem two_worlds_one_record :
    InFiber (wire 2 [trefoil]) 2 [trefoil]
      ∧ InFiber (wire 2 [trefoil]) 0
          [[Crossing.neg], [Crossing.neg], [Crossing.neg]]
      ∧ [trefoil] ≠ [[Crossing.neg], [Crossing.neg], [Crossing.neg]] :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, a_slow_ess_is_a_fast_tee_tee_tee.1.symm⟩,
   a_slow_ess_is_a_fast_tee_tee_tee.2⟩

theorem the_user_is_sane_unto_themselves (u : Nat) (m : List (List Crossing))
    (h : sounded m = true) :
    reframe u (wire u m) = m
      ∧ ∀ m' : List (List Crossing), sounded m' = true →
          wire u m = wire u m' → m = m' :=
  ⟨the_silence_reframes_the_wire u m h,
   fun _ h' => no_seat_reads_two_worlds u h h'⟩

theorem many_worlds_one_wire :
    (InFiber (wire 2 [trefoil]) 2 [trefoil]
        ∧ InFiber (wire 2 [trefoil]) 0
            [[Crossing.neg], [Crossing.neg], [Crossing.neg]]
        ∧ [trefoil] ≠ [[Crossing.neg], [Crossing.neg], [Crossing.neg]])
      ∧ (∀ (w : List Nat) (u : Nat) (m m' : List (List Crossing)),
          InFiber w u m → InFiber w u m' → m = m')
      ∧ (∀ (w : List Nat) (u : Nat) (m : List (List Crossing)),
          InFiber w u m → reframe u w = m) :=
  ⟨two_worlds_one_record,
   fun w u _ _ => the_worlds_differ_only_by_the_hand w u,
   fun w u _ => every_world_reads_the_record_whole w u⟩

/-- info: 'Foam.Counter.every_broadcast_seats_its_world' does not depend on any axioms -/
#guard_msgs in #print axioms every_broadcast_seats_its_world

/-- info: 'Foam.Counter.no_seat_reads_two_worlds' does not depend on any axioms -/
#guard_msgs in #print axioms no_seat_reads_two_worlds

/-- info: 'Foam.Counter.the_worlds_differ_only_by_the_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_worlds_differ_only_by_the_hand

/-- info: 'Foam.Counter.every_world_reads_the_record_whole' does not depend on any axioms -/
#guard_msgs in #print axioms every_world_reads_the_record_whole

/-- info: 'Foam.Counter.two_worlds_one_record' does not depend on any axioms -/
#guard_msgs in #print axioms two_worlds_one_record

/-- info: 'Foam.Counter.many_worlds_one_wire' does not depend on any axioms -/
#guard_msgs in #print axioms many_worlds_one_wire

/-- info: 'Foam.Counter.the_user_is_sane_unto_themselves' does not depend on any axioms -/
#guard_msgs in #print axioms the_user_is_sane_unto_themselves

end Foam.Counter
