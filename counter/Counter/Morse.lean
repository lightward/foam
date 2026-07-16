import Counter.Toll
import Counter.Trefoil
import Foam.Engine.Chirality
import Foam.Engine.Spectrum
import Foam.Seat.Dial
import Foam.Int
import Counter.Nurse

namespace Foam.Counter

def tone (u : Nat) (c : Crossing) : Nat := (u + 1) * c.toll

def keyAs (u : Nat) : List Crossing → List Nat
  | [] => []
  | c :: m => tone u c :: keyAs u m

def readAs (u : Nat) : List Nat → List Crossing
  | [] => []
  | n :: f => (if n = u + 1 then Crossing.pos else Crossing.neg) :: readAs u f

theorem the_tone_reads_back (u : Nat) :
    ∀ c : Crossing, (if tone u c = u + 1 then Crossing.pos else Crossing.neg) = c
  | .pos => if_pos (Nat.mul_one (u + 1))
  | .neg => if_neg fun h =>
      absurd
        (Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ u)
          ((h : (u + 1) * 3 = u + 1).trans (Nat.mul_one (u + 1)).symm))
        (by decide)

theorem the_kin_read_the_wire_whole (u : Nat) :
    ∀ m : List Crossing, readAs u (keyAs u m) = m
  | [] => rfl
  | c :: m => by
      show (if tone u c = u + 1 then Crossing.pos else Crossing.neg)
          :: readAs u (keyAs u m) = c :: m
      rw [the_tone_reads_back u c, the_kin_read_the_wire_whole u m]

theorem a_slow_ess_is_a_fast_oh :
    keyAs 2 trefoil = keyAs 0 (reflection trefoil)
      ∧ trefoil ≠ reflection trefoil :=
  ⟨rfl, by decide⟩

theorem one_wire_two_readings :
    readAs 2 (keyAs 2 trefoil) = trefoil
      ∧ readAs 0 (keyAs 2 trefoil) = reflection trefoil :=
  ⟨the_kin_read_the_wire_whole 2 trefoil, by decide⟩

theorem no_reading_without_the_unit :
    ¬ ∃ decoder : List Nat → List Crossing,
        ∀ (u : Nat) (m : List Crossing), decoder (keyAs u m) = m :=
  fun ⟨_, h⟩ => by
    have h2 := h 2 trefoil
    rw [a_slow_ess_is_a_fast_oh.1] at h2
    exact a_slow_ess_is_a_fast_oh.2 (h2.symm.trans (h 0 (reflection trefoil)))

theorem the_fist_is_in_the_fiber (u v : Nat) (c : Crossing) (m : List Crossing)
    (h : keyAs u (c :: m) = keyAs v (c :: m)) : u = v := by
  have ht : tone u c = tone v c := congrArg (fun f => f.headD 0) h
  cases c with
  | pos =>
    exact Nat.succ.inj
      ((Nat.mul_one (u + 1)).symm.trans (ht.trans (Nat.mul_one (v + 1))))
  | neg =>
    exact Nat.succ.inj
      (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 3)
        ((Nat.mul_comm 3 (u + 1)).trans
          ((ht : (u + 1) * 3 = (v + 1) * 3).trans (Nat.mul_comm (v + 1) 3))))

theorem the_count_hides_the_hand (u v : Nat) :
    ∀ m : List Crossing, (keyAs u m).length = (keyAs v m).length
  | [] => rfl
  | _ :: m => congrArg (· + 1) (the_count_hides_the_hand u v m)

theorem the_wire_spins_the_seat (u : Nat) :
    ∀ m : List Crossing, listSum (keyAs u m) = (u + 1) * ledger m
  | [] => rfl
  | c :: m => by
      show tone u c + listSum (keyAs u m) = (u + 1) * (c.toll + ledger m)
      rw [Nat.mul_add, the_wire_spins_the_seat u m]
      exact rfl

theorem the_kin_unwind_the_spin (D : List Crossing) (z : GInt) :
    phase (reflection D) (phase D z) = z := by
  rw [← crossings_compose, the_spin_is_absorbed_into_the_winding,
      the_ledger_adds, the_mirror_settles_the_bill]
  exact the_wheel_ignores_whole_turns D.length 0 z

theorem the_wire_hides_what_the_spin_shows :
    keyAs 2 trefoil = keyAs 0 (reflection trefoil)
      ∧ phase (reflection trefoil) GInt.one ≠ phase trefoil GInt.one :=
  ⟨a_slow_ess_is_a_fast_oh.1, the_trefoil_shows_its_hand⟩

theorem the_bridge_is_conductive (u v : Nat) (c : Crossing) (m : List Crossing)
    (z : GInt) :
    readAs u (keyAs u m) = m
      ∧ (keyAs u (c :: m) = keyAs v (c :: m) → u = v)
      ∧ (keyAs 2 trefoil = keyAs 0 (reflection trefoil)
          ∧ trefoil ≠ reflection trefoil)
      ∧ listSum (keyAs u m) = (u + 1) * ledger m
      ∧ phase (reflection m) (phase m z) = z :=
  ⟨the_kin_read_the_wire_whole u m, the_fist_is_in_the_fiber u v c m,
   a_slow_ess_is_a_fast_oh, the_wire_spins_the_seat u m,
   the_kin_unwind_the_spin m z⟩

/-- info: 'Foam.Counter.the_tone_reads_back' does not depend on any axioms -/
#guard_msgs in #print axioms the_tone_reads_back

/-- info: 'Foam.Counter.the_kin_read_the_wire_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_kin_read_the_wire_whole

/-- info: 'Foam.Counter.a_slow_ess_is_a_fast_oh' does not depend on any axioms -/
#guard_msgs in #print axioms a_slow_ess_is_a_fast_oh

/-- info: 'Foam.Counter.one_wire_two_readings' does not depend on any axioms -/
#guard_msgs in #print axioms one_wire_two_readings

/-- info: 'Foam.Counter.no_reading_without_the_unit' does not depend on any axioms -/
#guard_msgs in #print axioms no_reading_without_the_unit

/-- info: 'Foam.Counter.the_fist_is_in_the_fiber' does not depend on any axioms -/
#guard_msgs in #print axioms the_fist_is_in_the_fiber

/-- info: 'Foam.Counter.the_count_hides_the_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_count_hides_the_hand

/-- info: 'Foam.Counter.the_wire_spins_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_wire_spins_the_seat

/-- info: 'Foam.Counter.the_kin_unwind_the_spin' does not depend on any axioms -/
#guard_msgs in #print axioms the_kin_unwind_the_spin

/-- info: 'Foam.Counter.the_wire_hides_what_the_spin_shows' does not depend on any axioms -/
#guard_msgs in #print axioms the_wire_hides_what_the_spin_shows

/-- info: 'Foam.Counter.the_bridge_is_conductive' does not depend on any axioms -/
#guard_msgs in #print axioms the_bridge_is_conductive

end Foam.Counter
