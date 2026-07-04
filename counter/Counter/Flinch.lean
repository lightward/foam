import Counter.Bless

namespace Foam.Counter

theorem the_flinch_hides_until_touched (θ field act act' : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1))
    (hrest : GInt.align θ act' = 0) :
    GInt.born θ (field.add act') = GInt.born θ field + GInt.born θ act'
      ∧ GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
          = GInt.born θ field + GInt.born θ act :=
  ⟨silence_is_safe θ field act' hrest,
   the_standing_debt_taxes_the_aligned_act θ field act n m hf ha⟩

theorem the_frame_decides_the_sign :
    ∃ w w' z : GInt, GInt.align w z = 1 ∧ GInt.align w' z = -1 :=
  ⟨⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, by decide, by decide⟩

theorem a_frame_of_peace_always_exists (z : GInt) : GInt.align z.rot z = 0 := by
  show -z.im * z.re + z.re * z.im = 0
  rw [FInt.neg_mul, FInt.mulComm z.re z.im]
  exact FInt.add_left_neg (z.im * z.re)

theorem shedding_is_turning (θ act field : GInt) :
    GInt.align θ act * GInt.align θ field
      + GInt.align θ act * GInt.align θ (GInt.rot field)
      + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot field))
      + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot (GInt.rot field)))
      = 0 :=
  the_turned_field_pays_no_standing_tax θ act field

theorem the_touch_is_the_doorbell (m : Nat) :
    checkedSettle (Int.negSucc 0) (Int.negSucc 0) = 0
      ∧ checkedSettle (Int.ofNat m) (Int.ofNat m) = Int.ofNat m :=
  ⟨fresh_settle_grounds, settle_stops_at_ground m⟩

theorem moot_paths_flinch (θ field act act' z : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.negSucc n)
    (ha : GInt.align θ act = Int.ofNat (m + 1))
    (hrest : GInt.align θ act' = 0) :
    (GInt.born θ (field.add act') = GInt.born θ field + GInt.born θ act')
      ∧ (GInt.born θ (field.add act) + Int.ofNat (2 * ((n + 1) * m + n) + 1 + 1)
          = GInt.born θ field + GInt.born θ act)
      ∧ (∃ w w' y : GInt, GInt.align w y = 1 ∧ GInt.align w' y = -1)
      ∧ GInt.align z.rot z = 0 :=
  ⟨silence_is_safe θ field act' hrest,
   the_standing_debt_taxes_the_aligned_act θ field act n m hf ha,
   the_frame_decides_the_sign,
   a_frame_of_peace_always_exists z⟩

/-- info: 'Foam.Counter.the_flinch_hides_until_touched' does not depend on any axioms -/
#guard_msgs in #print axioms the_flinch_hides_until_touched

/-- info: 'Foam.Counter.the_frame_decides_the_sign' does not depend on any axioms -/
#guard_msgs in #print axioms the_frame_decides_the_sign

/-- info: 'Foam.Counter.a_frame_of_peace_always_exists' does not depend on any axioms -/
#guard_msgs in #print axioms a_frame_of_peace_always_exists

/-- info: 'Foam.Counter.shedding_is_turning' does not depend on any axioms -/
#guard_msgs in #print axioms shedding_is_turning

/-- info: 'Foam.Counter.the_touch_is_the_doorbell' does not depend on any axioms -/
#guard_msgs in #print axioms the_touch_is_the_doorbell

/-- info: 'Foam.Counter.moot_paths_flinch' does not depend on any axioms -/
#guard_msgs in #print axioms moot_paths_flinch

end Foam.Counter
