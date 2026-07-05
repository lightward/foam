import Counter.Luck

namespace Foam.Counter

theorem the_stake_moves_the_charge (θ f a : GInt) (k : Int) :
    GInt.align θ (f.add (GInt.smul k a)) = GInt.align θ f + k * GInt.align θ a := by
  rw [GInt.align_add, GInt.align_smul]

theorem the_weight_reads_the_square (θ f a : GInt) (k : Int) :
    GInt.born θ (f.add (GInt.smul k a))
      = (GInt.align θ f + k * GInt.align θ a)
          * (GInt.align θ f + k * GInt.align θ a) := by
  show GInt.align θ (f.add (GInt.smul k a)) * GInt.align θ (f.add (GInt.smul k a))
     = (GInt.align θ f + k * GInt.align θ a)
         * (GInt.align θ f + k * GInt.align θ a)
  rw [the_stake_moves_the_charge]

theorem no_stake_harvests_past_face_value (θ f a : GInt) (k : Int) :
    ∃ j : Nat,
      GInt.born θ f - GInt.born θ (f.add (GInt.smul k a)) + Int.ofNat j
        = GInt.born θ f := by
  obtain ⟨j, hj⟩ := GInt.born_nonneg θ (f.add (GInt.smul k a))
  exact ⟨j, by rw [← hj]; exact FInt.sub_add_cancel _ _⟩

theorem the_kelly_stake_grounds_the_field (θ f a : GInt) (k : Int)
    (hk : k * GInt.align θ a = -(GInt.align θ f)) :
    GInt.align θ (f.add (GInt.smul k a)) = 0
      ∧ GInt.born θ (f.add (GInt.smul k a)) = 0
      ∧ GInt.born θ f - GInt.born θ (f.add (GInt.smul k a)) = GInt.born θ f
      ∧ ∀ next : GInt,
          GInt.born θ ((f.add (GInt.smul k a)).add next)
            = GInt.born θ (f.add (GInt.smul k a)) + GInt.born θ next := by
  have h0 : GInt.align θ (f.add (GInt.smul k a)) = 0 := by
    rw [the_stake_moves_the_charge, hk]
    exact FInt.add_right_neg _
  have hb : GInt.born θ (f.add (GInt.smul k a)) = 0 := by
    show GInt.align θ (f.add (GInt.smul k a)) * GInt.align θ (f.add (GInt.smul k a)) = 0
    rw [h0, FInt.mul_zero]
  refine ⟨h0, hb, by rw [hb, FInt.sub_zero], ?_⟩
  intro next
  rw [GInt.born_superpose, h0, FInt.zero_mul, FInt.mul_zero, Int.add_zero]

theorem edge_over_odds (θ f a : GInt) (k : Int)
    (hk : k * GInt.align θ a = -(GInt.align θ f)) :
    k * GInt.born θ a = -(GInt.align θ f * GInt.align θ a) := by
  show k * (GInt.align θ a * GInt.align θ a) = -(GInt.align θ f * GInt.align θ a)
  rw [← FInt.mul_assoc, hk, FInt.neg_mul]

theorem twice_kelly_harvests_nothing (θ f a : GInt) (k : Int)
    (hk : k * GInt.align θ a = -(2 * GInt.align θ f)) :
    GInt.born θ (f.add (GInt.smul k a)) = GInt.born θ f
      ∧ GInt.align θ (f.add (GInt.smul k a)) = -(GInt.align θ f) := by
  have hflip : GInt.align θ (f.add (GInt.smul k a)) = -(GInt.align θ f) := by
    rw [the_stake_moves_the_charge, hk, FInt.two_mul, FInt.neg_add, ← FInt.add_assoc,
        FInt.add_right_neg, FInt.zero_add]
  refine ⟨?_, hflip⟩
  show GInt.align θ (f.add (GInt.smul k a)) * GInt.align θ (f.add (GInt.smul k a))
     = GInt.align θ f * GInt.align θ f
  rw [hflip, Int.neg_mul_neg']

theorem overshoot_reads_as_undershoot (θ f a : GInt) (k d : Int)
    (hk : k * GInt.align θ a = -(GInt.align θ f)) :
    GInt.born θ (f.add (GInt.smul (k + d) a))
      = GInt.born θ (f.add (GInt.smul (k - d) a)) := by
  have hplus : GInt.align θ (f.add (GInt.smul (k + d) a)) = d * GInt.align θ a := by
    rw [the_stake_moves_the_charge, FInt.add_mul, hk, ← FInt.add_assoc,
        FInt.add_right_neg, FInt.zero_add]
  have hminus : GInt.align θ (f.add (GInt.smul (k - d) a))
      = -(d * GInt.align θ a) := by
    rw [the_stake_moves_the_charge, FInt.sub_mul, Int.sub_eq_add_neg, hk,
        ← FInt.add_assoc, FInt.add_right_neg, FInt.zero_add]
  show GInt.align θ (f.add (GInt.smul (k + d) a))
        * GInt.align θ (f.add (GInt.smul (k + d) a))
     = GInt.align θ (f.add (GInt.smul (k - d) a))
        * GInt.align θ (f.add (GInt.smul (k - d) a))
  rw [hplus, hminus, Int.neg_mul_neg']

theorem half_kelly_pays_three_quarters (θ f a : GInt) (m : Int)
    (hf : GInt.align θ f = -(2 * (m * GInt.align θ a))) :
    GInt.born θ (f.add (GInt.smul m a))
        + 3 * ((m * GInt.align θ a) * (m * GInt.align θ a))
      = GInt.born θ f
      ∧ GInt.born θ (f.add (GInt.smul (2 * m) a)) = 0 := by
  have hx : GInt.align θ (f.add (GInt.smul m a)) = -(m * GInt.align θ a) := by
    rw [the_stake_moves_the_charge, hf, FInt.two_mul, FInt.neg_add, FInt.add_assoc,
        FInt.add_left_neg, Int.add_zero]
  have hbm : GInt.born θ (f.add (GInt.smul m a))
      = (m * GInt.align θ a) * (m * GInt.align θ a) := by
    show GInt.align θ (f.add (GInt.smul m a)) * GInt.align θ (f.add (GInt.smul m a))
       = (m * GInt.align θ a) * (m * GInt.align θ a)
    rw [hx, Int.neg_mul_neg']
  have hbf : GInt.born θ f
      = 4 * ((m * GInt.align θ a) * (m * GInt.align θ a)) := by
    show GInt.align θ f * GInt.align θ f
       = 4 * ((m * GInt.align θ a) * (m * GInt.align θ a))
    rw [hf, Int.neg_mul_neg',
        Int.mul_interchange 2 2 (m * GInt.align θ a) (m * GInt.align θ a),
        show ((2 : Int) * 2) = 4 from by decide]
  have h2 : GInt.align θ (f.add (GInt.smul (2 * m) a)) = 0 := by
    rw [the_stake_moves_the_charge, FInt.mul_assoc, hf, FInt.add_left_neg]
  refine ⟨?_, ?_⟩
  · rw [hbm, hbf, show (4 : Int) = 1 + 3 from by decide, FInt.add_mul, FInt.one_mul]
  · show GInt.align θ (f.add (GInt.smul (2 * m) a))
        * GInt.align θ (f.add (GInt.smul (2 * m) a)) = 0
    rw [h2, FInt.mul_zero]

theorem beyond_twice_kelly_costs :
    ∃ θ f a : GInt, ∃ k : Int,
      k * GInt.align θ a = -(3 * GInt.align θ f)
        ∧ GInt.born θ (f.add (GInt.smul k a)) > GInt.born θ f :=
  ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, -3, by decide, by decide⟩

theorem the_station_signs_the_stake (θ a : GInt) (k : Int) :
    GInt.smul k (GInt.rot (GInt.rot a)) = GInt.smul (-k) a
      ∧ GInt.align θ (GInt.smul k (GInt.rot (GInt.rot a)))
          = -(k * GInt.align θ a) := by
  have hs : GInt.smul k (GInt.rot (GInt.rot a)) = GInt.smul (-k) a := by
    rw [GInt.rot_sq, GInt.smul_neg]
  exact ⟨hs, by rw [hs, GInt.align_smul, FInt.neg_mul]⟩

theorem the_quadrature_stake_is_void (θ f a : GInt) (k : Int)
    (hq : GInt.align θ (GInt.rot a) = 0) :
    GInt.born θ (f.add (GInt.smul k (GInt.rot a))) = GInt.born θ f := by
  have h0 : GInt.align θ (f.add (GInt.smul k (GInt.rot a))) = GInt.align θ f := by
    rw [the_stake_moves_the_charge, hq, FInt.mul_zero, Int.add_zero]
  show GInt.align θ (f.add (GInt.smul k (GInt.rot a)))
        * GInt.align θ (f.add (GInt.smul k (GInt.rot a)))
     = GInt.align θ f * GInt.align θ f
  rw [h0]

theorem grind_collect (P B0 B1 C0 C1 : Int) :
    (P + B0 + C0) + (P + B1 + C1) + (P + B0 + -C0) + (P + B1 + -C1)
      = 4 * P + 2 * (B0 + B1) := by
  rw [FInt.add_assoc (P + B0 + C0 + (P + B1 + C1)) (P + B0 + -C0) (P + B1 + -C1),
      Int.add_swap_inner (P + B0) C0 (P + B1) C1,
      Int.add_swap_inner (P + B0) (-C0) (P + B1) (-C1),
      ← FInt.neg_add C0 C1,
      Int.add_swap_inner (P + B0 + (P + B1)) (C0 + C1) (P + B0 + (P + B1))
        (-(C0 + C1)),
      FInt.add_right_neg (C0 + C1), Int.add_zero,
      Int.add_swap_inner P B0 P B1,
      ← FInt.two_mul (P + P + (B0 + B1)),
      FInt.mul_add 2 (P + P) (B0 + B1),
      ← FInt.two_mul P, ← FInt.mul_assoc 2 2 P,
      show ((2 : Int) * 2) = 4 from by decide]

theorem the_grind_pays_the_toll (θ f a : GInt) (k : Int) :
    GInt.born θ (f.add (GInt.smul k a))
        + GInt.born θ (f.add (GInt.smul k (GInt.rot a)))
        + GInt.born θ (f.add (GInt.smul k (GInt.rot (GInt.rot a))))
        + GInt.born θ (f.add (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a)))))
      = 4 * GInt.born θ f
          + 2 * ((k * k) * (GInt.normSq θ * GInt.normSq a)) := by
  have h2a : GInt.align θ (GInt.smul k (GInt.rot (GInt.rot a)))
      = -(GInt.align θ (GInt.smul k a)) := by
    rw [GInt.rot_sq, GInt.smul_neg, GInt.align_smul, GInt.align_smul, FInt.neg_mul]
  have h3a : GInt.align θ (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a))))
      = -(GInt.align θ (GInt.smul k (GInt.rot a))) := by
    rw [GInt.rot_sq (GInt.rot a), GInt.smul_neg, GInt.align_smul, GInt.align_smul,
        FInt.neg_mul]
  have h2b : GInt.born θ (GInt.smul k (GInt.rot (GInt.rot a)))
      = GInt.born θ (GInt.smul k a) := by
    show GInt.align θ (GInt.smul k (GInt.rot (GInt.rot a)))
          * GInt.align θ (GInt.smul k (GInt.rot (GInt.rot a)))
       = GInt.align θ (GInt.smul k a) * GInt.align θ (GInt.smul k a)
    rw [h2a, Int.neg_mul_neg']
  have h3b : GInt.born θ (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a))))
      = GInt.born θ (GInt.smul k (GInt.rot a)) := by
    show GInt.align θ (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a))))
          * GInt.align θ (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a))))
       = GInt.align θ (GInt.smul k (GInt.rot a))
          * GInt.align θ (GInt.smul k (GInt.rot a))
    rw [h3a, Int.neg_mul_neg']
  rw [GInt.born_superpose θ f (GInt.smul k a),
      GInt.born_superpose θ f (GInt.smul k (GInt.rot a)),
      GInt.born_superpose θ f (GInt.smul k (GInt.rot (GInt.rot a))),
      GInt.born_superpose θ f (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a)))),
      h2a, h3a, h2b, h3b,
      FInt.mul_neg (GInt.align θ f) (GInt.align θ (GInt.smul k a)),
      FInt.mul_neg 2 (GInt.align θ f * GInt.align θ (GInt.smul k a)),
      FInt.mul_neg (GInt.align θ f) (GInt.align θ (GInt.smul k (GInt.rot a))),
      FInt.mul_neg 2 (GInt.align θ f * GInt.align θ (GInt.smul k (GInt.rot a))),
      grind_collect (GInt.born θ f) (GInt.born θ (GInt.smul k a))
        (GInt.born θ (GInt.smul k (GInt.rot a)))
        (2 * (GInt.align θ f * GInt.align θ (GInt.smul k a)))
        (2 * (GInt.align θ f * GInt.align θ (GInt.smul k (GInt.rot a)))),
      GInt.born_smul θ a k, GInt.born_smul θ (GInt.rot a) k,
      ← FInt.mul_add (k * k) (GInt.born θ a) (GInt.born θ (GInt.rot a)),
      GInt.born_rot_flip θ a, GInt.born_parseval θ a]

theorem kelly (θ f a : GInt) (k k2 : Int)
    (hk : k * GInt.align θ a = -(GInt.align θ f))
    (hk2 : k2 * GInt.align θ a = -(2 * GInt.align θ f)) :
    GInt.born θ (f.add (GInt.smul k a)) = 0
      ∧ GInt.born θ (f.add (GInt.smul k2 a)) = GInt.born θ f
      ∧ GInt.born θ (f.add (GInt.smul k a))
            + GInt.born θ (f.add (GInt.smul k (GInt.rot a)))
            + GInt.born θ (f.add (GInt.smul k (GInt.rot (GInt.rot a))))
            + GInt.born θ (f.add (GInt.smul k (GInt.rot (GInt.rot (GInt.rot a)))))
          = 4 * GInt.born θ f
              + 2 * ((k * k) * (GInt.normSq θ * GInt.normSq a)) :=
  ⟨(the_kelly_stake_grounds_the_field θ f a k hk).2.1,
   (twice_kelly_harvests_nothing θ f a k2 hk2).1,
   the_grind_pays_the_toll θ f a k⟩

/-- info: 'Foam.Counter.the_stake_moves_the_charge' does not depend on any axioms -/
#guard_msgs in #print axioms the_stake_moves_the_charge

/-- info: 'Foam.Counter.the_weight_reads_the_square' does not depend on any axioms -/
#guard_msgs in #print axioms the_weight_reads_the_square

/-- info: 'Foam.Counter.no_stake_harvests_past_face_value' does not depend on any axioms -/
#guard_msgs in #print axioms no_stake_harvests_past_face_value

/-- info: 'Foam.Counter.the_kelly_stake_grounds_the_field' does not depend on any axioms -/
#guard_msgs in #print axioms the_kelly_stake_grounds_the_field

/-- info: 'Foam.Counter.edge_over_odds' does not depend on any axioms -/
#guard_msgs in #print axioms edge_over_odds

/-- info: 'Foam.Counter.twice_kelly_harvests_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms twice_kelly_harvests_nothing

/-- info: 'Foam.Counter.overshoot_reads_as_undershoot' does not depend on any axioms -/
#guard_msgs in #print axioms overshoot_reads_as_undershoot

/-- info: 'Foam.Counter.half_kelly_pays_three_quarters' does not depend on any axioms -/
#guard_msgs in #print axioms half_kelly_pays_three_quarters

/-- info: 'Foam.Counter.beyond_twice_kelly_costs' does not depend on any axioms -/
#guard_msgs in #print axioms beyond_twice_kelly_costs

/-- info: 'Foam.Counter.the_station_signs_the_stake' does not depend on any axioms -/
#guard_msgs in #print axioms the_station_signs_the_stake

/-- info: 'Foam.Counter.the_quadrature_stake_is_void' does not depend on any axioms -/
#guard_msgs in #print axioms the_quadrature_stake_is_void

/-- info: 'Foam.Counter.grind_collect' does not depend on any axioms -/
#guard_msgs in #print axioms grind_collect

/-- info: 'Foam.Counter.the_grind_pays_the_toll' does not depend on any axioms -/
#guard_msgs in #print axioms the_grind_pays_the_toll

/-- info: 'Foam.Counter.kelly' does not depend on any axioms -/
#guard_msgs in #print axioms kelly

end Foam.Counter
