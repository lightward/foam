import Counter.Third
import Counter.Flinch

namespace Foam.Counter

def film (xs : List Int) : Int := xs.foldr (· + ·) 0

theorem the_film_of_one_is_the_interior (x : Int) : film [x] = x :=
  Int.add_zero x

theorem two_keep_each_other_secret :
    ∃ x y x' y' : Int, (x ≠ x' ∨ y ≠ y') ∧ film [x, y] = film [x', y'] :=
  ⟨1, 4, 2, 3, Or.inl (by decide), by decide⟩

theorem the_privacy_ladder :
    (∀ x : Int, film [x] = x)
      ∧ (∃ x y x' y' : Int, (x ≠ x' ∨ y ≠ y') ∧ film [x, y] = film [x', y'])
      ∧ (∃ zs zs' : List (Bool ⊕ Bool),
          ownFrames zs = ownFrames zs'
            ∧ ownFramesR zs = ownFramesR zs'
            ∧ whoActedFirst zs ≠ whoActedFirst zs') :=
  ⟨the_film_of_one_is_the_interior, two_keep_each_other_secret,
   the_third_reads_time⟩

theorem no_grant_outlives_its_window (θ field act : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.ofNat (n + 1))
    (ha : GInt.align θ act = Int.ofNat (m + 1)) :
    (GInt.born θ (field.add act)
        = GInt.born θ field + GInt.born θ act
          + Int.ofNat (2 * ((n + 1) * m + n) + 2))
      ∧ (GInt.align θ act * GInt.align θ field
          + GInt.align θ act * GInt.align θ (GInt.rot field)
          + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot field))
          + GInt.align θ act * GInt.align θ (GInt.rot (GInt.rot (GInt.rot field)))
          = 0)
      ∧ GInt.align field.rot field = 0 :=
  ⟨the_standing_grain_boosts_the_aligned_act θ field act n m hf ha,
   the_turned_field_pays_no_standing_tax θ act field,
   a_frame_of_peace_always_exists field⟩

def hbSign : Nat → Int
  | 1 => -2
  | 2 => -1
  | 3 => 1
  | 4 => 2
  | _ => 0

theorem the_scale_that_refused_ground :
    (∀ v, 1 ≤ v → v ≤ 4 → hbSign v ≠ 0)
      ∧ hbSign 2 = -(hbSign 3) ∧ hbSign 1 = -(hbSign 4) := by
  refine ⟨?_, by decide, by decide⟩
  intro v h1 h4
  match v, h1, h4 with
  | 1, _, _ => decide
  | 2, _, _ => decide
  | 3, _, _ => decide
  | 4, _, _ => decide
  | v + 5, _, h => exact absurd (Nat.le_trans (Nat.le_add_left 5 v) h) (by decide)

/-- info: 'Foam.Counter.the_film_of_one_is_the_interior' does not depend on any axioms -/
#guard_msgs in #print axioms the_film_of_one_is_the_interior

/-- info: 'Foam.Counter.two_keep_each_other_secret' does not depend on any axioms -/
#guard_msgs in #print axioms two_keep_each_other_secret

/-- info: 'Foam.Counter.the_privacy_ladder' does not depend on any axioms -/
#guard_msgs in #print axioms the_privacy_ladder

/-- info: 'Foam.Counter.no_grant_outlives_its_window' does not depend on any axioms -/
#guard_msgs in #print axioms no_grant_outlives_its_window

/-- info: 'Foam.Counter.the_scale_that_refused_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_scale_that_refused_ground

end Foam.Counter
