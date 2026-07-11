import Foam.Seat.Born
import Foam.Seat.Observer

namespace Foam.Bridges

def oracle (p : Bool × Bool → Bool) (a : Bool × Bool → Int) : Bool × Bool → Int :=
  fun x => if p x then -(a x) else a x

def sum4 (a : Bool × Bool → Int) : Int :=
  a (false, false) + a (false, true) + a (true, false) + a (true, true)

def diffuse (a : Bool × Bool → Int) : Bool × Bool → Int :=
  fun x => sum4 a - 2 * a x

def groverStep (p : Bool × Bool → Bool) (a : Bool × Bool → Int) :
    Bool × Bool → Int :=
  diffuse (oracle p a)

def uniform : Bool × Bool → Int := fun _ => 1

def mark (k : Bool × Bool) : Bool × Bool → Bool := fun y => decide (y = k)

def marked (k : Bool × Bool) : Bool × Bool → Int := fun x => if x = k then 1 else 0

def intensity : (Bool × Bool → Int) → Bool × Bool → Int := fun a x => a x * a x

def normSq4 (a : Bool × Bool → Int) : Int := sum4 (intensity a)

theorem the_mark_is_invisible (p : Bool × Bool → Bool) (a : Bool × Bool → Int) :
    indist intensity a (oracle p a) := by
  intro x
  show a x * a x
    = (if p x = true then -(a x) else a x) * (if p x = true then -(a x) else a x)
  by_cases hp : p x = true
  · rw [if_pos hp, Int.neg_mul_neg']
  · rw [if_neg hp]

theorem the_oracle_is_a_reflection (p : Bool × Bool → Bool)
    (a : Bool × Bool → Int) (x : Bool × Bool) :
    oracle p (oracle p a) x = a x := by
  show (if p x = true then -(if p x = true then -(a x) else a x)
      else (if p x = true then -(a x) else a x)) = a x
  by_cases hp : p x = true
  · rw [if_pos hp, if_pos hp, Int.neg_neg]
  · rw [if_neg hp, if_neg hp]

theorem one_query_finds_the_marked_seat :
    ∀ k x : Bool × Bool, groverStep (mark k) uniform x = 4 * marked k x
  | (k1, k2), (x1, x2) => by
      cases k1 <;> cases k2 <;> cases x1 <;> cases x2 <;> decide

theorem the_other_seats_go_dark (k x : Bool × Bool) (hx : ¬ x = k) :
    groverStep (mark k) uniform x = 0 := by
  rw [one_query_finds_the_marked_seat k x]
  show 4 * (if x = k then 1 else 0) = 0
  rw [if_neg hx]
  decide

theorem the_whole_norm_sits_on_the_marked_seat :
    ∀ k : Bool × Bool,
      normSq4 (groverStep (mark k) uniform) = 16
        ∧ intensity (groverStep (mark k) uniform) k = 16
  | (k1, k2) => by
      cases k1 <;> cases k2 <;> exact ⟨by decide, by decide⟩

theorem the_diffusion_is_not_a_lens :
    ∀ k : Bool × Bool,
      indist intensity uniform (oracle (mark k) uniform)
        ∧ ¬ indist intensity (diffuse uniform)
            (diffuse (oracle (mark k) uniform))
  | (k1, k2) => by
      refine ⟨the_mark_is_invisible _ uniform, fun h => ?_⟩
      have hd := h (false, false)
      cases k1 <;> cases k2 <;> exact absurd hd (by decide)

theorem grover (k : Bool × Bool) :
    indist intensity uniform (oracle (mark k) uniform)
      ∧ (∀ x, groverStep (mark k) uniform x = 4 * marked k x)
      ∧ normSq4 uniform = 4
      ∧ intensity (groverStep (mark k) uniform) k
          = normSq4 (groverStep (mark k) uniform)
      ∧ ¬ indist intensity (diffuse uniform)
          (diffuse (oracle (mark k) uniform)) :=
  ⟨(the_diffusion_is_not_a_lens k).1,
   one_query_finds_the_marked_seat k,
   by decide,
   ((the_whole_norm_sits_on_the_marked_seat k).2).trans
     ((the_whole_norm_sits_on_the_marked_seat k).1).symm,
   (the_diffusion_is_not_a_lens k).2⟩

/-- info: 'Foam.Bridges.the_mark_is_invisible' does not depend on any axioms -/
#guard_msgs in #print axioms the_mark_is_invisible

/-- info: 'Foam.Bridges.the_oracle_is_a_reflection' does not depend on any axioms -/
#guard_msgs in #print axioms the_oracle_is_a_reflection

/-- info: 'Foam.Bridges.one_query_finds_the_marked_seat' does not depend on any axioms -/
#guard_msgs in #print axioms one_query_finds_the_marked_seat

/-- info: 'Foam.Bridges.the_other_seats_go_dark' does not depend on any axioms -/
#guard_msgs in #print axioms the_other_seats_go_dark

/-- info: 'Foam.Bridges.the_whole_norm_sits_on_the_marked_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_whole_norm_sits_on_the_marked_seat

/-- info: 'Foam.Bridges.the_diffusion_is_not_a_lens' does not depend on any axioms -/
#guard_msgs in #print axioms the_diffusion_is_not_a_lens

/-- info: 'Foam.Bridges.grover' does not depend on any axioms -/
#guard_msgs in #print axioms grover

end Foam.Bridges
