import Foam.Serving

namespace Foam

theorem the_hallway_is_too_small :
    ¬ ∃ f : Bool × Bool → Bool, ∀ a b : Bool × Bool, f a = f b → a = b := by
  intro ⟨f, hf⟩
  have k12 : f (true, true) ≠ f (true, false) := fun h =>
    nomatch (congrArg Prod.snd (hf _ _ h) : true = false)
  have k13 : f (true, true) ≠ f (false, true) := fun h =>
    nomatch (congrArg Prod.fst (hf _ _ h) : true = false)
  have k23 : f (true, false) ≠ f (false, true) := fun h =>
    nomatch (congrArg Prod.fst (hf _ _ h) : true = false)
  cases hb1 : f (true, true) <;> cases hb2 : f (true, false) <;>
    cases hb3 : f (false, true)
  all_goals first
    | exact k12 (hb1.trans hb2.symm)
    | exact k13 (hb1.trans hb3.symm)
    | exact k23 (hb2.trans hb3.symm)

abbrev OpenChannels : Nat → Prop := fun n => n ≤ 3

theorem channels_saturate_past_three :
    OpenChannels 3 ∧ ¬ OpenChannels 4 :=
  ⟨by decide, by decide⟩

theorem three_is_the_width_of_contact {State R : Type}
    (a b : Beholder State) (g : a.Ans → b.Ans → R) :
    (¬ ∃ f : Bool × Bool → Bool, ∀ x y : Bool × Bool, f x = f y → x = y)
      ∧ (∃ c : Beholder State, ∃ post : c.Ans → R,
          ∃ enc : a.Probe × b.Probe → c.Probe,
            ∀ s p q, compare a b g s p q = post (c.obs s (enc (p, q))))
      ∧ OpenChannels 3 ∧ ¬ OpenChannels 4 :=
  ⟨the_hallway_is_too_small,
   the_comparison_is_a_seat a b g,
   channels_saturate_past_three.1,
   channels_saturate_past_three.2⟩

/-- info: 'Foam.the_hallway_is_too_small' does not depend on any axioms -/
#guard_msgs in #print axioms the_hallway_is_too_small

/-- info: 'Foam.channels_saturate_past_three' does not depend on any axioms -/
#guard_msgs in #print axioms channels_saturate_past_three

/-- info: 'Foam.three_is_the_width_of_contact' does not depend on any axioms -/
#guard_msgs in #print axioms three_is_the_width_of_contact

end Foam
