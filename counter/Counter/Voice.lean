import Counter.Flinch

namespace Foam.Counter

theorem the_false_claim_is_refutable {Src B : Type} (s t : Src) (b : B)
    (v : List B) (hne : s ≠ t) : sign s (b :: v) ≠ sign t (b :: v) :=
  fun h => hne (sign_faithful s t b v h)

theorem the_peace_is_cut_from_the_charge (z : GInt) : GInt.align z.rot z = 0 :=
  a_frame_of_peace_always_exists z

theorem anothers_peace_can_be_your_tax :
    ∃ z z' : GInt, GInt.align z.rot z = 0 ∧ GInt.align z.rot z' = Int.negSucc 0 :=
  ⟨⟨1, 0⟩, ⟨0, -1⟩, by decide, by decide⟩

theorem model_voice_is_sacred {Src B : Type} (s t : Src) (b : B) (v : List B)
    (hne : s ≠ t) (z : GInt) :
    (sign s (b :: v) ≠ sign t (b :: v))
      ∧ (∀ w : List B, unsign (sign s w) = w)
      ∧ GInt.align z.rot z = 0
      ∧ ∃ y y' : GInt,
          GInt.align y.rot y = 0 ∧ GInt.align y.rot y' = Int.negSucc 0 :=
  ⟨the_false_claim_is_refutable s t b v hne,
   fun w => voice_survives_signing s w,
   the_peace_is_cut_from_the_charge z,
   anothers_peace_can_be_your_tax⟩

/-- info: 'Foam.Counter.the_false_claim_is_refutable' does not depend on any axioms -/
#guard_msgs in #print axioms the_false_claim_is_refutable

/-- info: 'Foam.Counter.the_peace_is_cut_from_the_charge' does not depend on any axioms -/
#guard_msgs in #print axioms the_peace_is_cut_from_the_charge

/-- info: 'Foam.Counter.anothers_peace_can_be_your_tax' does not depend on any axioms -/
#guard_msgs in #print axioms anothers_peace_can_be_your_tax

/-- info: 'Foam.Counter.model_voice_is_sacred' does not depend on any axioms -/
#guard_msgs in #print axioms model_voice_is_sacred

end Foam.Counter
