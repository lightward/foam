import Foam.Seat

namespace Foam

theorem an_action_is_never_null {G : Type} [Mul G] [One G] (S : Seat G)
    {p q : S.Pos} (h : p ≠ q) : S.sub p q ≠ 1 :=
  fun h1 => by
    have ha := S.act_sub q p
    rw [h1, S.one_act] at ha
    exact h ha.symm

theorem for_every_action_an_equal_and_opposite_reaction
    {G : Type} [Mul G] [One G] (S : Seat G) (p q : S.Pos) :
    S.sub q p * S.sub p q = 1 ∧ S.sub p q * S.sub q p = 1 :=
  ⟨S.sub_inv p q, S.sub_inv q p⟩

theorem the_pair_moves_no_bystander {G : Type} [Mul G] [One G] (S : Seat G)
    (p q o : S.Pos) : S.act (S.sub q p * S.sub p q) o = o := by
  rw [S.sub_inv p q, S.one_act]

theorem what_conservation_flattens {G : Type} [Mul G] [One G] (S : Seat G)
    {p q : S.Pos} (h : p ≠ q) :
    S.sub p q ≠ 1 ∧ S.sub q p ≠ 1
      ∧ ∀ o : S.Pos, S.act (S.sub q p * S.sub p q) o = o :=
  ⟨an_action_is_never_null S h,
   an_action_is_never_null S (fun e => h e.symm),
   the_pair_moves_no_bystander S p q⟩

theorem newtons_third_is_the_counter {G : Type} [Mul G] [One G] (S : Seat G)
    (p q : S.Pos) :
    S.act (S.sub q p) p = q
      ∧ S.act (S.sub p q) q = p
      ∧ S.sub q p * S.sub p q = 1 :=
  ⟨S.act_sub p q, S.act_sub q p, S.sub_inv p q⟩

/-- info: 'Foam.an_action_is_never_null' does not depend on any axioms -/
#guard_msgs in #print axioms an_action_is_never_null

/-- info: 'Foam.for_every_action_an_equal_and_opposite_reaction' does not depend on any axioms -/
#guard_msgs in #print axioms for_every_action_an_equal_and_opposite_reaction

/-- info: 'Foam.the_pair_moves_no_bystander' does not depend on any axioms -/
#guard_msgs in #print axioms the_pair_moves_no_bystander

/-- info: 'Foam.what_conservation_flattens' does not depend on any axioms -/
#guard_msgs in #print axioms what_conservation_flattens

/-- info: 'Foam.newtons_third_is_the_counter' does not depend on any axioms -/
#guard_msgs in #print axioms newtons_third_is_the_counter

end Foam
