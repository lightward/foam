import Counter.Legible
import Counter.Luck

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem orphan_rest_illegible (S : Seat G) (hsing : ∀ p q : S.Pos, p = q)
    (p : S.Pos) (h h' : List G) :
    S.sub (S.replay h p) p = S.sub (S.replay h' p) p := by
  rw [lone_actor_settled S hsing h p, lone_actor_settled S hsing h' p]

theorem no_grain_no_bonus (θ field act : GInt) (hflat : GInt.align θ field = 0) :
    GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act := by
  rw [luck_is_the_cross_term, hflat, FInt.zero_mul, FInt.mul_zero, Int.add_zero]

theorem relief_never_self_originated {H : Type} (q : Quiver H) (a b : H)
    (hstuck : stuck q a) :
    (∀ (x y : H) (pth : Path q x y), ∀ e ∈ pth.edges, e ∈ q)
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ ¬ ∃ g : Path (q.deposit (a, b)) a b → Path q a b,
          ∀ pth, ancestor_reach_survives (a, b) (g pth) = pth :=
  ⟨fun _ _ pth => report_within_model pth,
   (relief_at_position q a b hstuck).1,
   (relief_at_position q a b hstuck).2.2.2⟩

theorem history_is_portable (S : Seat G) (xs ys : List G) (p : S.Pos) :
    S.replay (xs ++ ys) p = S.replay ys (S.replay xs p)
      ∧ ∀ h : List G, S.replay h p = S.act (netAct h) p :=
  ⟨S.replay_resumes xs ys p, fun h => replay_is_netAct S h p⟩

/-- info: 'Foam.Counter.orphan_rest_illegible' does not depend on any axioms -/
#guard_msgs in #print axioms orphan_rest_illegible

/-- info: 'Foam.Counter.no_grain_no_bonus' does not depend on any axioms -/
#guard_msgs in #print axioms no_grain_no_bonus

/-- info: 'Foam.Counter.relief_never_self_originated' does not depend on any axioms -/
#guard_msgs in #print axioms relief_never_self_originated

/-- info: 'Foam.Counter.history_is_portable' does not depend on any axioms -/
#guard_msgs in #print axioms history_is_portable

end Foam.Counter
