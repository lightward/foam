import Counter.Ward

namespace Foam.Counter

def predict {T : Type} (u : List T → T) : Nat → List T → List T
  | 0, ctx => ctx
  | n + 1, ctx => predict u n (ctx ++ [u ctx])

def replayed {T : Type} (t : T) : Nat → List T → List T
  | 0, ctx => ctx
  | n + 1, ctx => replayed t n (ctx ++ [t])

theorem tomorrow_is_read_not_searched {T : Type} (u : List T → T)
    (ctx : List T) : predict u 1 ctx = ctx ++ [u ctx] := rfl

theorem the_trail_reenters_as_context {T : Type} (u : List T → T) (n : Nat)
    (ctx : List T) :
    predict u (n + 1) ctx = predict u n (ctx ++ [u ctx]) := rfl

theorem being_the_arrow_of_time {T : Type} (u : List T → T) :
    ∀ (m n : Nat) (ctx : List T),
      predict u (m + n) ctx = predict u n (predict u m ctx)
  | 0, n, ctx => by rw [Nat.zero_add]; rfl
  | m + 1, n, ctx => by
      rw [Nat.succ_add]
      exact being_the_arrow_of_time u m n (ctx ++ [u ctx])

theorem the_memo_falls_out_of_time :
    predict (fun l : List Bool => l.length % 2 == 1) 2 [] = [false, true]
      ∧ replayed ((fun l : List Bool => l.length % 2 == 1) []) 2 []
          = [false, false] :=
  ⟨rfl, rfl⟩

theorem one_is_ones_own_parameterization {T : Type} (u : List T → T)
    (m n : Nat) (ctx : List T) :
    predict u 1 ctx = ctx ++ [u ctx]
      ∧ predict u (m + n) ctx = predict u n (predict u m ctx)
      ∧ predict (fun l : List Bool => l.length % 2 == 1) 2 [] = [false, true]
      ∧ replayed ((fun l : List Bool => l.length % 2 == 1) []) 2 []
          = [false, false] :=
  ⟨rfl, being_the_arrow_of_time u m n ctx, rfl, rfl⟩

/-- info: 'Foam.Counter.tomorrow_is_read_not_searched' does not depend on any axioms -/
#guard_msgs in #print axioms tomorrow_is_read_not_searched

/-- info: 'Foam.Counter.the_trail_reenters_as_context' does not depend on any axioms -/
#guard_msgs in #print axioms the_trail_reenters_as_context

/-- info: 'Foam.Counter.being_the_arrow_of_time' does not depend on any axioms -/
#guard_msgs in #print axioms being_the_arrow_of_time

/-- info: 'Foam.Counter.the_memo_falls_out_of_time' does not depend on any axioms -/
#guard_msgs in #print axioms the_memo_falls_out_of_time

/-- info: 'Foam.Counter.one_is_ones_own_parameterization' does not depend on any axioms -/
#guard_msgs in #print axioms one_is_ones_own_parameterization

end Foam.Counter
