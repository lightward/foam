import Counter.Needle

namespace Foam.Counter

def recount {K : Type} : List (K × Bool) → Nat
  | [] => 0
  | (_, true) :: rest => recount rest + 1
  | (_, false) :: rest => recount rest

def audit {K : Type} : List (K × Bool) → Nat × Nat
  | [] => (0, 0)
  | (_, true) :: rest => ((audit rest).1 + 1, (audit rest).2 + 1)
  | (_, false) :: rest => ((audit rest).1, (audit rest).2 + 1)

def click : Nat → Bool → Nat
  | c, true => c + 1
  | c, false => c

theorem the_landing_clicks_the_counter {K : Type} (prior : List (K × Bool))
    (k : K) : ∀ b : Bool, recount (land prior k b) = click (recount prior) b
  | true => rfl
  | false => rfl

theorem the_recount_tolls_the_whole_record {K : Type} :
    ∀ board : List (K × Bool), audit board = (recount board, board.length)
  | [] => rfl
  | (_, true) :: rest =>
      congrArg (fun p : Nat × Nat => (p.1 + 1, p.2 + 1))
        (the_recount_tolls_the_whole_record rest)
  | (_, false) :: rest =>
      congrArg (fun p : Nat × Nat => (p.1, p.2 + 1))
        (the_recount_tolls_the_whole_record rest)

theorem each_recount_costs_more_than_the_last {K : Type}
    (prior : List (K × Bool)) (k : K) :
    ∀ b : Bool, (audit (land prior k b)).2 = (audit prior).2 + 1
  | true => rfl
  | false => rfl

theorem the_kept_counter_is_the_count {K : Type}
    (g : List (K × Bool) → Nat) (h0 : g [] = 0)
    (hstep : ∀ (prior : List (K × Bool)) (k : K) (b : Bool),
      g (land prior k b) = click (g prior) b) :
    ∀ board : List (K × Bool), g board = recount board
  | [] => h0
  | (k, b) :: rest =>
      (hstep rest k b : g ((k, b) :: rest) = click (g rest) b).trans
        ((congrArg (fun c => click c b)
            (the_kept_counter_is_the_count g h0 hstep rest)).trans
          (the_landing_clicks_the_counter rest k b).symm)

theorem counter_counts_so_you_dont_have_to {K : Type}
    (prior board : List (K × Bool)) (k : K) (b : Bool)
    (g : List (K × Bool) → Nat) (h0 : g [] = 0)
    (hstep : ∀ (p : List (K × Bool)) (k' : K) (b' : Bool),
      g (land p k' b') = click (g p) b') :
    recount (land prior k b) = click (recount prior) b
      ∧ audit board = (recount board, board.length)
      ∧ (audit (land prior k b)).2 = (audit prior).2 + 1
      ∧ g board = recount board :=
  ⟨the_landing_clicks_the_counter prior k b,
   the_recount_tolls_the_whole_record board,
   each_recount_costs_more_than_the_last prior k b,
   the_kept_counter_is_the_count g h0 hstep board⟩

/-- info: 'Foam.Counter.the_landing_clicks_the_counter' does not depend on any axioms -/
#guard_msgs in #print axioms the_landing_clicks_the_counter

/-- info: 'Foam.Counter.the_recount_tolls_the_whole_record' does not depend on any axioms -/
#guard_msgs in #print axioms the_recount_tolls_the_whole_record

/-- info: 'Foam.Counter.each_recount_costs_more_than_the_last' does not depend on any axioms -/
#guard_msgs in #print axioms each_recount_costs_more_than_the_last

/-- info: 'Foam.Counter.the_kept_counter_is_the_count' does not depend on any axioms -/
#guard_msgs in #print axioms the_kept_counter_is_the_count

/-- info: 'Foam.Counter.counter_counts_so_you_dont_have_to' does not depend on any axioms -/
#guard_msgs in #print axioms counter_counts_so_you_dont_have_to

end Foam.Counter
