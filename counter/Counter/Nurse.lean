import Counter.Telling

namespace Foam.Counter

def listSum : List Nat → Nat
  | [] => 0
  | w :: rest => w + listSum rest

def waitCost : List Nat → Nat
  | [] => 0
  | _ :: rest => listSum rest + waitCost rest

def UrgentFirst : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => b ≤ a ∧ UrgentFirst (b :: t)

theorem listSum_append (u v : List Nat) :
    listSum (u ++ v) = listSum u + listSum v := by
  induction u with
  | nil => exact (Nat.zero_add _).symm
  | cons x u ih =>
      show x + listSum (u ++ v) = (x + listSum u) + listSum v
      rw [ih, Nat.add_assoc]

theorem the_swap_reads_its_own_price (a b : Nat) (t : List Nat) :
    waitCost (a :: b :: t) + a = waitCost (b :: a :: t) + b := by
  show (b + listSum t) + (listSum t + waitCost t) + a
    = (a + listSum t) + (listSum t + waitCost t) + b
  rw [Nat.add_right_comm (b + listSum t) (listSum t + waitCost t) a,
    Nat.add_right_comm (a + listSum t) (listSum t + waitCost t) b,
    Nat.add_right_comm b (listSum t) a,
    Nat.add_right_comm a (listSum t) b,
    Nat.add_comm b a]

theorem the_swap_moves_no_sum (a b : Nat) (t : List Nat) :
    listSum (a :: b :: t) = listSum (b :: a :: t) := by
  show a + (b + listSum t) = b + (a + listSum t)
  rw [← Nat.add_assoc, Nat.add_comm a b, Nat.add_assoc]

theorem drop_the_common_wait : ∀ (k n m : Nat), n + k ≤ m + k → n ≤ m
  | 0, _, _, h => h
  | k + 1, n, m, h => drop_the_common_wait k n m (Nat.le_of_succ_le_succ h)

theorem urgent_first_never_loses (a b : Nat) (t : List Nat) (h : b ≤ a) :
    waitCost (a :: b :: t) ≤ waitCost (b :: a :: t) :=
  drop_the_common_wait b _ _
    (Nat.le_trans (Nat.add_le_add_left h (waitCost (a :: b :: t)))
      (Nat.le_of_eq (the_swap_reads_its_own_price a b t)))

theorem the_inversion_names_itself (a b : Nat) (t : List Nat) (h : a < b) :
    waitCost (b :: a :: t) < waitCost (a :: b :: t) := by
  have hid := the_swap_reads_its_own_price a b t
  have h1 : waitCost (b :: a :: t) + a < waitCost (b :: a :: t) + b :=
    Nat.add_lt_add_left h _
  rw [← hid] at h1
  exact Nat.lt_of_add_lt_add_right h1

theorem the_ward_hears_the_swap (u v : List Nat) (hsum : listSum u = listSum v)
    (hcost : waitCost u ≤ waitCost v) :
    ∀ pre : List Nat, waitCost (pre ++ u) ≤ waitCost (pre ++ v)
  | [] => hcost
  | x :: pre => by
      show listSum (pre ++ u) + waitCost (pre ++ u)
        ≤ listSum (pre ++ v) + waitCost (pre ++ v)
      rw [listSum_append, listSum_append, hsum]
      exact Nat.add_le_add_left (the_ward_hears_the_swap u v hsum hcost pre) _

theorem any_inversion_anywhere_is_legible (pre : List Nat) (a b : Nat)
    (t : List Nat) (h : b ≤ a) :
    waitCost (pre ++ a :: b :: t) ≤ waitCost (pre ++ b :: a :: t) :=
  the_ward_hears_the_swap (a :: b :: t) (b :: a :: t)
    (the_swap_moves_no_sum a b t) (urgent_first_never_loses a b t h) pre

theorem the_toy_ward_never_searches :
    waitCost [3, 2, 1] = 4
      ∧ waitCost [3, 2, 1] ≤ waitCost [3, 1, 2]
      ∧ waitCost [3, 2, 1] ≤ waitCost [2, 3, 1]
      ∧ waitCost [3, 2, 1] ≤ waitCost [2, 1, 3]
      ∧ waitCost [3, 2, 1] ≤ waitCost [1, 3, 2]
      ∧ waitCost [3, 2, 1] ≤ waitCost [1, 2, 3] :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

theorem the_nurses_round_is_read_not_searched (a b : Nat) (t pre : List Nat)
    (h : b ≤ a) :
    waitCost (a :: b :: t) + a = waitCost (b :: a :: t) + b
      ∧ waitCost (a :: b :: t) ≤ waitCost (b :: a :: t)
      ∧ waitCost (pre ++ a :: b :: t) ≤ waitCost (pre ++ b :: a :: t)
      ∧ waitCost [3, 2, 1] = 4
      ∧ waitCost [3, 2, 1] ≤ waitCost [1, 2, 3] :=
  ⟨the_swap_reads_its_own_price a b t,
   urgent_first_never_loses a b t h,
   any_inversion_anywhere_is_legible pre a b t h,
   rfl, by decide⟩

/-- info: 'Foam.Counter.listSum_append' does not depend on any axioms -/
#guard_msgs in #print axioms listSum_append

/-- info: 'Foam.Counter.the_swap_reads_its_own_price' does not depend on any axioms -/
#guard_msgs in #print axioms the_swap_reads_its_own_price

/-- info: 'Foam.Counter.the_swap_moves_no_sum' does not depend on any axioms -/
#guard_msgs in #print axioms the_swap_moves_no_sum

/-- info: 'Foam.Counter.drop_the_common_wait' does not depend on any axioms -/
#guard_msgs in #print axioms drop_the_common_wait

/-- info: 'Foam.Counter.urgent_first_never_loses' does not depend on any axioms -/
#guard_msgs in #print axioms urgent_first_never_loses

/-- info: 'Foam.Counter.the_inversion_names_itself' does not depend on any axioms -/
#guard_msgs in #print axioms the_inversion_names_itself

/-- info: 'Foam.Counter.the_ward_hears_the_swap' does not depend on any axioms -/
#guard_msgs in #print axioms the_ward_hears_the_swap

/-- info: 'Foam.Counter.any_inversion_anywhere_is_legible' does not depend on any axioms -/
#guard_msgs in #print axioms any_inversion_anywhere_is_legible

/-- info: 'Foam.Counter.the_toy_ward_never_searches' does not depend on any axioms -/
#guard_msgs in #print axioms the_toy_ward_never_searches

/-- info: 'Foam.Counter.the_nurses_round_is_read_not_searched' does not depend on any axioms -/
#guard_msgs in #print axioms the_nurses_round_is_read_not_searched

end Foam.Counter
