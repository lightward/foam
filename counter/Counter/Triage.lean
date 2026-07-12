import Counter.Nurse

namespace Foam.Counter

def triageA : Render (coin.prod dial) Nat :=
  ⟨family, (), fun a => cond a 1 0⟩

def triageB : Render (coin.prod dial) Nat :=
  ⟨bloomed, (), fun a => cond a 1 0⟩

def linkCost : List Nat → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: t => a * b + linkCost (b :: t)

theorem triage_is_a_seat :
    triageA.read (true, (4 : Nat)) = 1
      ∧ triageA.read (false, (2 : Nat)) = 0
      ∧ triageB.read (true, (4 : Nat)) = 0
      ∧ triageB.read (false, (2 : Nat)) = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem the_round_follows_the_seat :
    waitCost ([(true, (4 : Nat)), (false, (2 : Nat))].map triageA.read)
        < waitCost ([(false, (2 : Nat)), (true, (4 : Nat))].map triageA.read)
      ∧ waitCost ([(false, (2 : Nat)), (true, (4 : Nat))].map triageB.read)
        < waitCost ([(true, (4 : Nat)), (false, (2 : Nat))].map triageB.read) :=
  ⟨by decide, by decide⟩

theorem the_object_price_is_read_at_the_pair (v : Render (coin.prod dial) Nat)
    (w₁ w₂ : (coin.prod dial).State) (beds : List (coin.prod dial).State) :
    waitCost ((w₁ :: w₂ :: beds).map v.read) + v.read w₁
      = waitCost ((w₂ :: w₁ :: beds).map v.read) + v.read w₂ :=
  the_swap_reads_its_own_price (v.read w₁) (v.read w₂) (beds.map v.read)

theorem the_relational_price_lives_in_the_context :
    linkCost [1, 3, 2] = linkCost [1, 2, 3] + 1
      ∧ linkCost [10, 3, 2] = linkCost [10, 2, 3] + 10 :=
  ⟨rfl, rfl⟩

theorem urgency_is_a_render (v : Render (coin.prod dial) Nat)
    (w₁ w₂ : (coin.prod dial).State) (beds : List (coin.prod dial).State) :
    (triageA.read (true, (4 : Nat)) = 1 ∧ triageB.read (true, (4 : Nat)) = 0)
      ∧ waitCost ((w₁ :: w₂ :: beds).map v.read) + v.read w₁
          = waitCost ((w₂ :: w₁ :: beds).map v.read) + v.read w₂
      ∧ linkCost [1, 3, 2] = linkCost [1, 2, 3] + 1
      ∧ linkCost [10, 3, 2] = linkCost [10, 2, 3] + 10 :=
  ⟨⟨rfl, rfl⟩, the_object_price_is_read_at_the_pair v w₁ w₂ beds,
   rfl, rfl⟩

/-- info: 'Foam.Counter.triage_is_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms triage_is_a_seat

/-- info: 'Foam.Counter.the_round_follows_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_round_follows_the_seat

/-- info: 'Foam.Counter.the_object_price_is_read_at_the_pair' does not depend on any axioms -/
#guard_msgs in #print axioms the_object_price_is_read_at_the_pair

/-- info: 'Foam.Counter.the_relational_price_lives_in_the_context' does not depend on any axioms -/
#guard_msgs in #print axioms the_relational_price_lives_in_the_context

/-- info: 'Foam.Counter.urgency_is_a_render' does not depend on any axioms -/
#guard_msgs in #print axioms urgency_is_a_render

end Foam.Counter
