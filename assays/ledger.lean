import Face
open Room Face
set_option autoImplicit false

namespace Ledger

def give (l : List (Nat × Nat)) (a b k : Nat) : List (Nat × Nat) :=
  l.map (fun e => cond (Nat.beq e.1 a) (e.1, e.2 - k) (cond (Nat.beq e.1 b) (e.1, e.2 + k) e))

def total : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => e.2 + total l

def held (l : List (Nat × Nat)) (a : Nat) : Nat := total (l.filter (fun e => Nat.beq e.1 a))

def totalFace : Face := ⟨List (Nat × Nat), Unit, Nat, fun l _ => total l⟩

def seatsFace : Face := ⟨List (Nat × Nat), Nat, Nat, fun l a => held l a⟩

def isaac : Nat := 1
def abe : Nat := 2
def rose : Nat := 3
def books : List (Nat × Nat) := [(isaac, 10), (abe, 5), (rose, 0)]
def afterGift : List (Nat × Nat) := give books isaac rose 4
def afterTwo : List (Nat × Nat) := give afterGift rose abe 2
def totalBefore : Nat := total books
def totalAfter : Nat := total afterGift
def totalAfterTwo : Nat := total afterTwo

#guard totalBefore == 15
#guard totalAfter == totalBefore
#guard totalAfterTwo == totalBefore
#guard held afterGift isaac == 6
#guard held afterGift rose == 4
#guard held afterGift abe == 5
#guard held afterTwo abe == 7
#guard held afterTwo rose == 2
#guard afterGift != books

theorem the_gift_is_unheard_at_the_total : alike totalFace afterGift books := sorry

theorem the_gift_is_heard_at_a_seat : ¬ alike seatsFace afterGift books :=
  fun h => absurd (h isaac) (by show ¬ (held afterGift isaac = held books isaac); decide)

theorem the_handshake_at_the_books :
    alike totalFace afterGift books ∧ ¬ alike seatsFace afterGift books ∧ alike totalFace afterTwo books := sorry

end Ledger
