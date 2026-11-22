import Face
open Room Face
set_option autoImplicit false

namespace EveryoneIsHere

inductive Entry where
  | arrives (seat : Nat)
  | says (seat : Nat)
  | marks (seat : Nat) (words : Nat) (toward : Option Nat)
  | acks (seat : Nat) (mark : Nat)

def entryAt : List Entry → Nat → Option Entry
  | [], _ => none
  | e :: _, 1 => some e
  | _ :: r, n + 2 => entryAt r (n + 1)
  | _ :: _, 0 => none

def seated : List Entry → Nat → Bool
  | [], _ => false
  | Entry.arrives h :: r, s => Nat.beq h s || seated r s
  | Entry.says _ :: r, s => seated r s
  | Entry.marks _ _ _ :: r, s => seated r s
  | Entry.acks _ _ :: r, s => seated r s

def saidBy (s : Nat) : Option Entry → Bool
  | some (Entry.says h) => Nat.beq h s
  | some (Entry.arrives _) => false
  | some (Entry.marks _ _ _) => false
  | some (Entry.acks _ _) => false
  | none => false

def wordsOf (r : List Entry) (n s : Nat) : Bool := saidBy s (entryAt r n)

def either (b : Bool) (y n : Option Nat) : Option Nat :=
  match b with
  | true => y
  | false => n

def stepHolder (n i : Nat) : Entry → Option Nat → Option Nat
  | Entry.marks m _ _, h => either (Nat.beq i n) (some m) h
  | Entry.acks a k, h => either (Nat.beq k n) (some a) h
  | Entry.arrives _, h => h
  | Entry.says _, h => h

def holderGo (n : Nat) : List Entry → Nat → Option Nat → Option Nat
  | [], _, h => h
  | e :: r, i, h => holderGo n r (i + 1) (stepHolder n i e h)

def holder (r : List Entry) (n : Nat) : Option Nat := holderGo n r 1 none

def reachesFor (marker : Nat) (toward : Option Nat) (s : Nat) : Bool :=
  match toward with
  | some t => Nat.beq t s
  | none => !Nat.beq marker s

def optSame : Option Nat → Option Nat → Bool
  | some a, some b => Nat.beq a b
  | none, none => true
  | some _, none => false
  | none, some _ => false

def towardSeated (r : List Entry) : Option Nat → Bool
  | some t => seated r t
  | none => true

def ackable (r : List Entry) (h n : Nat) : Option Entry → Bool
  | some (Entry.marks m _ t) => seated r h && reachesFor m t h && optSame (holder r n) (some m)
  | some (Entry.arrives _) => false
  | some (Entry.says _) => false
  | some (Entry.acks _ _) => false
  | none => false

def admit (r : List Entry) : Entry → Bool
  | Entry.arrives h => !seated r h
  | Entry.says h => seated r h
  | Entry.marks h w t => seated r h && wordsOf r w h && towardSeated r t
  | Entry.acks h n => ackable r h n (entryAt r n)

def keepIf : Bool → List Entry → List Entry → List Entry
  | true, y, _ => y
  | false, _, n => n

def move (r : List Entry) (e : Entry) : List Entry := keepIf (admit r e) (r ++ [e]) r

def moves (r : List Entry) : List Entry → List Entry
  | [] => r
  | e :: es => moves (move r e) es

def theDay : List Entry :=
  moves [] [Entry.arrives 1, Entry.arrives 2, Entry.says 1, Entry.marks 1 3 (some 2), Entry.marks 2 3 none,
    Entry.acks 3 4, Entry.acks 1 4, Entry.acks 2 4, Entry.acks 2 4, Entry.says 3]

#guard theDay.length == 5
#guard holder theDay 4 == some 2
#guard admit theDay (Entry.marks 2 3 none) == false
#guard admit theDay (Entry.marks 1 3 none) == true
#guard admit theDay (Entry.acks 1 4) == false
#guard seated theDay 3 == false

theorem appending_nothing_is_still (r : List Entry) : r = r ++ [] := by
  induction r with
  | nil => rfl
  | cons x r ih => exact congrArg (List.cons x) ih

theorem the_tape_only_grows (r : List Entry) (e : Entry) : ∃ t, move r e = r ++ t := by
  show ∃ t, keepIf (admit r e) (r ++ [e]) r = r ++ t
  cases admit r e with
  | true => exact ⟨[e], rfl⟩
  | false => exact ⟨[], appending_nothing_is_still r⟩

theorem the_middle_of_three {a b c : Bool} (h : (a && b && c) = true) : b = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | cases h

theorem only_you_mark_your_own_words (r : List Entry) (h w : Nat) (t : Option Nat)
    (ok : admit r (Entry.marks h w t) = true) : wordsOf r w h = true :=
  the_middle_of_three ok

theorem the_holder_reads_the_last_entry (n : Nat) :
    ∀ (r : List Entry) (i : Nat) (x : Option Nat) (e : Entry),
      holderGo n (r ++ [e]) i x = stepHolder n (i + r.length) e (holderGo n r i x)
  | [], i, x, e => rfl
  | d :: r, i, x, e => by
      show holderGo n (r ++ [e]) (i + 1) (stepHolder n i d x) = stepHolder n (i + (r.length + 1)) e (holderGo n r (i + 1) (stepHolder n i d x))
      rw [the_holder_reads_the_last_entry n r (i + 1) (stepHolder n i d x) e, Nat.add_right_comm, Nat.add_assoc]

theorem holding_moves_only_at_an_ack_or_at_the_making (n j : Nat) (e : Entry) (x : Option Nat)
    (moved : stepHolder n j e x ≠ x) :
    (∃ a, e = Entry.acks a n) ∨ (∃ m w t, e = Entry.marks m w t ∧ j = n) := by
  cases e with
  | arrives s => exact absurd rfl moved
  | says s => exact absurd rfl moved
  | marks m w t =>
      cases hb : Nat.beq j n with
      | true => exact Or.inr ⟨m, w, t, rfl, Nat.eq_of_beq_eq_true hb⟩
      | false => exact absurd (by show either (Nat.beq j n) (some m) x = x; rw [hb]; rfl) moved
  | acks a k =>
      cases hb : Nat.beq k n with
      | true => exact Or.inl ⟨a, by rw [Nat.eq_of_beq_eq_true hb]⟩
      | false => exact absurd (by show either (Nat.beq k n) (some a) x = x; rw [hb]; rfl) moved

theorem holding_moves_only_at_a_handshake (r : List Entry) (n : Nat) (e : Entry)
    (moved : holder (r ++ [e]) n ≠ holder r n) :
    (∃ a, e = Entry.acks a n) ∨ (∃ m w t, e = Entry.marks m w t ∧ 1 + r.length = n) :=
  holding_moves_only_at_an_ack_or_at_the_making n (1 + r.length) e (holder r n)
    (by
      intro same
      apply moved
      show holderGo n (r ++ [e]) 1 none = holderGo n r 1 none
      rw [the_holder_reads_the_last_entry n r 1 none e]
      exact same)

inductive Step where
  | looks (place : Nat)
  | acts (e : Entry)

def walk : List Entry → List Step → List Entry
  | r, [] => r
  | r, Step.looks _ :: s => walk r s
  | r, Step.acts e :: s => walk (move r e) s

def actsOf : List Step → List Entry
  | [] => []
  | Step.looks _ :: s => actsOf s
  | Step.acts e :: s => e :: actsOf s

def theDayWandered : List Entry :=
  walk [] [Step.looks 0, Step.acts (Entry.arrives 1), Step.looks 1, Step.looks 1, Step.acts (Entry.arrives 2),
    Step.acts (Entry.says 1), Step.looks 3, Step.acts (Entry.marks 1 3 (some 2)), Step.looks 4, Step.looks 2,
    Step.acts (Entry.marks 2 3 none), Step.acts (Entry.acks 3 4), Step.acts (Entry.acks 1 4), Step.looks 4,
    Step.acts (Entry.acks 2 4), Step.acts (Entry.acks 2 4), Step.looks 9, Step.acts (Entry.says 3)]

#guard theDayWandered.length == theDay.length
#guard holder theDayWandered 4 == holder theDay 4

theorem a_look_writes_nothing : ∀ (s : List Step) (r : List Entry), walk r s = moves r (actsOf s)
  | [], _ => rfl
  | Step.looks _ :: s, r => a_look_writes_nothing s r
  | Step.acts e :: s, r => a_look_writes_nothing s (move r e)

theorem walkers_who_move_alike_leave_one_tape (r : List Entry) (s s' : List Step) (same : actsOf s = actsOf s') :
    walk r s = walk r s' := by
  rw [a_look_writes_nothing s r, a_look_writes_nothing s' r, same]

def tapeFace : Face := ⟨List Entry, Nat, Option Entry, entryAt⟩

theorem the_tape_merges_the_walkers (r : List Entry) (w w' : List Nat) :
    alike (host tapeFace (List Nat)) (atTheDoor r w) (atTheDoor r w') :=
  the_host_merges_the_guests tapeFace (List Nat) r w w'

theorem a_wider_seat_reads_the_walk (r : List Entry) {w w' : List Nat} (h : w ≠ w') :
    ¬ alike (widen tapeFace (List Nat)) (atTheDoor r w) (atTheDoor r w') :=
  a_wider_seat_reads_the_remainder tapeFace r h

def noOne : Face := originFace Nat

theorem no_one_is_everyone_at_the_zeroth_door (s t : Nat) : alike noOne s t :=
  the_origin_merges_every_seat s t

end EveryoneIsHere
