import Witness
open Room Face Witness
set_option autoImplicit false

namespace Game

structure World where
  weight : Nat
  hue : Nat
  heads : Nat

def weight : Nat := 0
def hue : Nat := 1
def heads : Nat := 2

def see (w : World) (p : Nat) : Nat :=
  cond (Nat.beq p weight) w.weight (cond (Nat.beq p hue) w.hue (cond (Nat.beq p heads) w.heads 0))

def worldFace : Face := ⟨World, Nat, Nat, see⟩

def firstGap (x y : World) : List Nat → Option Nat
  | [] => none
  | p :: ps => cond (Nat.beq (see x p) (see y p)) (firstGap x y ps) (some p)

def fuelToPart (x y : World) : List Nat → Nat
  | [] => 0
  | p :: ps => cond (Nat.beq (see x p) (see y p)) (fuelToPart x y ps + 1) 1

def room : List Nat := [weight, hue, heads]
def deaf : List Nat := [weight, heads]

def a : World := ⟨3, 5, 1⟩
def b : World := ⟨4, 5, 1⟩
def c : World := ⟨3, 6, 1⟩
def levelOne : door World Nat × door World Nat := (atTheDoor a 7, atTheDoor b 7)
def levelTwo : door World Nat × door World Nat := (atTheDoor a 7, atTheDoor a 9)
def levelThree : door World Nat × door World Nat := (atTheDoor a 7, atTheDoor a 7)
def levelFour : door World Nat × door World Nat := (atTheDoor a 7, atTheDoor c 7)
def levelOneGap : Option Nat := firstGap a b room
def levelOneFuel : Nat := fuelToPart a b room
def levelFourAtTheDeafSeat : Option Nat := firstGap a c deaf
def levelFourAtTheRoom : Option Nat := firstGap a c room
def levelFourFuel : Nat := fuelToPart a c room
def levelTwoAtTheRoom : Option Nat := firstGap a a room
def deafReadsA : List Nat := reads worldFace deaf a
def deafReadsC : List Nat := reads worldFace deaf c
def roomReadsA : List Nat := reads worldFace room a
def roomReadsC : List Nat := reads worldFace room c
def mirrorOfA : door Nat Nat := turnAbout (atTheDoor (3 : Nat) (3 : Nat))
def notAMirror : door Nat Nat := turnAbout (atTheDoor (3 : Nat) (5 : Nat))

#guard levelOneGap == some weight
#guard levelOneFuel == 1
#guard levelTwoAtTheRoom == none
#guard levelFourAtTheDeafSeat == none
#guard levelFourAtTheRoom == some hue
#guard levelFourFuel == 2
#guard deafReadsA == deafReadsC
#guard roomReadsA != roomReadsC
#guard face mirrorOfA == 3 && met mirrorOfA == 3
#guard face notAMirror == 5 && met notAMirror == 3

theorem level_one_is_timelike : ¬ alike worldFace a b :=
  fun h => absurd (h weight) (by show ¬ (see a weight = see b weight); decide)

theorem level_two_is_lightlike :
    alike (host worldFace Nat) (atTheDoor a 7) (atTheDoor a 9) ∧ ¬ alike (widen worldFace Nat) (atTheDoor a 7) (atTheDoor a 9) :=
  ⟨the_host_merges_the_guests worldFace Nat a 7 9, a_wider_seat_reads_the_remainder worldFace a (by decide)⟩

theorem level_three_is_spacelike : alike (widen worldFace Nat) (atTheDoor a 7) (atTheDoor a 7) := sorry

theorem level_four_is_a_wall_at_the_deaf_seat : reads worldFace deaf a = reads worldFace deaf c := sorry

theorem level_four_is_read_at_the_room : reads worldFace room a ≠ reads worldFace room c :=
  fun h => absurd (the_first_mark_reads (the_rest_reads h)) (by show ¬ (see a hue = see c hue); decide)

theorem the_engine_agrees_or_names_the_gap (x y : World) (seat : List Nat) :
    (∀ p, p ∈ seat → Nat.beq (see x p) (see y p) = true) ∨ ∃ p, p ∈ seat ∧ Nat.beq (see x p) (see y p) = false :=
  the_window_agrees_or_names_the_gap worldFace Nat.beq x y seat

theorem the_mirror (d : door Nat Nat) : turnAbout d = d ↔ met d = face d := sorry

theorem the_three_fates :
    ¬ alike worldFace a b
      ∧ (alike (host worldFace Nat) (atTheDoor a 7) (atTheDoor a 9) ∧ ¬ alike (widen worldFace Nat) (atTheDoor a 7) (atTheDoor a 9))
      ∧ alike (widen worldFace Nat) (atTheDoor a 7) (atTheDoor a 7) := sorry

def res3 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n + 3 => res3 n

def tick (d : door World Nat) : door World Nat :=
  atTheDoor ⟨(face d).weight + res3 (met d), (face d).hue, (face d).heads⟩ (met d + 1)

def after : Nat → door World Nat → door World Nat
  | 0, d => d
  | k + 1, d => after k (tick d)

def partsAt (d d' : door World Nat) (k : Nat) : Bool :=
  !(Nat.beq (see (face (after k d)) weight) (see (face (after k d')) weight))

def crossingWithin (d d' : door World Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | k, fuel + 1 => cond (partsAt d d' k) (some k) (crossingWithin d d' (k + 1) fuel)

def levelFive : door World Nat × door World Nat := (atTheDoor a 7, atTheDoor a 9)
def levelSix : door World Nat × door World Nat := (atTheDoor a 7, atTheDoor a 10)
def levelFiveCrossing : Option Nat := crossingWithin (atTheDoor a 7) (atTheDoor a 9) 0 12
def levelSixCrossing : Option Nat := crossingWithin (atTheDoor a 7) (atTheDoor a 10) 0 12
def levelFiveWeights : Nat × Nat := ((face (after 1 (atTheDoor a 7))).weight, (face (after 1 (atTheDoor a 9))).weight)

#guard levelFiveCrossing == some 1
#guard levelSixCrossing == none
#guard levelFiveWeights == (4, 3)
#guard partsAt (atTheDoor a 7) (atTheDoor a 10) 5 == false
#guard met (after 4 (atTheDoor a 7)) == 11

theorem level_five_parts_at_the_first_tick : partsAt (atTheDoor a 7) (atTheDoor a 9) 1 = true := sorry

theorem level_six_is_in_step_to_twelve : crossingWithin (atTheDoor a 7) (atTheDoor a 10) 0 12 = none := sorry

theorem the_two_secrets_are_alike_at_the_door : alike (host worldFace Nat) (atTheDoor a 7) (atTheDoor a 10) := sorry

theorem the_tick_hears_the_secret_only_as_a_residue (w : World) (s : Nat) :
    face (tick (atTheDoor w s)) = face (tick (atTheDoor w (s + 3))) := sorry

end Game
