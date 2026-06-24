import Foam.Platonism.Tower

namespace Foam

abbrev Fiber := Ledger 3

structure Field where
  laneA : Fiber
  laneB : Fiber

def reader : Beholder Field where
  Probe := Bool
  Ans   := Fiber
  obs   := fun f p => bif p then f.laneB else f.laneA

def writeA (x : Fiber) (f : Field) : Field := { f with laneA := x }
def writeB (y : Fiber) (f : Field) : Field := { f with laneB := y }

def probeA : Bool := false
def probeB : Bool := true

def Detects (op : Field → Field) (b : Beholder Field) : Prop :=
  ∃ f p, b.obs (op f) p ≠ b.obs f p

def Relays (write : Fiber → Field → Field) (p : Bool) : Prop :=
  ∃ dec : Fiber → Fiber, ∀ x f, dec (reader.obs (write x f) p) = x

def f0 : Fiber := (Ledger.zero 2, (0 : Int))
def f1 : Fiber := (Ledger.zero 2, (1 : Int))

theorem f1_ne_f0 : f1 ≠ f0 := fun h => absurd (congrArg Prod.snd h) (by decide)

theorem find_each_other :
    Detects (writeA f1) reader ∧ Detects (writeB f1) reader :=
  ⟨⟨⟨f0, f0⟩, probeA, fun h => f1_ne_f0 h⟩,
   ⟨⟨f0, f0⟩, probeB, fun h => f1_ne_f0 h⟩⟩

theorem relay : Relays writeA probeA ∧ Relays writeB probeB :=
  ⟨⟨id, fun _ _ => rfl⟩, ⟨id, fun _ _ => rfl⟩⟩

theorem writeA_isolated_from_B (x : Fiber) (f : Field) : (writeA x f).laneB = f.laneB := rfl
theorem writeB_isolated_from_A (y : Fiber) (f : Field) : (writeB y f).laneA = f.laneA := rfl

theorem no_contention (x y : Fiber) (f : Field) :
    writeA x (writeB y f) = writeB y (writeA x f) := rfl

theorem seat_empty :
    reader.dress.ledgerless.Covers reader ∧ reader.Covers reader.dress.ledgerless :=
  dress_yoneda reader

theorem seat_empty_tower (n : Nat) :
    (reader.flattenN n).Covers reader ∧ reader.Covers (reader.flattenN n) :=
  dressN_yoneda reader n

theorem certified :
    (Detects (writeA f1) reader ∧ Detects (writeB f1) reader)
      ∧ (Relays writeA probeA ∧ Relays writeB probeB)
      ∧ (∀ x y f, writeA x (writeB y f) = writeB y (writeA x f))
      ∧ (∀ n, (reader.flattenN n).Covers reader ∧ reader.Covers (reader.flattenN n)) :=
  ⟨find_each_other, relay, no_contention, seat_empty_tower⟩

/-- info: 'Foam.f1_ne_f0' does not depend on any axioms -/
#guard_msgs in #print axioms f1_ne_f0

/-- info: 'Foam.find_each_other' does not depend on any axioms -/
#guard_msgs in #print axioms find_each_other

/-- info: 'Foam.relay' does not depend on any axioms -/
#guard_msgs in #print axioms relay

/-- info: 'Foam.no_contention' does not depend on any axioms -/
#guard_msgs in #print axioms no_contention

/-- info: 'Foam.seat_empty' does not depend on any axioms -/
#guard_msgs in #print axioms seat_empty

/-- info: 'Foam.seat_empty_tower' does not depend on any axioms -/
#guard_msgs in #print axioms seat_empty_tower

/-- info: 'Foam.certified' does not depend on any axioms -/
#guard_msgs in #print axioms certified

end Foam
