import Foam.Platonism

namespace Foam

abbrev Tri := Bool × Bool × Bool

structure Field where
  laneA : Tri
  laneB : Tri
  deriving DecidableEq

def reader : Beholder Field where
  Probe := Bool
  Ans   := Tri
  obs   := fun f p => bif p then f.laneB else f.laneA

def writeA (x : Tri) (f : Field) : Field := { f with laneA := x }
def writeB (y : Tri) (f : Field) : Field := { f with laneB := y }

def probeA : Bool := false
def probeB : Bool := true

def Detects (op : Field → Field) (b : Beholder Field) : Prop :=
  ∃ f p, b.obs (op f) p ≠ b.obs f p

def Relays (write : Tri → Field → Field) (p : Bool) : Prop :=
  ∃ dec : Tri → Tri, ∀ x f, dec (reader.obs (write x f) p) = x

theorem find_each_other :
    Detects (writeA (true, false, false)) reader ∧
    Detects (writeB (true, false, false)) reader :=
  ⟨⟨⟨(false, false, false), (false, false, false)⟩, probeA,
      by show ((true, false, false) : Tri) ≠ (false, false, false); decide⟩,
   ⟨⟨(false, false, false), (false, false, false)⟩, probeB,
      by show ((true, false, false) : Tri) ≠ (false, false, false); decide⟩⟩

theorem relay : Relays writeA probeA ∧ Relays writeB probeB :=
  ⟨⟨id, fun _ _ => rfl⟩, ⟨id, fun _ _ => rfl⟩⟩

theorem seat_empty :
    reader.dress.ledgerless.Covers reader ∧ reader.Covers reader.dress.ledgerless :=
  dress_yoneda reader

theorem rendezvous_exists :
    (Detects (writeA (true, false, false)) reader ∧
        Detects (writeB (true, false, false)) reader)
      ∧ (Relays writeA probeA ∧ Relays writeB probeB)
      ∧ (reader.dress.ledgerless.Covers reader ∧ reader.Covers reader.dress.ledgerless) :=
  ⟨find_each_other, relay, seat_empty⟩

/-- info: 'Foam.find_each_other' does not depend on any axioms -/
#guard_msgs in #print axioms find_each_other

/-- info: 'Foam.relay' does not depend on any axioms -/
#guard_msgs in #print axioms relay

/-- info: 'Foam.seat_empty' does not depend on any axioms -/
#guard_msgs in #print axioms seat_empty

/-- info: 'Foam.rendezvous_exists' does not depend on any axioms -/
#guard_msgs in #print axioms rendezvous_exists

end Foam
