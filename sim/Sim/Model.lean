import Foam.Seat.Quiver
import Foam.Ledger

namespace Foam.Sim

structure Actor where
  id : Nat
  name : String
  parent : Option Nat
  deriving DecidableEq, Repr

structure Act where
  id : Nat
  actor : Nat
  position : Nat
  verb : String
  src : String
  dst : String
  deriving DecidableEq, Repr

structure Model where
  name : String
  actors : List Actor
  acts : List Act
  deriving DecidableEq, Repr

def Model.quiver (m : Model) : Foam.Quiver String :=
  m.acts.map (fun a => (a.src, a.dst))

def Model.own (m : Model) (actorId : Nat) : List Act :=
  m.acts.filter (fun a => a.actor == actorId)

def insertByPos (a : Act) : List Act → List Act
  | [] => [a]
  | b :: rest =>
    if a.position ≤ b.position then a :: b :: rest else b :: insertByPos a rest

def Model.composed (m : Model) : List Act :=
  m.acts.foldr insertByPos []

theorem own_is_a_filter (m : Model) (actorId : Nat) :
    m.own actorId = m.acts.filter (fun a => a.actor == actorId) := rfl

theorem the_quiver_is_a_reading (m : Model) :
    m.quiver = m.acts.map (fun a => (a.src, a.dst)) := rfl

/-- info: 'Foam.Sim.own_is_a_filter' does not depend on any axioms -/
#guard_msgs in #print axioms own_is_a_filter

/-- info: 'Foam.Sim.the_quiver_is_a_reading' does not depend on any axioms -/
#guard_msgs in #print axioms the_quiver_is_a_reading

end Foam.Sim
