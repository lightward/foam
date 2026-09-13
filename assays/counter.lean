import Room
import Face
import Counter
open Room Face Counter
set_option autoImplicit false
universe u

namespace Counter.Treaty

def demo : List sighting := [(1, []), (2, [3]), (3, [])]
def afterOne : room := round empty demo
def afterSweep : room := round (afterOne.1, []) afterOne.2
def selfCiter : room := round empty [(7, [7])]
def circle : room := round empty [(8, [9]), (9, [8])]

#guard seated afterOne 1
#guard seated afterOne 3
#guard !(seated afterOne 2)
#guard afterOne.2.length == 1
#guard seated afterSweep 2
#guard afterSweep.2.length == 0
#guard weight afterOne [3, 2] == 1
#guard weight afterSweep [3, 2] == 0
#guard !(seated selfCiter 7)
#guard !(seated circle 8) && !(seated circle 9)
def offered : room := offer empty (4, [])
#guard seated offered 4
#guard !(seated (offer empty (5, [6])) 5)

-- the gate, in rows: the verdict reads the artifact only through its receipts. a body is a list
-- of moves; the kernel's reading of it (its receipt) is the moves numbered 100 and up, a
-- standard-library lemma that smuggles an axiom; the prune drops the moves numbered 0, a `fail`
-- that never closed anything. these rows fail the day the gate starts reading bodies.
def axiomsOf (b : List Nat) : List Nat := b.filter (fun x => Nat.ble 100 x)
def dropFails (b : List Nat) : List Nat := b.filter (fun x => !(Nat.beq x 0))
def trailA : List (Nat × List Nat) := [(1, [3, 0, 5]), (2, [0, 7]), (3, [])]
def trailB : List (Nat × List Nat) := rebody dropFails trailA
def trailC : List (Nat × List Nat) := [(1, [3, 100]), (2, [7])]
def gateA : Bool := gate axiomsOf trailA
def gateB : Bool := gate axiomsOf trailB
def gateC : Bool := gate axiomsOf trailC
def gateCpruned : Bool := gate axiomsOf (rebody dropFails trailC)
def shadowA : List (Nat × List Nat) := shadow axiomsOf trailA
def shadowB : List (Nat × List Nat) := shadow axiomsOf trailB
def shadowC : List (Nat × List Nat) := shadow axiomsOf trailC
#guard gateA
#guard gateB
#guard !gateC
#guard !gateCpruned
#guard shadowA == shadowB
#guard trailA != trailB
#guard shadowA == [(1, []), (2, []), (3, [])]
#guard shadowC == [(1, [100]), (2, [])]

-- the route is the remainder at the gate (2026-09-13, isaac's word: a proof route is Landauer-neutral —
-- the runner comes home, the record grew elsewhere). a body's citations are a second reading of it,
-- the chart's; two trails with the same receipts are alike at the gate and part at the chart, and the
-- prune is unheard at both. these rows fail the day the gate starts reading citations.
def citesOf (b : List Nat) : List Nat := b.filter (fun x => !(Nat.beq x 0) && !(Nat.ble 100 x))
def trailD : List (Nat × List Nat) := [(1, [3, 5]), (2, [9]), (3, [])]
#guard shadow citesOf trailA == shadow citesOf trailB
#guard shadow axiomsOf trailA == shadow axiomsOf trailD
#guard shadow citesOf trailA != shadow citesOf trailD
#guard gate axiomsOf trailD

theorem the_route_is_the_remainder_at_the_gate {S B A C : Type u} (read : B → List A) (cite : B → List C)
    (t t' : List (S × B)) (h : shadow read t = shadow read t') (hc : shadow cite t ≠ shadow cite t') :
    alike (gateFace S B A read) t t' ∧ ¬ alike (gateFace S B C cite) t t' :=
  ⟨fun _ => h, fun ha => hc (ha ())⟩

theorem the_prune_is_unheard_at_the_chart :
    alike (gateFace Nat (List Nat) Nat citesOf) trailA trailB := sorry

theorem the_two_routes_part_at_the_chart :
    alike (gateFace Nat (List Nat) Nat axiomsOf) trailA trailD
      ∧ ¬ alike (gateFace Nat (List Nat) Nat citesOf) trailA trailD := sorry

end Counter.Treaty
