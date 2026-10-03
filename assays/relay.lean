import Face
open Room Face
set_option autoImplicit false

namespace Relay

def stage (σ : List Bool → List Bool) (d : door Nat (List Bool)) : door Nat (List Bool) :=
  vertical (fun d => σ (met d)) d

def relay (stages : List (List Bool → List Bool)) : door Nat (List Bool) → door Nat (List Bool)
  | d => stages.foldl (fun d σ => stage σ d) d

def erase (s : List Bool) : List Bool := zeros s.length

def signal : List Bool := [true, false, true, true]
def sent : door Nat (List Bool) := atTheDoor (0 : Nat) signal
def throughOdometer : door Nat (List Bool) := relay [inc, inc, inc] sent
def recovered : List Bool := again dec 3 (met throughOdometer)
def throughErase : door Nat (List Bool) := relay [inc, erase] sent
def otherSignal : List Bool := [false, false, true, true]
def throughEraseOther : door Nat (List Bool) := relay [inc, erase] (atTheDoor (0 : Nat) otherSignal)
def faceSent : Nat := face sent
def faceArrived : Nat := face throughOdometer

#guard faceArrived == faceSent
#guard met throughOdometer != signal
#guard recovered == signal
#guard met throughErase == met throughEraseOther
#guard signal != otherSignal

theorem the_relay_is_unheard_at_the_face (σ : List Bool → List Bool) (d : door Nat (List Bool)) :
    alike (host (originFace Nat) (List Bool)) (stage σ d) d := sorry

theorem the_odometer_stage_has_a_section (s : List Bool) : dec (inc s) = s := sorry

theorem the_signal_is_recovered : again dec 3 (met throughOdometer) = signal := sorry

theorem the_erasing_stage_merges : met throughErase = met throughEraseOther ∧ signal ≠ otherSignal := sorry

theorem no_section_recovers_the_erased (r : List Bool → List Bool) (hr : ∀ s, r (erase s) = s) : False :=
  a_merging_map_has_no_section erase (s := signal) (s' := otherSignal) (by decide) (by decide) r hr

def helloWorld : List Bool := [true, false, false, true, false, true, true, false]
def playedBack : List Bool := behavior (replayer (ledger Bool)) helloWorld
def theRouteKept : List Bool := park (replayer (ledger Bool)) [] helloWorld

#guard playedBack == helloWorld
#guard theRouteKept == helloWorld
#guard theRouteKept.length == helloWorld.length

theorem the_replayer_parks_the_word {I O : Type} (m : Machine.{0, 0, 0} I O) :
    ∀ (ws rec : List I), park (replayer m) rec ws = rec ++ ws := sorry

theorem the_identity_relay_keeps_its_route (w : List Bool) :
    behavior (replayer (ledger Bool)) w = behavior (ledger Bool) w ∧ park (replayer (ledger Bool)) [] w = w :=
  ⟨the_replay_is_the_machine (ledger Bool) w, the_replayer_parks_the_word (ledger Bool) w []⟩

end Relay
