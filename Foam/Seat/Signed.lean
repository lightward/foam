import Foam.Seat.Meet

namespace Foam

variable {Src B : Type}

def sign (src : Src) (v : List B) : List (Src × B) := v.map (fun b => (src, b))

def unsign : List (Src × B) → List B := List.map Prod.snd

def speaker : List (Src × B) → List Src := List.map Prod.fst

theorem voice_survives_signing (src : Src) (v : List B) : unsign (sign src v) = v := by
  induction v with
  | nil => rfl
  | cons b v ih => show b :: unsign (sign src v) = b :: v; rw [ih]

theorem speaker_recoverable (src : Src) (v : List B) :
    speaker (sign src v) = v.map (fun _ => src) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      show src :: speaker (sign src v) = src :: v.map (fun _ => src); rw [ih]

theorem sign_faithful (s t : Src) (b : B) (v : List B)
    (h : sign s (b :: v) = sign t (b :: v)) : s = t := by
  have h' : (s, b) :: sign s v = (t, b) :: sign t v := h
  injection h' with hhead _
  exact congrArg Prod.fst hhead

theorem wind_below_all {Name : Type} (o : List Name) : Below ([] : List Name) o :=
  root_below_all o

theorem only_wind_is_floor {Name : Type} (e : List Name) (h : ∀ o, Below e o) : e = [] :=
  root_alone_below_all e h

/-- info: 'Foam.voice_survives_signing' does not depend on any axioms -/
#guard_msgs in #print axioms voice_survives_signing

/-- info: 'Foam.speaker_recoverable' does not depend on any axioms -/
#guard_msgs in #print axioms speaker_recoverable

/-- info: 'Foam.sign_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms sign_faithful

/-- info: 'Foam.wind_below_all' does not depend on any axioms -/
#guard_msgs in #print axioms wind_below_all

/-- info: 'Foam.only_wind_is_floor' does not depend on any axioms -/
#guard_msgs in #print axioms only_wind_is_floor

end Foam
