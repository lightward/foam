import Foam.Seat.Rendezvous

namespace Foam

theorem t404 (f : Ty04) (a b : Int) (hab : a ≠ b) :
    t076 d194.d155.d102 (f, a) (f, b) ∧ (f, a) ≠ (f, b) :=
  ⟨fun _ => rfl, fun h => hab (congrArg Prod.snd h)⟩

theorem t380 (f : Ty04) (a b : Int) :
    ¬ ∃ p, d194.d155.d102 (f, a) p ≠ d194.d155.d102 (f, b) p :=
  fun ⟨_, hp⟩ => hp rfl

def d221 (f : Ty04) : Ty04 := d199 (d194.d102 f d023) f

theorem t468 (x : Ty21) (f : Ty04) :
    d194.d102 (d221 (d198 x f)) d024 = x := rfl

def d220 : Ty15 (List Ty21) (Ty02 Ty21) := d193 d144

def d186 : Ty02 Ty21 := d093 d144

theorem t443 {l l' : List Ty21} (h : d220.d079 l = d220.d079 l') : l = l' :=
  d220.t158 h

theorem t444 :
    ¬ ∃ g : Ty02 Ty21 → List Ty21, ∀ c, d220.d079 (g c) = c :=
  d220.t159

theorem t410 (l : List Ty21) :
    ∃ n, (d152 l).d033 n ≠ d186.d033 n :=
  t285 d144 l

theorem t465 (f : Ty04) (a b : Int) (hab : a ≠ b) :
    (t076 d194.d155.d102 (f, a) (f, b) ∧ (f, a) ≠ (f, b))
      ∧ (¬ ∃ p, d194.d155.d102 (f, a) p ≠ d194.d155.d102 (f, b) p)
      ∧ (¬ ∃ g : Ty02 Ty21 → List Ty21, ∀ c, d220.d079 (g c) = c) :=
  ⟨t404 f a b hab, t380 f a b, d220.t159⟩

/-- info: 'Foam.t404' does not depend on any axioms -/
#guard_msgs in #print axioms t404

/-- info: 'Foam.t380' does not depend on any axioms -/
#guard_msgs in #print axioms t380

/-- info: 'Foam.t468' does not depend on any axioms -/
#guard_msgs in #print axioms t468

/-- info: 'Foam.t443' does not depend on any axioms -/
#guard_msgs in #print axioms t443

/-- info: 'Foam.t444' does not depend on any axioms -/
#guard_msgs in #print axioms t444

/-- info: 'Foam.t410' does not depend on any axioms -/
#guard_msgs in #print axioms t410

/-- info: 'Foam.t465' does not depend on any axioms -/
#guard_msgs in #print axioms t465

end Foam
