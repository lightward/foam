import Foam.Seat.Sed

namespace Foam

def Ty13 : Nat → Type
  | 0 => Ty05
  | n + 1 => Ty13 n × Ty13 n

def Ty13.d074 : (n : Nat) → Ty13 n
  | 0 => Foam.Ty05.d044
  | n + 1 => (Foam.Ty13.d074 n, Foam.Ty13.d074 n)

def Ty13.d066 : (n : Nat) → Ty13 n → Ty13 n → Ty13 n
  | 0, a, b => Foam.Ty05.d108 a b
  | n + 1, x, y => (Foam.Ty13.d066 n x.1 y.1, Foam.Ty13.d066 n x.2 y.2)

def Ty13.d070 : (n : Nat) → Ty13 n → Ty13 n
  | 0, a => ⟨-a.d043, -a.d041⟩
  | n + 1, x => (Foam.Ty13.d070 n x.1, Foam.Ty13.d070 n x.2)

def Ty13.d128 (n : Nat) (x y : Ty13 n) : Ty13 n :=
  Foam.Ty13.d066 n x (Foam.Ty13.d070 n y)

def Ty13.d067 : (n : Nat) → Ty13 n → Ty13 n
  | 0, a => Foam.Ty05.d110 a
  | n + 1, x => (Foam.Ty13.d067 n x.1, Foam.Ty13.d070 n x.2)

def Ty13.d069 : (n : Nat) → Ty13 n → Ty13 n → Ty13 n
  | 0, a, b => Foam.Ty05.d112 a b
  | n + 1, x, y =>
    (Foam.Ty13.d128 n (Foam.Ty13.d069 n x.1 y.1) (Foam.Ty13.d069 n (Foam.Ty13.d067 n y.2) x.2),
     Foam.Ty13.d066 n (Foam.Ty13.d069 n y.2 x.1) (Foam.Ty13.d069 n x.2 (Foam.Ty13.d067 n y.1)))

def Ty13.d071 : (n : Nat) → Ty13 n → Int
  | 0, a => Foam.Ty05.d114 a
  | n + 1, x => Foam.Ty13.d071 n x.1 + Foam.Ty13.d071 n x.2

def Ty13.d068 : (n : Nat) → DecidableEq (Ty13 n)
  | 0 => (inferInstance : DecidableEq Ty05)
  | n + 1 => fun x y =>
    @instDecidableEqProd _ _ (Foam.Ty13.d068 n) (Foam.Ty13.d068 n) x y

instance {n : Nat} : DecidableEq (Ty13 n) := Foam.Ty13.d068 n

theorem Ty13.t235 (n : Nat) (x y : Ty13 (n + 1)) :
    Foam.Ty13.d069 (n + 1) x y =
      (Foam.Ty13.d128 n (Foam.Ty13.d069 n x.1 y.1) (Foam.Ty13.d069 n (Foam.Ty13.d067 n y.2) x.2),
       Foam.Ty13.d066 n (Foam.Ty13.d069 n y.2 x.1) (Foam.Ty13.d069 n x.2 (Foam.Ty13.d067 n y.1))) := rfl

theorem Ty13.t232 (a b : Ty05) : Foam.Ty13.d069 0 a b = Foam.Ty05.d112 a b := rfl

def Ty13.d073 (x : Ty13 1) : Ty10 := ⟨x.1, x.2⟩
def Ty10.d122 (q : Ty10) : Ty13 1 := (q.d056, q.d057)

theorem Ty13.t236 (q : Ty10) : Foam.Ty13.d073 (Foam.Ty10.d122 q) = q := rfl
theorem Ty10.t226 (x : Ty13 1) : Foam.Ty10.d122 (Foam.Ty13.d073 x) = x := rfl

theorem Ty13.t361 (x y : Ty13 1) :
    Foam.Ty13.d073 (Foam.Ty13.d069 1 x y) = Foam.Ty10.d172 (Foam.Ty13.d073 x) (Foam.Ty13.d073 y) := rfl

def Ty13.d129 (x : Ty13 2) : Ty09 := ⟨Foam.Ty13.d073 x.1, Foam.Ty13.d073 x.2⟩
def Ty09.d167 (o : Ty09) : Ty13 2 := (Foam.Ty10.d122 o.d053, Foam.Ty10.d122 o.d054)

theorem Ty13.t360 (o : Ty09) : Foam.Ty13.d129 (Foam.Ty09.d167 o) = o := rfl
theorem Ty09.t355 (x : Ty13 2) : Foam.Ty09.d167 (Foam.Ty13.d129 x) = x := rfl

theorem Ty13.t434 (x y : Ty13 2) :
    Foam.Ty13.d129 (Foam.Ty13.d069 2 x y) = Foam.Ty09.d209 (Foam.Ty13.d129 x) (Foam.Ty13.d129 y) := rfl

def Ty13.d180 (x : Ty13 3) : Ty17 := ⟨Foam.Ty13.d129 x.1, Foam.Ty13.d129 x.2⟩
def Ty17.d215 (s : Ty17) : Ty13 3 := (Foam.Ty09.d167 s.d081, Foam.Ty09.d167 s.d082)

theorem Ty13.t435 (s : Ty17) : Foam.Ty13.d180 (Foam.Ty17.d215 s) = s := rfl
theorem Ty17.t439 (x : Ty13 3) : Foam.Ty17.d215 (Foam.Ty13.d180 x) = x := rfl

theorem Ty13.t483 (x y : Ty13 3) :
    Foam.Ty13.d180 (Foam.Ty13.d069 3 x y) = Foam.Ty17.d227 (Foam.Ty13.d180 x) (Foam.Ty13.d180 y) := rfl

theorem t190 :
    Foam.Ty13.d069 1 (⟨Foam.Ty05.d044, ⟨1, 0⟩⟩ : Ty13 1) (⟨Foam.Ty05.d044, ⟨1, 0⟩⟩ : Ty13 1)
      = Foam.Ty13.d070 1 (⟨⟨1, 0⟩, Foam.Ty05.d044⟩ : Ty13 1) := rfl

/-- info: 'Foam.Ty13.t235' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t235

/-- info: 'Foam.Ty13.t232' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t232

/-- info: 'Foam.Ty13.t361' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t361

/-- info: 'Foam.Ty10.t226' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty10.t226

/-- info: 'Foam.Ty13.t434' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t434

/-- info: 'Foam.Ty09.t355' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty09.t355

/-- info: 'Foam.Ty13.t483' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty13.t483

/-- info: 'Foam.Ty17.t439' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty17.t439

/-- info: 'Foam.t190' does not depend on any axioms -/
#guard_msgs in #print axioms t190

end Foam
