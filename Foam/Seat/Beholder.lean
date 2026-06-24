import Foam.Seat.Stage
import Foam.Seat.Observer

namespace Foam

structure Ty01 (State : Type) where
  Ty20 : Type
  Ty19 : Type
  d102 : State → Ty20 → Ty19

def Ty01.d161 {State : Type} (b : Ty01 State) : Ty18 where
  Ty27 := State
  Ty26 := b.Ty20
  Ty25 := b.Ty19
  d134 := b.d102

def Ty01.d159 {State : Type} (a b : Ty01 State) : Ty01 State where
  Ty20 := a.Ty20 × b.Ty20
  Ty19 := a.Ty19 × b.Ty19
  d102 s pq := (a.d102 s pq.1, b.d102 s pq.2)

theorem t394 {State : Type} (a b : Ty01 State)
    (s : State) (p : a.Ty20) (q : b.Ty20) :
    ((a.d159 b).d102 s (p, q)).1 = a.d102 s p := rfl

/-- info: 'Foam.t394' does not depend on any axioms -/
#guard_msgs in #print axioms t394

theorem t395 {State : Type} (a b : Ty01 State)
    (s : State) (p : a.Ty20) (q : b.Ty20) :
    ((a.d159 b).d102 s (p, q)).2 = b.d102 s q := rfl

/-- info: 'Foam.t395' does not depend on any axioms -/
#guard_msgs in #print axioms t395

def d187 {State R : Type} (a b : Ty01 State)
    (g : a.Ty19 → b.Ty19 → R) (s : State) (p : a.Ty20) (q : b.Ty20) : R :=
  g (a.d102 s p) (b.d102 s q)

theorem t369 {State R : Type} (a b : Ty01 State)
    (g : a.Ty19 → b.Ty19 → R) (s : State) (p : a.Ty20) (q : b.Ty20) :
    d187 a b g s p q = g ((a.d159 b).d102 s (p, q)).1 ((a.d159 b).d102 s (p, q)).2 :=
  rfl

/-- info: 'Foam.t369' does not depend on any axioms -/
#guard_msgs in #print axioms t369

theorem t390 {State R : Type} (a b : Ty01 State)
    (g : a.Ty19 → b.Ty19 → R) :
    ∃ c : Ty01 State, ∃ post : c.Ty19 → R, ∃ enc : a.Ty20 × b.Ty20 → c.Ty20,
      ∀ s p q, d187 a b g s p q = post (c.d102 s (enc (p, q))) :=
  ⟨a.d159 b, fun ans => g ans.1 ans.2, id, fun _ _ _ => rfl⟩

/-- info: 'Foam.t390' does not depend on any axioms -/
#guard_msgs in #print axioms t390

def Ty18.d183 (S : Ty18) : Ty01 S.Ty27 := ⟨S.Ty26, S.Ty25, S.d134⟩

theorem Ty18.t362 (S : Ty18) : S.d183.d161 = S := rfl

/-- info: 'Foam.Ty18.t362' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty18.t362

theorem Ty01.t334 {State : Type} (b : Ty01 State) :
    b.d161.d183 = b := rfl

/-- info: 'Foam.Ty01.t334' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty01.t334

end Foam
