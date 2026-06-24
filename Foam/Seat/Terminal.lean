import Foam.Seat.Observer

namespace Foam

def d196 (S : Ty18) (p : S.Ty26) : Ty18 where
  Ty27 := S.Ty27
  Ty26 := Unit
  Ty25   := S.Ty25
  d134   := fun s _ => S.d134 s p

def d223 (S : Ty18) (p : S.Ty26) : Ty28 (d196 S p) S where
  d139  := fun s => s
  d138  := fun _ => p
  d137    := fun a => a
  t255 := fun _ _ => rfl

theorem t375 (S : Ty18) (p : S.Ty26) (s : S.Ty27) :
    (d196 S p).d134 s () = S.d134 s p := rfl

theorem t457 (S : Ty18) (p : S.Ty26) :
    (d223 S p).d138 () = p := rfl

def d101 : Ty18 where
  Ty27 := Unit
  Ty26 := Unit
  Ty25   := Unit
  d134   := fun _ _ => ()

def d143 (S : Ty18) : Ty28 S d101 where
  d139  := fun _ => ()
  d138  := fun _ => ()
  d137    := fun _ => ()
  t255 := fun _ _ => rfl

theorem t281 (S : Ty18) (f : Ty28 S d101) : f = d143 S := rfl

theorem t456 (S : Ty18) (p : S.Ty26) :
    (d143 S).d185 (d223 S p) = d143 (d196 S p) := rfl

/-- info: 'Foam.d223' does not depend on any axioms -/
#guard_msgs in #print axioms d223

/-- info: 'Foam.t375' does not depend on any axioms -/
#guard_msgs in #print axioms t375

/-- info: 'Foam.t457' does not depend on any axioms -/
#guard_msgs in #print axioms t457

/-- info: 'Foam.t281' does not depend on any axioms -/
#guard_msgs in #print axioms t281

/-- info: 'Foam.t456' does not depend on any axioms -/
#guard_msgs in #print axioms t456

end Foam
