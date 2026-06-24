import Foam.Engine.Spectrum

namespace Foam

def d091 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) : List S → S → Ty05 → Ty05
  | [], _, z => z
  | x :: l, s, z => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step (d091 step l s z))

theorem t172 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) (s : S) (z : Ty05) :
    d091 step [] s z = z := rfl

theorem t197 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) :
    ∀ (new old : List S) (s : S),
      d089 step (new ++ old) s = d091 step new s (d089 step old s)
  | [], _, _ => rfl
  | x :: new, old, s =>
      congrArg (fun z => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step z))
        (t197 step new old s)

theorem t167 {S : Type} [DecidableEq S] (step : Ty05 → Ty05) :
    ∀ (l : List S) (s : S), d089 step l s = d091 step l s Foam.Ty05.d044
  | [], _ => rfl
  | x :: l, s =>
      congrArg (fun z => (if x = s then Foam.Ty05.d042 else Foam.Ty05.d044).d108 (step z))
        (t167 step l s)

theorem t162 {S : Type} [DecidableEq S] (new old : List S) (s : S) :
    d089 id (new ++ old) s = d091 id new s (d089 id old s) :=
  t197 id new old s

theorem t323 {S : Type} [DecidableEq S] (new old : List S) (s : S) :
    d089 Foam.Ty05.d115 (new ++ old) s = d091 Foam.Ty05.d115 new s (d089 Foam.Ty05.d115 old s) :=
  t197 Foam.Ty05.d115 new old s

/-- info: 'Foam.t197' does not depend on any axioms -/
#guard_msgs in #print axioms t197

/-- info: 'Foam.t167' does not depend on any axioms -/
#guard_msgs in #print axioms t167

/-- info: 'Foam.t162' does not depend on any axioms -/
#guard_msgs in #print axioms t162

/-- info: 'Foam.t323' does not depend on any axioms -/
#guard_msgs in #print axioms t323

end Foam
