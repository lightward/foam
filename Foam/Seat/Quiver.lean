namespace Foam

abbrev Ty11 (Handle : Type) := List (Handle × Handle)

inductive Ty23 {Handle : Type} (q : Ty11 Handle) : Handle → Handle → Type where
  | c6  {a : Handle} : Ty23 q a a
  | c5 {a b c : Handle} : ((a, b) ∈ q) → Ty23 q b c → Ty23 q a c

def Ty23.d117 {Handle : Type} {q : Ty11 Handle} :
    {a b c : Handle} → Ty23 q a b → Ty23 q b c → Ty23 q a c
  | _, _, _, Foam.Ty23.c6,      p => p
  | _, _, _, Foam.Ty23.c5 e r, p => Foam.Ty23.c5 e (r.d117 p)

theorem Ty23.t223 {Handle : Type} {q : Ty11 Handle} {a b : Handle}
    (p : Ty23 q a b) : Foam.Ty23.c6.d117 p = p := rfl

theorem Ty23.t219 {Handle : Type} {q : Ty11 Handle} {a b : Handle}
    (p : Ty23 q a b) : p.d117 Foam.Ty23.c6 = p := by
  induction p with
  | c6 => rfl
  | c5 e r ih => exact congrArg (Foam.Ty23.c5 e) ih

theorem Ty23.t218 {Handle : Type} {q : Ty11 Handle} :
    {a b c d : Handle} → (p : Ty23 q a b) → (r : Ty23 q b c) → (s : Ty23 q c d) →
    (p.d117 r).d117 s = p.d117 (r.d117 s)
  | _, _, _, _, Foam.Ty23.c6,      _, _ => rfl
  | _, _, _, _, Foam.Ty23.c5 e p, r, s => congrArg (Foam.Ty23.c5 e) (Foam.Ty23.t218 p r s)

def Ty23.d119 {Handle : Type} {q : Ty11 Handle} :
    {a b : Handle} → Ty23 q a b → List (Handle × Handle)
  | _, _, Foam.Ty23.c6                 => []
  | _, _, @Foam.Ty23.c5 _ _ a b _ _ r => (a, b) :: r.d119

theorem Ty23.t221 {Handle : Type} {q : Ty11 Handle} :
    {a b c : Handle} → (p : Ty23 q a b) → (r : Ty23 q b c) →
    (p.d117 r).d119 = p.d119 ++ r.d119
  | _, _, _, Foam.Ty23.c6,                 _ => rfl
  | _, _, _, @Foam.Ty23.c5 _ _ a b _ _ p, r =>
      congrArg ((a, b) :: ·) (Foam.Ty23.t221 p r)

def Ty11.d062 {Handle : Type} (q : Ty11 Handle) : Ty11 Handle :=
  q.map (fun e => (e.2, e.1))

theorem t182 {Handle : Type} {q : Ty11 Handle} {a b : Handle}
    (h : (a, b) ∈ q) : (b, a) ∈ q.d062 := by
  induction h with
  | head as     => exact List.Mem.head _
  | tail e _ ih => exact List.Mem.tail _ ih

def Ty23.d120 {Handle : Type} {q : Ty11 Handle} :
    {a b : Handle} → Ty23 q a b → Ty23 q.d062 b a
  | _, _, Foam.Ty23.c6      => Foam.Ty23.c6
  | _, _, Foam.Ty23.c5 e r => r.d120.d117 (Foam.Ty23.c5 (t182 e) Foam.Ty23.c6)

theorem Ty23.t225 {Handle : Type} {q : Ty11 Handle} {a : Handle} :
    (Foam.Ty23.c6 : Ty23 q a a).d120 = Foam.Ty23.c6 := rfl

theorem Ty23.t224 {Handle : Type} {q : Ty11 Handle} :
    {a b c : Handle} → (p : Ty23 q a b) → (r : Ty23 q b c) →
    (p.d117 r).d120 = r.d120.d117 p.d120
  | _, _, _, Foam.Ty23.c6,      r => (Foam.Ty23.t219 r.d120).symm
  | _, _, _, Foam.Ty23.c5 e p, r => by
      have ih := Foam.Ty23.t224 p r
      show (p.d117 r).d120.d117 (Foam.Ty23.c5 (t182 e) Foam.Ty23.c6)
         = r.d120.d117 (p.d120.d117 (Foam.Ty23.c5 (t182 e) Foam.Ty23.c6))
      rw [ih]
      exact Foam.Ty23.t218 r.d120 p.d120 _

theorem Ty11.t147 {Handle : Type} :
    ∀ (q : Ty11 Handle), q.d062.d062 = q
  | []      => rfl
  | e :: es => congrArg (e :: ·) (Foam.Ty11.t147 es)

/-- info: 'Foam.Ty23.t223' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t223

/-- info: 'Foam.Ty23.t219' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t219

/-- info: 'Foam.Ty23.t218' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t218

/-- info: 'Foam.Ty23.t221' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t221

/-- info: 'Foam.t182' does not depend on any axioms -/
#guard_msgs in #print axioms t182

/-- info: 'Foam.Ty23.t225' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t225

/-- info: 'Foam.Ty23.t224' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty23.t224

/-- info: 'Foam.Ty11.t147' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty11.t147

end Foam