import Foam.Seat.Stage
import Foam.Ledger

namespace Foam

def t227 (S : Ty18) (r : S.Ty27 → S.Ty27 → Prop) : Prop :=
  ∀ s t, r s t → ∀ p, S.d134 s p = S.d134 t p

structure Ty22 (S : Ty18) where
  t139      : S.Ty27 → S.Ty27 → Prop
  t350 : t227 S t139

structure Ty28 (S T : Ty18) where
  d139  : S.Ty27 → T.Ty27
  d138  : S.Ty26 → T.Ty26
  d137    : S.Ty25 → T.Ty25
  t255 : ∀ s p, T.d134 (d139 s) (d138 p) = d137 (S.d134 s p)

def Ty28.d136 (S : Ty18) : Ty28 S S where
  d139  := fun s => s
  d138  := fun p => p
  d137    := fun a => a
  t255 := fun _ _ => rfl

def Ty28.d185 {S T U : Ty18} (g : Ty28 T U) (f : Ty28 S T) : Ty28 S U where
  d139  := fun s => g.d139 (f.d139 s)
  d138  := fun p => g.d138 (f.d138 p)
  d137    := fun a => g.d137 (f.d137 a)
  t255 := fun s p => by
    show U.d134 (g.d139 (f.d139 s)) (g.d138 (f.d138 p))
       = g.d137 (f.d137 (S.d134 s p))
    rw [g.t255 (f.d139 s) (f.d138 p), f.t255 s p]

theorem Ty28.t365 {S T : Ty18} (f : Ty28 S T) :
    (Foam.Ty28.d136 T).d185 f = f := rfl

theorem Ty28.t364 {S T : Ty18} (f : Ty28 S T) :
    f.d185 (Foam.Ty28.d136 S) = f := rfl

theorem Ty28.t363 {S T U V : Ty18}
    (h : Ty28 U V) (g : Ty28 T U) (f : Ty28 S T) :
    (h.d185 g).d185 f = h.d185 (g.d185 f) := rfl

def Ty18.d184 (S T : Ty18) : Ty18 where
  Ty27 := S.Ty27 × T.Ty27
  Ty26 := S.Ty26 × T.Ty26
  Ty25   := S.Ty25 × T.Ty25
  d134   := fun st pq => (S.d134 st.1 pq.1, T.d134 st.2 pq.2)

def Ty28.d217 (S T : Ty18) : Ty28 (Foam.Ty18.d184 S T) S where
  d139  := fun st => st.1
  d138  := fun pq => pq.1
  d137    := fun a => a.1
  t255 := fun _ _ => rfl

def Ty28.d219 (S T : Ty18) : Ty28 (Foam.Ty18.d184 S T) T where
  d139  := fun st => st.2
  d138  := fun pq => pq.2
  d137    := fun a => a.2
  t255 := fun _ _ => rfl

def Ty28.d218 {X S T : Ty18} (f : Ty28 X S) (g : Ty28 X T) :
    Ty28 X (Foam.Ty18.d184 S T) where
  d139  := fun x => (f.d139 x, g.d139 x)
  d138  := fun p => (f.d138 p, g.d138 p)
  d137    := fun a => (f.d137 a, g.d137 a)
  t255 := fun x p => by
    show (S.d134 (f.d139 x) (f.d138 p), T.d134 (g.d139 x) (g.d138 p))
       = (f.d137 (X.d134 x p), g.d137 (X.d134 x p))
    rw [f.t255 x p, g.t255 x p]

theorem Ty28.t440 {X S T : Ty18} (f : Ty28 X S) (g : Ty28 X T) :
    (Foam.Ty28.d217 S T).d185 (Foam.Ty28.d218 f g) = f := rfl

theorem Ty28.t442 {X S T : Ty18} (f : Ty28 X S) (g : Ty28 X T) :
    (Foam.Ty28.d219 S T).d185 (Foam.Ty28.d218 f g) = g := rfl

theorem Ty28.t441 {X S T : Ty18} (h : Ty28 X (Foam.Ty18.d184 S T)) :
    h = Foam.Ty28.d218 ((Foam.Ty28.d217 S T).d185 h) ((Foam.Ty28.d219 S T).d185 h) := rfl

def Ty22.d205 {S T : Ty18} (F : Ty22 S) (G : Ty22 T) :
    Ty22 (Foam.Ty18.d184 S T) where
  t139      := fun st st' => F.t139 st.1 st'.1 ∧ G.t139 st.2 st'.2
  t350 := fun st st' h pq => by
    show (S.d134 st.1 pq.1, T.d134 st.2 pq.2) = (S.d134 st'.1 pq.1, T.d134 st'.2 pq.2)
    rw [F.t350 st.1 st'.1 h.1 pq.1, G.t350 st.2 st'.2 h.2 pq.2]

def t069 {S : Type} (r r' : S → S → Prop) : Prop := ∀ a b, r a b → r' a b

theorem t069.t097 {S : Type} (r : S → S → Prop) : t069 r r :=
  fun _ _ h => h

theorem t069.t098 {S : Type} {r r' r'' : S → S → Prop}
    (h1 : t069 r r') (h2 : t069 r' r'') : t069 r r'' :=
  fun a b h => h2 a b (h1 a b h)

def t076 {State Probe A : Type} (o : State → Probe → A) (s t : State) : Prop :=
  ∀ p, o s p = o t p

def t068 {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) : Prop :=
  ∃ g : A → B, ∀ s p, o2 s p = g (o1 s p)

theorem t068.t095 {State Probe A : Type} (o : State → Probe → A) :
    t068 o o :=
  ⟨fun a => a, fun _ _ => rfl⟩

theorem t068.t096 {State Probe A B C : Type}
    {o1 : State → Probe → A} {o2 : State → Probe → B} {o3 : State → Probe → C}
    (h12 : t068 o1 o2) (h23 : t068 o2 o3) : t068 o1 o3 := by
  obtain ⟨g, hg⟩ := h12
  obtain ⟨g', hg'⟩ := h23
  exact ⟨fun a => g' (g a), fun s p => by rw [hg' s p, hg s p]⟩

theorem t128 {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) (h : t068 o1 o2) :
    t069 (t076 o1) (t076 o2) := by
  obtain ⟨g, hg⟩ := h
  intro s t hst p
  rw [hg s p, hg t p]
  exact congrArg g (hst p)

def d087 (S : Type) [DecidableEq S] : Ty18 where
  Ty27 := List S
  Ty26 := S
  Ty25   := Nat
  d134   := fun l s => Foam.Ty08.d003 l s

def d151 (S : Type) [DecidableEq S] : Ty22 (d087 S) where
  t139      := fun l l' => l.Perm l'
  t350 := fun _ _ h s => Foam.Ty08.t093 h s

/-- info: 'Foam.Ty28.t365' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t365

/-- info: 'Foam.Ty28.t363' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t363

/-- info: 'Foam.Ty28.t440' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t440

/-- info: 'Foam.Ty28.t442' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t442

/-- info: 'Foam.Ty28.t441' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty28.t441

/-- info: 'Foam.Ty22.d205' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.Ty22.d205

/-- info: 'Foam.t069.t098' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t069.t098

/-- info: 'Foam.t068.t096' does not depend on any axioms -/
#guard_msgs in #print axioms Foam.t068.t096

/-- info: 'Foam.t128' does not depend on any axioms -/
#guard_msgs in #print axioms t128

/-- info: 'Foam.d151' does not depend on any axioms -/
#guard_msgs in #print axioms d151

end Foam