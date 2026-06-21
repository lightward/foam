import Foam.Seat.Stage

namespace Foam

def Respects (S : Stage) (r : S.State → S.State → Prop) : Prop :=
  ∀ s t, r s t → ∀ p, S.obs s p = S.obs t p

structure Frontstage (S : Stage) where
  rel      : S.State → S.State → Prop
  respects : Respects S rel

structure StageHom (S T : Stage) where
  onState  : S.State → T.State
  onProbe  : S.Probe → T.Probe
  onAns    : S.Ans → T.Ans
  commutes : ∀ s p, T.obs (onState s) (onProbe p) = onAns (S.obs s p)

def StageHom.id (S : Stage) : StageHom S S where
  onState  := fun s => s
  onProbe  := fun p => p
  onAns    := fun a => a
  commutes := fun _ _ => rfl

def StageHom.comp {S T U : Stage} (g : StageHom T U) (f : StageHom S T) : StageHom S U where
  onState  := fun s => g.onState (f.onState s)
  onProbe  := fun p => g.onProbe (f.onProbe p)
  onAns    := fun a => g.onAns (f.onAns a)
  commutes := fun s p => by
    show U.obs (g.onState (f.onState s)) (g.onProbe (f.onProbe p))
       = g.onAns (f.onAns (S.obs s p))
    rw [g.commutes (f.onState s) (f.onProbe p), f.commutes s p]

theorem StageHom.id_comp {S T : Stage} (f : StageHom S T) :
    (StageHom.id T).comp f = f := rfl

theorem StageHom.comp_id {S T : Stage} (f : StageHom S T) :
    f.comp (StageHom.id S) = f := rfl

theorem StageHom.comp_assoc {S T U V : Stage}
    (h : StageHom U V) (g : StageHom T U) (f : StageHom S T) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

def Stage.prod (S T : Stage) : Stage where
  State := S.State × T.State
  Probe := S.Probe × T.Probe
  Ans   := S.Ans × T.Ans
  obs   := fun st pq => (S.obs st.1 pq.1, T.obs st.2 pq.2)

def StageHom.fst (S T : Stage) : StageHom (Stage.prod S T) S where
  onState  := fun st => st.1
  onProbe  := fun pq => pq.1
  onAns    := fun a => a.1
  commutes := fun _ _ => rfl

def StageHom.snd (S T : Stage) : StageHom (Stage.prod S T) T where
  onState  := fun st => st.2
  onProbe  := fun pq => pq.2
  onAns    := fun a => a.2
  commutes := fun _ _ => rfl

def StageHom.pair {X S T : Stage} (f : StageHom X S) (g : StageHom X T) :
    StageHom X (Stage.prod S T) where
  onState  := fun x => (f.onState x, g.onState x)
  onProbe  := fun p => (f.onProbe p, g.onProbe p)
  onAns    := fun a => (f.onAns a, g.onAns a)
  commutes := fun x p => by
    show (S.obs (f.onState x) (f.onProbe p), T.obs (g.onState x) (g.onProbe p))
       = (f.onAns (X.obs x p), g.onAns (X.obs x p))
    rw [f.commutes x p, g.commutes x p]

theorem StageHom.fst_pair {X S T : Stage} (f : StageHom X S) (g : StageHom X T) :
    (StageHom.fst S T).comp (StageHom.pair f g) = f := rfl

theorem StageHom.snd_pair {X S T : Stage} (f : StageHom X S) (g : StageHom X T) :
    (StageHom.snd S T).comp (StageHom.pair f g) = g := rfl

theorem StageHom.pair_unique {X S T : Stage} (h : StageHom X (Stage.prod S T)) :
    h = StageHom.pair ((StageHom.fst S T).comp h) ((StageHom.snd S T).comp h) := rfl

def Frontstage.prod {S T : Stage} (F : Frontstage S) (G : Frontstage T) :
    Frontstage (Stage.prod S T) where
  rel      := fun st st' => F.rel st.1 st'.1 ∧ G.rel st.2 st'.2
  respects := fun st st' h pq => by
    show (S.obs st.1 pq.1, T.obs st.2 pq.2) = (S.obs st'.1 pq.1, T.obs st'.2 pq.2)
    rw [F.respects st.1 st'.1 h.1 pq.1, G.respects st.2 st'.2 h.2 pq.2]

def Refines {S : Type} (r r' : S → S → Prop) : Prop := ∀ a b, r a b → r' a b

theorem Refines.refl {S : Type} (r : S → S → Prop) : Refines r r :=
  fun _ _ h => h

theorem Refines.trans {S : Type} {r r' r'' : S → S → Prop}
    (h1 : Refines r r') (h2 : Refines r' r'') : Refines r r'' :=
  fun a b h => h2 a b (h1 a b h)

def indist {State Probe A : Type} (o : State → Probe → A) (s t : State) : Prop :=
  ∀ p, o s p = o t p

def ReadingRefines {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) : Prop :=
  ∃ g : A → B, ∀ s p, o2 s p = g (o1 s p)

theorem ReadingRefines.refl {State Probe A : Type} (o : State → Probe → A) :
    ReadingRefines o o :=
  ⟨fun a => a, fun _ _ => rfl⟩

theorem ReadingRefines.trans {State Probe A B C : Type}
    {o1 : State → Probe → A} {o2 : State → Probe → B} {o3 : State → Probe → C}
    (h12 : ReadingRefines o1 o2) (h23 : ReadingRefines o2 o3) : ReadingRefines o1 o3 := by
  obtain ⟨g, hg⟩ := h12
  obtain ⟨g', hg'⟩ := h23
  exact ⟨fun a => g' (g a), fun s p => by rw [hg' s p, hg s p]⟩

theorem readingRefines_shadow {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) (h : ReadingRefines o1 o2) :
    Refines (indist o1) (indist o2) := by
  obtain ⟨g, hg⟩ := h
  intro s t hst p
  rw [hg s p, hg t p]
  exact congrArg g (hst p)

def freq {S : Type} [DecidableEq S] : List S → S → Nat
  | [], _ => 0
  | x :: l, s => (if x = s then 1 else 0) + freq l s

theorem freq_perm {S : Type} [DecidableEq S] {xs ys : List S} (h : xs.Perm ys) (s : S) :
    freq xs s = freq ys s := by
  induction h with
  | nil => rfl
  | cons x _ ih => exact congrArg ((if x = s then 1 else 0) + ·) ih
  | swap x y l => exact Nat.add_left_comm _ _ _
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

def countStage (S : Type) [DecidableEq S] : Stage where
  State := List S
  Probe := S
  Ans   := Nat
  obs   := fun l s => freq l s

def permLicense (S : Type) [DecidableEq S] : Frontstage (countStage S) where
  rel      := fun l l' => l.Perm l'
  respects := fun _ _ h s => freq_perm h s

/-- info: 'Foam.StageHom.id_comp' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.id_comp

/-- info: 'Foam.StageHom.comp_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.comp_assoc

/-- info: 'Foam.StageHom.fst_pair' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.fst_pair

/-- info: 'Foam.StageHom.snd_pair' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.snd_pair

/-- info: 'Foam.StageHom.pair_unique' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.pair_unique

/-- info: 'Foam.Frontstage.prod' does not depend on any axioms -/
#guard_msgs in #print axioms Frontstage.prod

/-- info: 'Foam.Refines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Refines.trans

/-- info: 'Foam.ReadingRefines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms ReadingRefines.trans

/-- info: 'Foam.readingRefines_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms readingRefines_shadow

/-- info: 'Foam.freq_perm' does not depend on any axioms -/
#guard_msgs in #print axioms freq_perm

/-- info: 'Foam.permLicense' does not depend on any axioms -/
#guard_msgs in #print axioms permLicense

end Foam