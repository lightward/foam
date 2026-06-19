import Foam.Lattice.Frontstage

namespace Foam.Lattice

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

def StageHom.ofReading {State Probe A B : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) (g : A → B)
    (hg : ∀ s p, o2 s p = g (o1 s p)) :
    StageHom ⟨State, Probe, A, o1⟩ ⟨State, Probe, B, o2⟩ where
  onState  := fun s => s
  onProbe  := fun p => p
  onAns    := g
  commutes := hg

theorem StageHom.ofReading_comp {State Probe A B C : Type}
    (o1 : State → Probe → A) (o2 : State → Probe → B) (o3 : State → Probe → C)
    (g : A → B) (g' : B → C)
    (hg : ∀ s p, o2 s p = g (o1 s p)) (hg' : ∀ s p, o3 s p = g' (o2 s p)) :
    (StageHom.ofReading o2 o3 g' hg').comp (StageHom.ofReading o1 o2 g hg)
      = StageHom.ofReading o1 o3 (fun a => g' (g a))
          (fun s p => by rw [hg' s p, hg s p]) := rfl

/-- info: 'Foam.Lattice.Refines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Refines.trans

/-- info: 'Foam.Lattice.ReadingRefines.trans' does not depend on any axioms -/
#guard_msgs in #print axioms ReadingRefines.trans

/-- info: 'Foam.Lattice.readingRefines_shadow' does not depend on any axioms -/
#guard_msgs in #print axioms readingRefines_shadow

/-- info: 'Foam.Lattice.StageHom.ofReading' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.ofReading

/-- info: 'Foam.Lattice.StageHom.ofReading_comp' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.ofReading_comp

end Foam.Lattice
