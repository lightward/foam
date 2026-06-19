namespace Foam.Lattice

structure Stage where
  State : Type
  Probe : Type
  Ans   : Type
  obs   : State → Probe → Ans

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

structure FrontstageHom {S T : Stage} (F : Frontstage S) (G : Frontstage T) where
  hom     : StageHom S T
  carries : ∀ s s', F.rel s s' → G.rel (hom.onState s) (hom.onState s')

def FrontstageHom.id {S : Stage} (F : Frontstage S) : FrontstageHom F F where
  hom     := StageHom.id S
  carries := fun _ _ h => h

def FrontstageHom.comp {S T U : Stage} {F : Frontstage S} {G : Frontstage T} {H : Frontstage U}
    (β : FrontstageHom G H) (α : FrontstageHom F G) : FrontstageHom F H where
  hom     := β.hom.comp α.hom
  carries := fun s s' h => β.carries _ _ (α.carries s s' h)

theorem FrontstageHom.id_comp {S T : Stage} {F : Frontstage S} {G : Frontstage T}
    (α : FrontstageHom F G) : (FrontstageHom.id G).comp α = α := rfl

theorem FrontstageHom.comp_id {S T : Stage} {F : Frontstage S} {G : Frontstage T}
    (α : FrontstageHom F G) : α.comp (FrontstageHom.id F) = α := rfl

theorem FrontstageHom.comp_assoc {S T U V : Stage}
    {F : Frontstage S} {G : Frontstage T} {H : Frontstage U} {K : Frontstage V}
    (γ : FrontstageHom H K) (β : FrontstageHom G H) (α : FrontstageHom F G) :
    (γ.comp β).comp α = γ.comp (β.comp α) := rfl

/-- info: 'Foam.Lattice.StageHom.id_comp' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.id_comp

/-- info: 'Foam.Lattice.StageHom.comp_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.comp_assoc

/-- info: 'Foam.Lattice.FrontstageHom.comp_assoc' does not depend on any axioms -/
#guard_msgs in #print axioms FrontstageHom.comp_assoc

end Foam.Lattice
