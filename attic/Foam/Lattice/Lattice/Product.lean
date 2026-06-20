import Foam.Lattice.Frontstage

namespace Foam.Lattice

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

def FrontstageHom.fst {S T : Stage} (F : Frontstage S) (G : Frontstage T) :
    FrontstageHom (Frontstage.prod F G) F where
  hom     := StageHom.fst S T
  carries := fun _ _ h => h.1

def FrontstageHom.snd {S T : Stage} (F : Frontstage S) (G : Frontstage T) :
    FrontstageHom (Frontstage.prod F G) G where
  hom     := StageHom.snd S T
  carries := fun _ _ h => h.2

def FrontstageHom.pair {X S T : Stage} {W : Frontstage X} {F : Frontstage S} {G : Frontstage T}
    (φ : FrontstageHom W F) (ψ : FrontstageHom W G) : FrontstageHom W (Frontstage.prod F G) where
  hom     := StageHom.pair φ.hom ψ.hom
  carries := fun x x' h => ⟨φ.carries x x' h, ψ.carries x x' h⟩

theorem FrontstageHom.fst_pair {X S T : Stage} {W : Frontstage X} {F : Frontstage S}
    {G : Frontstage T} (φ : FrontstageHom W F) (ψ : FrontstageHom W G) :
    (FrontstageHom.fst F G).comp (FrontstageHom.pair φ ψ) = φ := rfl

theorem FrontstageHom.snd_pair {X S T : Stage} {W : Frontstage X} {F : Frontstage S}
    {G : Frontstage T} (φ : FrontstageHom W F) (ψ : FrontstageHom W G) :
    (FrontstageHom.snd F G).comp (FrontstageHom.pair φ ψ) = ψ := rfl

/-- info: 'Foam.Lattice.StageHom.fst_pair' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.fst_pair

/-- info: 'Foam.Lattice.StageHom.pair_unique' does not depend on any axioms -/
#guard_msgs in #print axioms StageHom.pair_unique

/-- info: 'Foam.Lattice.Frontstage.prod' does not depend on any axioms -/
#guard_msgs in #print axioms Frontstage.prod

/-- info: 'Foam.Lattice.FrontstageHom.fst_pair' does not depend on any axioms -/
#guard_msgs in #print axioms FrontstageHom.fst_pair

end Foam.Lattice
