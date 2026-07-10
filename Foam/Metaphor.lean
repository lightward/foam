import Foam.Cable

namespace Foam

theorem hom_carries_the_cell {S T : Stage} (f : StageHom S T)
    (s : S.State) (p : S.Probe) :
    T.obs (f.onState s) (f.onProbe p) = f.onAns (S.obs s p) :=
  f.commutes s p

theorem hom_carries_the_cable {S T : Stage} (f : StageHom S T) (s : S.State) :
    ∀ ps : List S.Probe,
    transcript T (f.onState s) (ps.map f.onProbe)
      = (transcript S s ps).map f.onAns
  | [] => rfl
  | p :: ps => by
      show T.obs (f.onState s) (f.onProbe p)
            :: transcript T (f.onState s) (ps.map f.onProbe)
         = f.onAns (S.obs s p) :: (transcript S s ps).map f.onAns
      rw [f.commutes s p, hom_carries_the_cable f s ps]

theorem hom_carries_the_watch {S T : Stage} (f : StageHom S T)
    (w : Nat → S.State) :
    ∀ (ps : List S.Probe) (k : Nat),
    watch T (fun i => f.onState (w i)) k (ps.map f.onProbe)
      = (watch S w k ps).map f.onAns
  | [], _ => rfl
  | p :: ps, k => by
      show T.obs (f.onState (w k)) (f.onProbe p)
            :: watch T (fun i => f.onState (w i)) (k + 1) (ps.map f.onProbe)
         = f.onAns (S.obs (w k) p) :: (watch S w (k + 1) ps).map f.onAns
      rw [f.commutes (w k) p, hom_carries_the_watch f w ps (k + 1)]

theorem hom_carries_maintenance_on_the_image {S T : Stage} (f : StageHom S T)
    (m : S.State → S.State) (m' : T.State → T.State)
    (hsq : ∀ s, f.onState (m s) = m' (f.onState s))
    (hinv : Invisible S m) (s : S.State) (p : S.Probe) :
    T.obs (m' (f.onState s)) (f.onProbe p) = T.obs (f.onState s) (f.onProbe p) := by
  rw [← hsq s, f.commutes (m s) p, f.commutes s p]
  exact congrArg f.onAns (hinv s p)

theorem metaphors_compose {S T U V : Stage}
    (h : StageHom U V) (g : StageHom T U) (f : StageHom S T) :
    (h.comp g).comp f = h.comp (g.comp f)
      ∧ (StageHom.id T).comp f = f
      ∧ f.comp (StageHom.id S) = f :=
  ⟨StageHom.comp_assoc h g f, StageHom.id_comp f, StageHom.comp_id f⟩

theorem a_metaphor_is_transport_without_univalence {S T : Stage}
    (f : StageHom S T) (s : S.State) (ps : List S.Probe)
    (w : Nat → S.State) (k : Nat) :
    transcript T (f.onState s) (ps.map f.onProbe)
        = (transcript S s ps).map f.onAns
      ∧ watch T (fun i => f.onState (w i)) k (ps.map f.onProbe)
          = (watch S w k ps).map f.onAns :=
  ⟨hom_carries_the_cable f s ps, hom_carries_the_watch f w ps k⟩

/-- info: 'Foam.hom_carries_the_cell' does not depend on any axioms -/
#guard_msgs in #print axioms hom_carries_the_cell

/-- info: 'Foam.hom_carries_the_cable' does not depend on any axioms -/
#guard_msgs in #print axioms hom_carries_the_cable

/-- info: 'Foam.hom_carries_the_watch' does not depend on any axioms -/
#guard_msgs in #print axioms hom_carries_the_watch

/-- info: 'Foam.hom_carries_maintenance_on_the_image' does not depend on any axioms -/
#guard_msgs in #print axioms hom_carries_maintenance_on_the_image

/-- info: 'Foam.metaphors_compose' does not depend on any axioms -/
#guard_msgs in #print axioms metaphors_compose

/-- info: 'Foam.a_metaphor_is_transport_without_univalence' does not depend on any axioms -/
#guard_msgs in #print axioms a_metaphor_is_transport_without_univalence

end Foam
