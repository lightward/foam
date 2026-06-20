import Foam.Lattice.Frontstage

namespace Foam.Lattice

abbrev Quiver (Handle : Type) := List (Handle × Handle)

def Quiver.deposit {Handle : Type} (q : Quiver Handle) (e : Handle × Handle) : Quiver Handle :=
  e :: q

def ReachWithin {Handle : Type} (q : Quiver Handle) : Nat → Handle → Handle → Prop
  | 0,     a, c => a = c
  | n + 1, a, c => a = c ∨ ∃ b, (a, b) ∈ q ∧ ReachWithin q n b c

def Reaches {Handle : Type} (q : Quiver Handle) (a b : Handle) : Prop :=
  ∃ n, ReachWithin q n a b

theorem reachW_then {Handle : Type} {q : Quiver Handle} {c : Handle} :
    ∀ (n : Nat) {a b : Handle}, ReachWithin q n a b → Reaches q b c → Reaches q a c
  | 0,     _, _, hab, hbc => by cases hab; exact hbc
  | n + 1, _, _, hab, hbc => by
      rcases hab with rfl | ⟨d, hd, hdb⟩
      · exact hbc
      · obtain ⟨j, hj⟩ := reachW_then n hdb hbc
        exact ⟨j + 1, Or.inr ⟨d, hd, hj⟩⟩

theorem Reaches.refl {Handle : Type} (q : Quiver Handle) (a : Handle) : Reaches q a a :=
  ⟨0, rfl⟩

theorem Reaches.trans {Handle : Type} {q : Quiver Handle} {a b c : Handle}
    (h1 : Reaches q a b) (h2 : Reaches q b c) : Reaches q a c := by
  obtain ⟨n, hn⟩ := h1
  exact reachW_then n hn h2

def MutualReach {Handle : Type} (q : Quiver Handle) (a b : Handle) : Prop :=
  Reaches q a b ∧ Reaches q b a

theorem MutualReach.refl {Handle : Type} (q : Quiver Handle) (a : Handle) : MutualReach q a a :=
  ⟨Reaches.refl q a, Reaches.refl q a⟩

theorem MutualReach.symm {Handle : Type} {q : Quiver Handle} {a b : Handle}
    (h : MutualReach q a b) : MutualReach q b a := ⟨h.2, h.1⟩

theorem MutualReach.trans {Handle : Type} {q : Quiver Handle} {a b c : Handle}
    (h1 : MutualReach q a b) (h2 : MutualReach q b c) : MutualReach q a c :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

def reachStage {Handle : Type} (q : Quiver Handle) : Stage :=
  ⟨Handle, Handle, Prop, fun s p => Reaches q s p⟩

def mergeFrontstage {Handle : Type} (q : Quiver Handle) : Frontstage (reachStage q) where
  rel      := MutualReach q
  respects := fun _ _ h _p => propext ⟨fun hsp => h.2.trans hsp, fun htp => h.1.trans htp⟩

/-- info: 'Foam.Lattice.Reaches.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Reaches.trans

/-- info: 'Foam.Lattice.MutualReach.trans' does not depend on any axioms -/
#guard_msgs in #print axioms MutualReach.trans

/-- info: 'Foam.Lattice.mergeFrontstage' depends on axioms: [propext] -/
#guard_msgs in #print axioms mergeFrontstage

end Foam.Lattice
