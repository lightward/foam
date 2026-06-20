import Foam.Lattice.Seam

namespace Foam.Lattice

def CoBisim {S : Type} (c d : CoList S) : Prop := ∀ n, c.at_ n = d.at_ n

theorem CoBisim.refl {S : Type} (c : CoList S) : CoBisim c c := fun _ => rfl

theorem CoBisim.symm {S : Type} {c d : CoList S} (h : CoBisim c d) : CoBisim d c :=
  fun n => (h n).symm

theorem CoBisim.trans {S : Type} {c d e : CoList S}
    (h1 : CoBisim c d) (h2 : CoBisim d e) : CoBisim c e :=
  fun n => (h1 n).trans (h2 n)

theorem playback_reflects {S : Type} (l l' : List S)
    (h : CoBisim (playback l) (playback l')) : l = l' :=
  playback_faithful l l' h

theorem forever_apart {S : Type} (s : S) (l : List S) :
    ¬ CoBisim (playback l) (forever s) := by
  intro h
  obtain ⟨n, hn⟩ := forever_escapes s l
  exact hn (h n)

/-- info: 'Foam.Lattice.CoBisim.trans' does not depend on any axioms -/
#guard_msgs in #print axioms CoBisim.trans

/-- info: 'Foam.Lattice.playback_reflects' does not depend on any axioms -/
#guard_msgs in #print axioms playback_reflects

/-- info: 'Foam.Lattice.forever_apart' does not depend on any axioms -/
#guard_msgs in #print axioms forever_apart

end Foam.Lattice
