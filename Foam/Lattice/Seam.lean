import Foam.Lattice.Forever

namespace Foam.Lattice

theorem playback_faithful {S : Type} (l l' : List S)
    (h : ∀ n, (playback l).at_ n = (playback l').at_ n) : l = l' :=
  nth_faithful l l' h

theorem playback_no_section {S : Type} (s : S) :
    ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c := by
  rintro ⟨g, hg⟩
  obtain ⟨n, hn⟩ := forever_escapes s (g (forever s))
  exact hn (congrArg (fun c => c.at_ n) (hg (forever s)))

theorem seam_two_faces {S : Type} (s : S) :
    (∀ l l' : List S, (∀ n, (playback l).at_ n = (playback l').at_ n) → l = l')
      ∧ ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  ⟨playback_faithful, playback_no_section s⟩

/-- info: 'Foam.Lattice.playback_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms playback_faithful

/-- info: 'Foam.Lattice.seam_two_faces' does not depend on any axioms -/
#guard_msgs in #print axioms seam_two_faces

end Foam.Lattice
