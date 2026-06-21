import Foam.Seat

namespace Foam

structure Seam (A B : Type) where
  up       : A → B
  faithful : ∀ {x y : A}, up x = up y → x = y
  escapes  : ∃ y : B, ∀ x : A, up x ≠ y

def Seam.prime {A B : Type} (S : Seam A B) (q : B) : Prop := ∀ x : A, S.up x ≠ q

theorem Seam.no_section {A B : Type} (S : Seam A B) :
    ¬ ∃ g : B → A, ∀ b, S.up (g b) = b := by
  rintro ⟨g, hg⟩
  obtain ⟨y, hy⟩ := S.escapes
  exact hy (g y) (hg y)

def nth {S : Type} : List S → Nat → Option S
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: l, n + 1 => nth l n

theorem nth_faithful {S : Type} : ∀ s t : List S, (∀ n, nth s n = nth t n) → s = t
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h 0
  | _ :: _, [], h => nomatch h 0
  | a :: s, b :: t, h => by
    injection h 0 with hab
    rw [hab, nth_faithful s t (fun n => h (n + 1))]

theorem nth_stable {S : Type} : ∀ (l : List S) (n : Nat), nth l n = none → nth l (n + 1) = none
  | [], _, _ => rfl
  | _ :: _, 0, h => nomatch h
  | _ :: l, n + 1, h => nth_stable l n h

theorem nth_length {S : Type} : ∀ l : List S, nth l l.length = none
  | [] => rfl
  | _ :: l => nth_length l

structure CoList (S : Type) where
  at_    : Nat → Option S
  stable : ∀ n, at_ n = none → at_ (n + 1) = none

def playback {S : Type} (l : List S) : CoList S := ⟨nth l, nth_stable l⟩

def forever {S : Type} (s : S) : CoList S := ⟨fun _ => some s, fun _ h => nomatch h⟩

theorem forever_escapes {S : Type} (s : S) (l : List S) :
    ∃ n, (playback l).at_ n ≠ (forever s).at_ n :=
  ⟨l.length, fun h => nomatch (nth_length l).symm.trans h⟩

theorem playback_faithful {S : Type} (l l' : List S)
    (h : ∀ n, (playback l).at_ n = (playback l').at_ n) : l = l' :=
  nth_faithful l l' h

def playbackSeam {S : Type} (s : S) : Seam (List S) (CoList S) where
  up       := playback
  faithful := fun {l l'} h => playback_faithful l l' (fun n => congrArg (fun c => c.at_ n) h)
  escapes  := ⟨forever s, fun l h => (forever_escapes s l).elim (fun n hn => hn (congrArg (fun c => c.at_ n) h))⟩

theorem playback_no_section {S : Type} (s : S) :
    ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  Seam.no_section (playbackSeam s)

theorem seam_two_faces {S : Type} (s : S) :
    (∀ l l' : List S, (∀ n, (playback l).at_ n = (playback l').at_ n) → l = l')
      ∧ ¬ ∃ g : CoList S → List S, ∀ c, playback (g c) = c :=
  ⟨playback_faithful, playback_no_section s⟩

/-- info: 'Foam.Seam.no_section' does not depend on any axioms -/
#guard_msgs in #print axioms Seam.no_section

/-- info: 'Foam.playbackSeam' does not depend on any axioms -/
#guard_msgs in #print axioms playbackSeam

/-- info: 'Foam.playback_faithful' does not depend on any axioms -/
#guard_msgs in #print axioms playback_faithful

/-- info: 'Foam.playback_no_section' does not depend on any axioms -/
#guard_msgs in #print axioms playback_no_section

/-- info: 'Foam.seam_two_faces' does not depend on any axioms -/
#guard_msgs in #print axioms seam_two_faces

end Foam
