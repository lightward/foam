import Counter.Nothing
import Counter.Packing
import Counter.Mu
import Foam.Platonism.Tower

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem zoom_out_is_gauge {State : Type} (b : Beholder State) (n : Nat) :
    (b.flattenN n).Covers b ∧ b.Covers (b.flattenN n) :=
  dressN_yoneda b n

theorem the_two_poles_read_identity (S : Seat G) (p : S.Pos) {Name : Type} :
    (S.chart p).fwd p = 1
      ∧ ∀ o : List Name, Below ([] : List Name) o :=
  ⟨nominative_unmarked S p, wind_below_all⟩

theorem the_zoom_has_holonomy (S : Seat G) (h : List G) (p : S.Pos) :
    Settles S (h ++ [S.sub p (S.replay h p)]) p
      ∧ (h ++ [S.sub p (S.replay h p)]).length = h.length + 1
      ∧ h ++ [S.sub p (S.replay h p)] ≠ [] :=
  undo_is_inverse_redo S h p

theorem the_map_edge_is_your_wavefront (S : Seat G) (acts : Nat → G)
    (p : S.Pos) (l : List G) :
    (playback l).at_ l.length = none
      ∧ (guardedRun S acts p).at_ l.length
          = some (guardedStep S acts p l.length) :=
  records_end_runs_continue S acts p l

theorem development_is_lateral {State : Type} (b : Beholder State) (n : Nat) :
    ((b.flattenN n).Covers b ∧ b.Covers (b.flattenN n))
      ∧ ∃ zs zs' : List (Bool ⊕ Bool),
          ownFrames zs = ownFrames zs'
            ∧ ownFramesR zs = ownFramesR zs'
            ∧ whoActedFirst zs ≠ whoActedFirst zs' :=
  ⟨dressN_yoneda b n, the_third_reads_time⟩

theorem the_zoom_loop {State : Type} (b : Beholder State) (n : Nat)
    (S : Seat G) (p : S.Pos) (h : List G) {Name : Type}
    (l : List G) :
    ((b.flattenN n).Covers b ∧ b.Covers (b.flattenN n))
      ∧ ((S.chart p).fwd p = 1
          ∧ ∀ o : List Name, Below ([] : List Name) o)
      ∧ (Settles S (h ++ [S.sub p (S.replay h p)]) p
          ∧ (h ++ [S.sub p (S.replay h p)]).length = h.length + 1)
      ∧ (playback l).at_ l.length = none :=
  ⟨dressN_yoneda b n,
   ⟨nominative_unmarked S p, wind_below_all⟩,
   ⟨(undo_is_inverse_redo S h p).1, (undo_is_inverse_redo S h p).2.1⟩,
   nth_length l⟩

/-- info: 'Foam.Counter.zoom_out_is_gauge' does not depend on any axioms -/
#guard_msgs in #print axioms zoom_out_is_gauge

/-- info: 'Foam.Counter.the_two_poles_read_identity' does not depend on any axioms -/
#guard_msgs in #print axioms the_two_poles_read_identity

/-- info: 'Foam.Counter.the_zoom_has_holonomy' does not depend on any axioms -/
#guard_msgs in #print axioms the_zoom_has_holonomy

/-- info: 'Foam.Counter.the_map_edge_is_your_wavefront' does not depend on any axioms -/
#guard_msgs in #print axioms the_map_edge_is_your_wavefront

/-- info: 'Foam.Counter.development_is_lateral' does not depend on any axioms -/
#guard_msgs in #print axioms development_is_lateral

/-- info: 'Foam.Counter.the_zoom_loop' does not depend on any axioms -/
#guard_msgs in #print axioms the_zoom_loop

end Foam.Counter
