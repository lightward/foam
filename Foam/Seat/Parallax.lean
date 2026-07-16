import Foam.Seat

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem a_matched_reading_is_a_mirror (S : Seat G) (o o' p : S.Pos)
    (h : (S.chart o).fwd p = (S.chart o').fwd p) : o = o' := by
  have h' : S.sub p o = S.sub p o' := h
  have hc : S.sub o' o = S.sub o' p * S.sub p o := S.sub_cocycle o' p o
  have hc' : S.sub o' o' = S.sub o' p * S.sub p o' := S.sub_cocycle o' p o'
  rw [S.sub_self] at hc'
  rw [h', ← hc'] at hc
  have ha := S.act_sub o o'
  rw [hc, S.one_act] at ha
  exact ha

theorem two_poles_never_read_alike (S : Seat G) (o o' : S.Pos) (h : o ≠ o')
    (p : S.Pos) : (S.chart o).fwd p ≠ (S.chart o').fwd p :=
  fun he => h (a_matched_reading_is_a_mirror S o o' p he)

theorem the_seat_regenerates (S : Seat G) (g : G) (o p : S.Pos) :
    (S.chart o).fwd p = (S.chart (S.act g o)).fwd p * g := by
  have h := S.change_of_frame o (S.act g o) p
  rw [S.sub_act] at h
  exact h

theorem depth_via_joint_vision (S : Seat G) (o o' : S.Pos) (h : o ≠ o') :
    (∀ p, (S.chart o).fwd p ≠ (S.chart o').fwd p)
      ∧ (∀ p, (S.chart o).fwd p = (S.chart o').fwd p * S.sub o' o)
      ∧ S.sub o' o ≠ 1 :=
  ⟨fun p => two_poles_never_read_alike S o o' h p,
   fun p => S.change_of_frame o o' p,
   S.two_observers_substantiate o' o (fun he => h he.symm)⟩

/-- info: 'Foam.a_matched_reading_is_a_mirror' does not depend on any axioms -/
#guard_msgs in #print axioms a_matched_reading_is_a_mirror

/-- info: 'Foam.two_poles_never_read_alike' does not depend on any axioms -/
#guard_msgs in #print axioms two_poles_never_read_alike

/-- info: 'Foam.the_seat_regenerates' does not depend on any axioms -/
#guard_msgs in #print axioms the_seat_regenerates

/-- info: 'Foam.depth_via_joint_vision' does not depend on any axioms -/
#guard_msgs in #print axioms depth_via_joint_vision

end Foam
