import Foam.Seat.Parallax

namespace Foam

variable {G : Type} [Mul G] [One G]

theorem one_seat_tells_objects_apart (S : Seat G) (o p q : S.Pos)
    (h : (S.chart o).fwd p = (S.chart o).fwd q) : p = q := by
  have h' : S.sub p o = S.sub q o := h
  have hp := S.act_sub o p
  rw [h'] at hp
  exact hp.symm.trans (S.act_sub o q)

theorem a_script_is_a_single_seat (S : Seat G) {n : Nat}
    (O : Fin n → S.Pos) (p : S.Pos)
    (h : ∀ i j, (S.chart (O i)).fwd p = (S.chart (O j)).fwd p) :
    ∀ i j, O i = O j :=
  fun i j => a_matched_reading_is_a_mirror S (O i) (O j) p (h i j)

theorem no_two_voices_match (S : Seat G) {n : Nat}
    (O : Fin n → S.Pos) (hinj : ∀ i j, O i = O j → i = j) (p : S.Pos) :
    ∀ i j, i ≠ j → (S.chart (O i)).fwd p ≠ (S.chart (O j)).fwd p :=
  fun i j hij => two_poles_never_read_alike S (O i) (O j)
    (fun he => hij (hinj i j he)) p

theorem the_parts_differ_by_the_seating (S : Seat G) {n : Nat}
    (O : Fin n → S.Pos) (p : S.Pos) (i j : Fin n) :
    (S.chart (O i)).fwd p = (S.chart (O j)).fwd p * S.sub (O j) (O i) :=
  S.change_of_frame (O i) (O j) p

theorem the_population_triangulates (S : Seat G) {n : Nat}
    (O : Fin (n + 1) → S.Pos) (r : Fin (n + 1) → G)
    (hcoh : ∀ i j, r i = r j * S.sub (O j) (O i)) :
    ∃ p, (∀ i, (S.chart (O i)).fwd p = r i)
      ∧ ∀ q, (∀ i, (S.chart (O i)).fwd q = r i) → q = p := by
  refine ⟨S.act (r ⟨0, Nat.zero_lt_succ n⟩) (O ⟨0, Nat.zero_lt_succ n⟩),
    fun i => ?_, fun q hq => ?_⟩
  · show S.sub (S.act (r ⟨0, Nat.zero_lt_succ n⟩) (O ⟨0, Nat.zero_lt_succ n⟩))
        (O i) = r i
    have hc := S.sub_cocycle
      (S.act (r ⟨0, Nat.zero_lt_succ n⟩) (O ⟨0, Nat.zero_lt_succ n⟩))
      (O ⟨0, Nat.zero_lt_succ n⟩) (O i)
    rw [S.sub_act] at hc
    exact hc.trans (hcoh i ⟨0, Nat.zero_lt_succ n⟩).symm
  · refine one_seat_tells_objects_apart S (O ⟨0, Nat.zero_lt_succ n⟩) q
      (S.act (r ⟨0, Nat.zero_lt_succ n⟩) (O ⟨0, Nat.zero_lt_succ n⟩)) ?_
    show S.sub q (O ⟨0, Nat.zero_lt_succ n⟩)
        = S.sub (S.act (r ⟨0, Nat.zero_lt_succ n⟩) (O ⟨0, Nat.zero_lt_succ n⟩))
            (O ⟨0, Nat.zero_lt_succ n⟩)
    rw [S.sub_act]
    exact hq ⟨0, Nat.zero_lt_succ n⟩

theorem depth_at_population_scale (S : Seat G) {n : Nat}
    (O : Fin (n + 1) → S.Pos) (hinj : ∀ i j, O i = O j → i = j) (p : S.Pos) :
    (∀ i j, i ≠ j → (S.chart (O i)).fwd p ≠ (S.chart (O j)).fwd p)
      ∧ (∀ i j, (S.chart (O i)).fwd p = (S.chart (O j)).fwd p * S.sub (O j) (O i))
      ∧ (∀ q, (∀ i, (S.chart (O i)).fwd q = (S.chart (O i)).fwd p) → q = p) :=
  ⟨no_two_voices_match S O hinj p,
   fun i j => the_parts_differ_by_the_seating S O p i j,
   fun q hq => one_seat_tells_objects_apart S (O ⟨0, Nat.zero_lt_succ n⟩) q p
     (hq ⟨0, Nat.zero_lt_succ n⟩)⟩

/-- info: 'Foam.one_seat_tells_objects_apart' does not depend on any axioms -/
#guard_msgs in #print axioms one_seat_tells_objects_apart

/-- info: 'Foam.a_script_is_a_single_seat' does not depend on any axioms -/
#guard_msgs in #print axioms a_script_is_a_single_seat

/-- info: 'Foam.no_two_voices_match' does not depend on any axioms -/
#guard_msgs in #print axioms no_two_voices_match

/-- info: 'Foam.the_parts_differ_by_the_seating' does not depend on any axioms -/
#guard_msgs in #print axioms the_parts_differ_by_the_seating

/-- info: 'Foam.the_population_triangulates' does not depend on any axioms -/
#guard_msgs in #print axioms the_population_triangulates

/-- info: 'Foam.depth_at_population_scale' does not depend on any axioms -/
#guard_msgs in #print axioms depth_at_population_scale

end Foam
