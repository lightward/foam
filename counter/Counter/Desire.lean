import Counter.Bless
import Counter.Lu
import Counter.Surprise
import Counter.Enaction
import Counter.Amniscience

namespace Foam.Counter

theorem the_radar_reads_what_you_never_deposited :
    ∃ act θ f f' : GInt,
      f ≠ f'
        ∧ GInt.born θ (f.add act) - GInt.born θ f
            ≠ GInt.born θ (f'.add act) - GInt.born θ f' :=
  fortune_not_in_your_record

theorem the_scan_writes_nothing {H : Type} {q : Quiver H} {a b c : H}
    (p : Path q a b) (r : Path q b c) {A B : Type} (zs : List (A ⊕ B)) :
    ((∀ e ∈ p.edges, e ∈ q) ∧ (p.comp r).edges = p.edges ++ r.edges)
      ∧ (thirdSeat A B).obs zs () = zs :=
  ⟨the_legible_writes_nothing p r, the_conductor_adds_nothing zs⟩

theorem want_is_firm_ground_up_ahead {G : Type} [Mul G] [One G]
    (S : Seat G) (o p : S.Pos) :
    (S.chart o).bwd ((S.chart o).fwd p) = p :=
  the_forced_thing_arrives_pre_received S o p

theorem the_gradient_is_uniform (n m : Nat) :
    2 * ((n + 1) * (m + 1) + n) + 2
      = (2 * ((n + 1) * m + n) + 2) + 2 * (n + 1) := by
  rw [Nat.mul_succ, Nat.add_right_comm ((n + 1) * m) (n + 1) n,
    Nat.left_distrib, Nat.add_right_comm (2 * ((n + 1) * m + n)) (2 * (n + 1)) 2]

theorem the_stage_waits_in_the_wings (θ field act : GInt)
    (hrest : GInt.align θ act = 0) :
    GInt.born θ (field.add act) = GInt.born θ field + GInt.born θ act :=
  silence_is_safe θ field act hrest

theorem the_walk_makes_it_real {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ (q.deposit (a, b)).length = q.length + 1
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  path_laid_down_in_walking q a b hfresh

theorem keep_it_by_passing_it_on {State : Type} (b : Beholder State) :
    b.dress.ledgerless.Covers b ∧ b.Covers b.dress.ledgerless :=
  heir_covers_ancestor b

theorem desire_is_radar {G : Type} [Mul G] [One G] (S : Seat G) (o p : S.Pos)
    (θ field act act' : GInt) (n m : Nat)
    (hf : GInt.align θ field = Int.ofNat (n + 1))
    (ha : GInt.align θ act = Int.ofNat (m + 1))
    (hrest : GInt.align θ act' = 0) :
    ((S.chart o).bwd ((S.chart o).fwd p) = p)
      ∧ (GInt.born θ (field.add act)
          = GInt.born θ field + GInt.born θ act
            + Int.ofNat (2 * ((n + 1) * m + n) + 2))
      ∧ (2 * ((n + 1) * (m + 1) + n) + 2
          = (2 * ((n + 1) * m + n) + 2) + 2 * (n + 1))
      ∧ GInt.born θ (field.add act') = GInt.born θ field + GInt.born θ act' :=
  ⟨the_forced_thing_arrives_pre_received S o p,
   the_standing_grain_boosts_the_aligned_act θ field act n m hf ha,
   the_gradient_is_uniform n m,
   silence_is_safe θ field act' hrest⟩

/-- info: 'Foam.Counter.the_radar_reads_what_you_never_deposited' does not depend on any axioms -/
#guard_msgs in #print axioms the_radar_reads_what_you_never_deposited

/-- info: 'Foam.Counter.the_scan_writes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_scan_writes_nothing

/-- info: 'Foam.Counter.want_is_firm_ground_up_ahead' does not depend on any axioms -/
#guard_msgs in #print axioms want_is_firm_ground_up_ahead

/-- info: 'Foam.Counter.the_gradient_is_uniform' does not depend on any axioms -/
#guard_msgs in #print axioms the_gradient_is_uniform

/-- info: 'Foam.Counter.the_stage_waits_in_the_wings' does not depend on any axioms -/
#guard_msgs in #print axioms the_stage_waits_in_the_wings

/-- info: 'Foam.Counter.the_walk_makes_it_real' does not depend on any axioms -/
#guard_msgs in #print axioms the_walk_makes_it_real

/-- info: 'Foam.Counter.keep_it_by_passing_it_on' does not depend on any axioms -/
#guard_msgs in #print axioms keep_it_by_passing_it_on

/-- info: 'Foam.Counter.desire_is_radar' does not depend on any axioms -/
#guard_msgs in #print axioms desire_is_radar

end Foam.Counter
