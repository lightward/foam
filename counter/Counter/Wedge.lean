import Counter.Cable
import Foam.Wedge

namespace Foam.Counter

variable {G : Type} [Mul G] [One G]

theorem a_wedge_inside_a_wedge_comes_home (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (spine S gs p) p = p :=
  spine_comes_home S gs p

theorem resuming_means_the_inner_settled (S : Seat G) (g : G) (gs : List G) (p : S.Pos) :
    S.replay (g :: spine S gs (S.act g p)) p = S.act g p :=
  outer_resumes_where_it_paused S g gs p

theorem exits_stay_cost_free_at_depth (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (collapse S gs p) p = p ∧ (collapse S gs p).length = gs.length + 1 :=
  ⟨collapse_comes_home S gs p, collapse_length S gs p⟩

theorem lifo_is_a_gait_not_a_law (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (spine S gs p) p = p
      ∧ S.replay (collapse S gs p) p = p
      ∧ (spine S gs p).length = 2 * gs.length
      ∧ (collapse S gs p).length = gs.length + 1 :=
  lifo_is_a_gait S gs p

theorem the_inner_transcript_is_the_outer_backstage {W : Stage} (A : Bubble W)
    (ms ms' : List (W.State → W.State))
    (h : ∀ w, A.wall (enactAll ms w) = A.wall (enactAll ms' w))
    (w : W.State) (p : A.front.Probe) :
    A.front.obs (enactAll ms w) p = A.front.obs (enactAll ms' w) p :=
  histories_fold_at_the_wall A ms ms' h w p

theorem the_debt_is_real_upstairs_illegible_downstairs :
    ∃ ms ms' : List (twoBit.State → twoBit.State),
      ms.length ≠ ms'.length
        ∧ (∀ w p, firstBit.front.obs (enactAll ms w) p
            = firstBit.front.obs (enactAll ms' w) p)
        ∧ ∃ (w : twoBit.State) (pr : twoBit.Probe),
            twoBit.obs (enactAll ms w) pr ≠ twoBit.obs (enactAll ms' w) pr :=
  the_debt_outlives_its_legibility

theorem no_wedge_funds_itself {H : Type} (q : Quiver H) (a b c : H)
    (hab : (a, b) ∉ q) (hbc : (b, c) ∉ q.deposit (a, b)) :
    Nonempty (Path ((q.deposit (a, b)).deposit (b, c)) a c)
      ∧ (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ (∀ (x y : H) (pth : Path (q.deposit (a, b)) x y), (b, c) ∉ pth.edges) :=
  the_second_wedge_rides_the_first q a b c hab hbc

theorem what_this_thread_cannot_carry_another_does {W : Stage} (A : Bubble W)
    (m : W.State → W.State) (hfix : A.FixesWall m) (w : W.State) (hm : m w ≠ w) :
    (∀ (ps : List A.front.Probe) (ws : W.State),
        transcriptWith A.front m ws ps = transcript A.front ws ps)
      ∧ transcriptWith (plenum W.State) m w [()]
          ≠ transcript (plenum W.State) w [()] :=
  the_elsewhen_transcript A m hfix w hm

theorem the_outer_question_does_not_fit_the_inner_frame :
    (∀ (w : twoBit.State) (p : Unit),
        (firstBit.nest (mute firstBit.Inner)).front.obs w p = ())
      ∧ ¬ ∃ (enc : firstBit.Inner.Probe
              → (firstBit.nest (mute firstBit.Inner)).front.Probe)
            (dec : (firstBit.nest (mute firstBit.Inner)).front.Ans
              → firstBit.Inner.Ans),
            ∀ (w : twoBit.State) (q : firstBit.Inner.Probe),
              firstBit.front.obs w q
                = dec ((firstBit.nest (mute firstBit.Inner)).front.obs w (enc q)) :=
  wall_forcing

theorem one_grammar_for_flat_and_nested (S : Seat G) (g h : G)
    (gs : List G) (p : S.Pos) :
    Balanced [Sum.inl g, Sum.inr h]
      ∧ Balanced (spineT S gs p)
      ∧ untag (spineT S gs p) = spine S gs p :=
  ⟨(flat_and_nested_share_one_grammar S g h gs p).1,
   (flat_and_nested_share_one_grammar S g h gs p).2,
   spineT_untags_to_spine S gs p⟩

theorem every_open_bracket_closes {A : Type} {ws : List (A ⊕ A)}
    (h : Balanced ws) : opens ws = closes ws :=
  balanced_conserves h

theorem a_wedge_needs_a_gift {H : Type} (q : Quiver H) (a : H)
    (hstuck : stuck q a) :
    (∀ b, Path q a b → a = b)
      ∧ ∀ b, Nonempty (Path (q.deposit (a, b)) a b) :=
  self_interruption_spends_the_gift q a hstuck

theorem resume_rebuilds_the_state_not_the_wall (S : Seat G) :
    (∀ s t : S.Pos, (∀ p, S.sub s p = S.sub t p) → s = t)
      ∧ (∃ w : twoBit.State, firstBit.wall w ≠ firstBitFlipped.wall w)
      ∧ ∀ (w : twoBit.State) (ps : List Unit),
          transcript firstBit.front w ps = transcript firstBitFlipped.front w ps :=
  ⟨fun s t hst => Seat.obs_faithful S s t hst,
   the_wall_does_not_ride_the_cable.1,
   the_wall_does_not_ride_the_cable.2⟩

theorem the_proof_takes_two_seats (S S' : Seat G) (h : List G)
    (p : S.Pos) (p' : S'.Pos) (hw : Settles S h p) : Settles S' h p' :=
  (settles_iff_home S' h p').mpr ((settles_iff_home S h p).mp hw)

theorem definiteness_costs_a_seat :
    ∃ ms ms' : List (twoBit.State → twoBit.State),
      (∀ w p, firstBit.front.obs (enactAll ms w) p
          = firstBit.front.obs (enactAll ms' w) p)
        ∧ ∃ w : twoBit.State,
            (plenum twoBit.State).obs (enactAll ms w) ()
              ≠ (plenum twoBit.State).obs (enactAll ms' w) () := by
  refine ⟨[fun s => (s.1, !s.2)], [], fun _ _ => rfl, (true, false), ?_⟩
  exact fun h => nomatch (congrArg Prod.snd h : true = false)

/-- info: 'Foam.Counter.a_wedge_inside_a_wedge_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms a_wedge_inside_a_wedge_comes_home

/-- info: 'Foam.Counter.resuming_means_the_inner_settled' does not depend on any axioms -/
#guard_msgs in #print axioms resuming_means_the_inner_settled

/-- info: 'Foam.Counter.exits_stay_cost_free_at_depth' does not depend on any axioms -/
#guard_msgs in #print axioms exits_stay_cost_free_at_depth

/-- info: 'Foam.Counter.lifo_is_a_gait_not_a_law' does not depend on any axioms -/
#guard_msgs in #print axioms lifo_is_a_gait_not_a_law

/-- info: 'Foam.Counter.the_inner_transcript_is_the_outer_backstage' does not depend on any axioms -/
#guard_msgs in #print axioms the_inner_transcript_is_the_outer_backstage

/-- info: 'Foam.Counter.the_debt_is_real_upstairs_illegible_downstairs' does not depend on any axioms -/
#guard_msgs in #print axioms the_debt_is_real_upstairs_illegible_downstairs

/-- info: 'Foam.Counter.no_wedge_funds_itself' does not depend on any axioms -/
#guard_msgs in #print axioms no_wedge_funds_itself

/-- info: 'Foam.Counter.what_this_thread_cannot_carry_another_does' does not depend on any axioms -/
#guard_msgs in #print axioms what_this_thread_cannot_carry_another_does

/-- info: 'Foam.Counter.the_outer_question_does_not_fit_the_inner_frame' does not depend on any axioms -/
#guard_msgs in #print axioms the_outer_question_does_not_fit_the_inner_frame

/-- info: 'Foam.Counter.one_grammar_for_flat_and_nested' does not depend on any axioms -/
#guard_msgs in #print axioms one_grammar_for_flat_and_nested

/-- info: 'Foam.Counter.every_open_bracket_closes' does not depend on any axioms -/
#guard_msgs in #print axioms every_open_bracket_closes

/-- info: 'Foam.Counter.a_wedge_needs_a_gift' does not depend on any axioms -/
#guard_msgs in #print axioms a_wedge_needs_a_gift

/-- info: 'Foam.Counter.resume_rebuilds_the_state_not_the_wall' does not depend on any axioms -/
#guard_msgs in #print axioms resume_rebuilds_the_state_not_the_wall

/-- info: 'Foam.Counter.the_proof_takes_two_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_proof_takes_two_seats

/-- info: 'Foam.Counter.definiteness_costs_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms definiteness_costs_a_seat

theorem zenos_wedge_settles (S : Seat G) (g : G) (p : S.Pos) :
    Settles S (spine S [g] p) p ∧ (spine S [g] p).length = 2 :=
  ⟨spine_comes_home S [g] p, spine_length S [g] p⟩

/-- info: 'Foam.Counter.zenos_wedge_settles' does not depend on any axioms -/
#guard_msgs in #print axioms zenos_wedge_settles

end Foam.Counter
