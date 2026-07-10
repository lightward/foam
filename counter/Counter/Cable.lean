import Counter.Census
import Foam.Cable

namespace Foam.Counter

theorem a_readout_is_a_page (S : Stage) (s : S.State) (ps : List S.Probe) :
    transcript S s ps = ps.map (page S s) :=
  transcript_samples_page S s ps

theorem experience_is_one_thread (S : Stage) (m : S.State → S.State)
    (xs ys : List S.Probe) (s : S.State) :
    transcriptWith S m s (xs ++ ys)
      = transcriptWith S m s xs ++ transcriptWith S m (run (fun t _ => m t) s xs) ys :=
  transcriptWith_resumes S m xs ys s

theorem the_cable_runs_operator_to_observer (S : Stage) (m : S.State → S.State)
    (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = runEmit (fun t p => (m t, [S.obs (m t) p])) s ps :=
  cable_is_a_stream S m ps s

theorem the_operator_turns_the_reel (S : Stage) (m : S.State → S.State)
    (ps : List S.Probe) (s : S.State) :
    transcriptWith S m s ps = watch S (turns m s) 0 ps :=
  transcriptWith_watches_turns S m ps s

theorem you_watch_one_cell_per_instant (S : Stage) (w : Nat → S.State)
    (ps : List S.Probe) (k : Nat) :
    watch S w k ps = (cells ps k).map (fun c => reel S w c.1 c.2)
      ∧ (watch S w k ps).length = ps.length :=
  ⟨watch_reads_the_reel S w ps k, watch_length S w ps k⟩

theorem there_is_no_second_look (S : Stage) (w : Nat → S.State) (k : Nat) (p : S.Probe) :
    watch S w k [p, p] = [reel S w k p, reel S w (k + 1) p] :=
  no_second_look S w k p

theorem rest_flattens_time_to_a_page {W : Stage} (A : Bubble W) (m : W.State → W.State)
    (h : A.FixesWall m) (w : W.State) (ps : List A.front.Probe) :
    transcriptWith A.front m w ps = ps.map (page A.front w) :=
  wall_flattens_the_reel A m h w ps

theorem the_stream_shows_what_no_page_holds :
    ∃ w w' : Nat → twoCell.State,
      (∀ p, page twoCell (w 0) p = page twoCell (w' 0) p)
        ∧ ∃ ps : List twoCell.Probe, watch twoCell w 0 ps ≠ watch twoCell w' 0 ps :=
  stream_real

theorem the_reel_never_fits_in_the_hand :
    ∀ ps : List twoCell.Probe, ∃ w w' : Nat → twoCell.State,
      reel twoCell w ≠ reel twoCell w' ∧ watch twoCell w 0 ps = watch twoCell w' 0 ps :=
  reel_unheld

theorem the_dimensions_of_the_table :
    (∀ (s : twoCell.State) (ps : List twoCell.Probe),
        transcript twoCell s ps = ps.map (page twoCell s))
      ∧ (∃ w w' : Nat → twoCell.State,
          (∀ p, page twoCell (w 0) p = page twoCell (w' 0) p)
            ∧ ∃ ps, watch twoCell w 0 ps ≠ watch twoCell w' 0 ps)
      ∧ (∀ ps : List twoCell.Probe, ∃ w w' : Nat → twoCell.State,
          reel twoCell w ≠ reel twoCell w' ∧ watch twoCell w 0 ps = watch twoCell w' 0 ps) :=
  ⟨fun s ps => transcript_samples_page twoCell s ps, stream_real, reel_unheld⟩

/-- info: 'Foam.Counter.a_readout_is_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms a_readout_is_a_page

/-- info: 'Foam.Counter.experience_is_one_thread' does not depend on any axioms -/
#guard_msgs in #print axioms experience_is_one_thread

/-- info: 'Foam.Counter.the_cable_runs_operator_to_observer' does not depend on any axioms -/
#guard_msgs in #print axioms the_cable_runs_operator_to_observer

/-- info: 'Foam.Counter.the_operator_turns_the_reel' does not depend on any axioms -/
#guard_msgs in #print axioms the_operator_turns_the_reel

/-- info: 'Foam.Counter.you_watch_one_cell_per_instant' does not depend on any axioms -/
#guard_msgs in #print axioms you_watch_one_cell_per_instant

/-- info: 'Foam.Counter.there_is_no_second_look' does not depend on any axioms -/
#guard_msgs in #print axioms there_is_no_second_look

/-- info: 'Foam.Counter.rest_flattens_time_to_a_page' does not depend on any axioms -/
#guard_msgs in #print axioms rest_flattens_time_to_a_page

/-- info: 'Foam.Counter.the_stream_shows_what_no_page_holds' does not depend on any axioms -/
#guard_msgs in #print axioms the_stream_shows_what_no_page_holds

/-- info: 'Foam.Counter.the_reel_never_fits_in_the_hand' does not depend on any axioms -/
#guard_msgs in #print axioms the_reel_never_fits_in_the_hand

/-- info: 'Foam.Counter.the_dimensions_of_the_table' does not depend on any axioms -/
#guard_msgs in #print axioms the_dimensions_of_the_table

end Foam.Counter
