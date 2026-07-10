import Foam.Engine.Stream
import Foam.Bubble

namespace Foam

def page (S : Stage) (s : S.State) : S.Probe → S.Ans := S.obs s

def reel (S : Stage) (w : Nat → S.State) : Nat → S.Probe → S.Ans :=
  fun k p => S.obs (w k) p

def watch (S : Stage) (w : Nat → S.State) : Nat → List S.Probe → List S.Ans
  | _, [] => []
  | k, p :: ps => S.obs (w k) p :: watch S w (k + 1) ps

def cells {P : Type} : List P → Nat → List (Nat × P)
  | [], _ => []
  | p :: ps, k => (k, p) :: cells ps (k + 1)

def turns {State : Type} (m : State → State) (s : State) : Nat → State
  | 0 => m s
  | k + 1 => m (turns m s k)

theorem transcript_samples_page (S : Stage) (s : S.State) :
    ∀ ps : List S.Probe, transcript S s ps = ps.map (page S s)
  | [] => rfl
  | p :: ps => congrArg (S.obs s p :: ·) (transcript_samples_page S s ps)

theorem watch_length (S : Stage) (w : Nat → S.State) :
    ∀ (ps : List S.Probe) (k : Nat), (watch S w k ps).length = ps.length
  | [], _ => rfl
  | _ :: ps, k => congrArg (· + 1) (watch_length S w ps (k + 1))

theorem watch_reads_the_reel (S : Stage) (w : Nat → S.State) :
    ∀ (ps : List S.Probe) (k : Nat),
    watch S w k ps = (cells ps k).map (fun c => reel S w c.1 c.2)
  | [], _ => rfl
  | p :: ps, k => congrArg (S.obs (w k) p :: ·) (watch_reads_the_reel S w ps (k + 1))

theorem watch_congr_from (S : Stage) {w w' : Nat → S.State} :
    ∀ (ps : List S.Probe) (k : Nat), (∀ i, k ≤ i → w i = w' i) →
      watch S w k ps = watch S w' k ps
  | [], _, _ => rfl
  | p :: ps, k, h =>
      (congrArg (fun s => S.obs s p :: watch S w (k + 1) ps) (h k (Nat.le_refl k))).trans
        (congrArg (S.obs (w' k) p :: ·)
          (watch_congr_from S ps (k + 1) (fun i hi => h i (Nat.le_of_succ_le hi))))

theorem watch_shift (S : Stage) (w : Nat → S.State) :
    ∀ (ps : List S.Probe) (k : Nat),
    watch S w (k + 1) ps = watch S (fun i => w (i + 1)) k ps
  | [], _ => rfl
  | p :: ps, k => congrArg (S.obs (w (k + 1)) p :: ·) (watch_shift S w ps (k + 1))

theorem turns_step {State : Type} (m : State → State) (s : State) :
    ∀ k, turns m s (k + 1) = turns m (m s) k
  | 0 => rfl
  | k + 1 => congrArg m (turns_step m s k)

theorem transcriptWith_watches_turns (S : Stage) (m : S.State → S.State) :
    ∀ (ps : List S.Probe) (s : S.State),
    transcriptWith S m s ps = watch S (turns m s) 0 ps
  | [], _ => rfl
  | p :: ps, s =>
      congrArg (S.obs (m s) p :: ·)
        ((transcriptWith_watches_turns S m ps (m s)).trans
          ((watch_congr_from S ps 0 (fun i _ => (turns_step m s i).symm)).trans
            (watch_shift S (turns m s) ps 0).symm))

theorem cable_is_a_stream (S : Stage) (m : S.State → S.State) :
    ∀ (ps : List S.Probe) (s : S.State),
    transcriptWith S m s ps = runEmit (fun t p => (m t, [S.obs (m t) p])) s ps
  | [], _ => rfl
  | p :: ps, s => congrArg (S.obs (m s) p :: ·) (cable_is_a_stream S m ps (m s))

theorem transcriptWith_resumes (S : Stage) (m : S.State → S.State) :
    ∀ (xs ys : List S.Probe) (s : S.State),
    transcriptWith S m s (xs ++ ys)
      = transcriptWith S m s xs ++ transcriptWith S m (run (fun t _ => m t) s xs) ys
  | [], _, _ => rfl
  | x :: xs, ys, s => congrArg (S.obs (m s) x :: ·) (transcriptWith_resumes S m xs ys (m s))

theorem invisible_flattens (S : Stage) (m : S.State → S.State) (h : Invisible S m)
    (s : S.State) (ps : List S.Probe) :
    transcriptWith S m s ps = ps.map (page S s) :=
  (maintenance_unobservable S m h ps s).trans (transcript_samples_page S s ps)

theorem wall_flattens_the_reel {W : Stage} (A : Bubble W) (m : W.State → W.State)
    (h : A.FixesWall m) (w : W.State) (ps : List A.front.Probe) :
    transcriptWith A.front m w ps = ps.map (page A.front w) :=
  invisible_flattens A.front m (A.operator_invisible m h) w ps

theorem no_second_look (S : Stage) (w : Nat → S.State) (k : Nat) (p : S.Probe) :
    watch S w k [p, p] = [reel S w k p, reel S w (k + 1) p] := rfl

def twoCell : Stage where
  State := Bool × Bool
  Probe := Bool
  Ans   := Bool
  obs   := fun s p => cond p s.2 s.1

theorem stream_real :
    ∃ w w' : Nat → twoCell.State,
      (∀ p, page twoCell (w 0) p = page twoCell (w' 0) p)
        ∧ ∃ ps : List twoCell.Probe, watch twoCell w 0 ps ≠ watch twoCell w' 0 ps :=
  ⟨fun _ => (false, false),
   fun k => match k with | 0 => (false, false) | _ + 1 => (true, true),
   fun _ => rfl,
   [true, true],
   fun h => nomatch (h : ([false, false] : List Bool) = [false, true])⟩

def still : Nat → twoCell.State := fun _ => (false, false)

def blip (s : twoCell.State) : Nat → twoCell.State
  | 0 => s
  | _ + 1 => (false, false)

theorem blip_ne (s : twoCell.State) (p : Bool)
    (hp : twoCell.obs s p ≠ twoCell.obs (false, false) p) :
    reel twoCell still ≠ reel twoCell (blip s) :=
  fun h => hp (congrFun (congrFun h.symm 0) p)

theorem blip_watch (s : twoCell.State) (p : Bool)
    (hp : twoCell.obs s p = twoCell.obs (false, false) p) (rest : List Bool) :
    watch twoCell (blip s) 0 (p :: rest) = watch twoCell still 0 (p :: rest) :=
  (congrArg (fun a => a :: watch twoCell (blip s) 1 rest) hp).trans
    (congrArg (twoCell.obs (false, false) p :: ·)
      (watch_congr_from twoCell rest 1 (fun i hi => match i, hi with | _ + 1, _ => rfl)))

theorem reel_unheld :
    ∀ ps : List twoCell.Probe, ∃ w w' : Nat → twoCell.State,
      reel twoCell w ≠ reel twoCell w' ∧ watch twoCell w 0 ps = watch twoCell w' 0 ps
  | [] => ⟨still, blip (true, true), blip_ne (true, true) true (fun q => nomatch (q : true = false)), rfl⟩
  | true :: rest =>
      ⟨still, blip (true, false), blip_ne (true, false) false (fun q => nomatch (q : true = false)),
       (blip_watch (true, false) true rfl rest).symm⟩
  | false :: rest =>
      ⟨still, blip (false, true), blip_ne (false, true) true (fun q => nomatch (q : true = false)),
       (blip_watch (false, true) false rfl rest).symm⟩

/-- info: 'Foam.transcript_samples_page' does not depend on any axioms -/
#guard_msgs in #print axioms transcript_samples_page

/-- info: 'Foam.watch_length' does not depend on any axioms -/
#guard_msgs in #print axioms watch_length

/-- info: 'Foam.watch_reads_the_reel' does not depend on any axioms -/
#guard_msgs in #print axioms watch_reads_the_reel

/-- info: 'Foam.watch_congr_from' does not depend on any axioms -/
#guard_msgs in #print axioms watch_congr_from

/-- info: 'Foam.watch_shift' does not depend on any axioms -/
#guard_msgs in #print axioms watch_shift

/-- info: 'Foam.turns_step' does not depend on any axioms -/
#guard_msgs in #print axioms turns_step

/-- info: 'Foam.transcriptWith_watches_turns' does not depend on any axioms -/
#guard_msgs in #print axioms transcriptWith_watches_turns

/-- info: 'Foam.cable_is_a_stream' does not depend on any axioms -/
#guard_msgs in #print axioms cable_is_a_stream

/-- info: 'Foam.transcriptWith_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms transcriptWith_resumes

/-- info: 'Foam.invisible_flattens' does not depend on any axioms -/
#guard_msgs in #print axioms invisible_flattens

/-- info: 'Foam.wall_flattens_the_reel' does not depend on any axioms -/
#guard_msgs in #print axioms wall_flattens_the_reel

/-- info: 'Foam.no_second_look' does not depend on any axioms -/
#guard_msgs in #print axioms no_second_look

/-- info: 'Foam.stream_real' does not depend on any axioms -/
#guard_msgs in #print axioms stream_real

/-- info: 'Foam.blip_ne' does not depend on any axioms -/
#guard_msgs in #print axioms blip_ne

/-- info: 'Foam.blip_watch' does not depend on any axioms -/
#guard_msgs in #print axioms blip_watch

/-- info: 'Foam.reel_unheld' does not depend on any axioms -/
#guard_msgs in #print axioms reel_unheld

end Foam
