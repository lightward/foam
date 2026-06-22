namespace Foam

def run {S B : Type} (step : S → B → S) (init : S) (stream : List B) : S :=
  stream.foldl step init

theorem run_resumes {S B : Type} (step : S → B → S) :
    ∀ (init : S) (xs ys : List B),
    run step init (xs ++ ys) = run step (run step init xs) ys
  | _,    [],      _  => rfl
  | init, x :: xs, ys => run_resumes step (step init x) xs ys

def runState {S B O : Type} (step : S → B → S × List O) : S → List B → S :=
  run (fun s b => (step s b).1)

def runEmit {S B O : Type} (step : S → B → S × List O) (init : S) : List B → List O
  | []      => []
  | b :: bs => (step init b).2 ++ runEmit step (step init b).1 bs

def output {S B O : Type} (step : S → B → S × List O) (flush : S → List O)
    (init : S) (stream : List B) : List O :=
  runEmit step init stream ++ flush (runState step init stream)

theorem runState_resumes {S B O : Type} (step : S → B → S × List O)
    (init : S) (xs ys : List B) :
    runState step init (xs ++ ys) = runState step (runState step init xs) ys :=
  run_resumes (fun s b => (step s b).1) init xs ys

theorem appendAssoc {α : Type} :
    ∀ (as bs cs : List α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
  | [],      _,  _  => rfl
  | a :: as, bs, cs => congrArg (a :: ·) (appendAssoc as bs cs)

theorem appendNil {α : Type} : ∀ (as : List α), as ++ [] = as
  | []      => rfl
  | a :: as => congrArg (a :: ·) (appendNil as)

theorem runEmit_resumes {S B O : Type} (step : S → B → S × List O) :
    ∀ (init : S) (xs ys : List B),
    runEmit step init (xs ++ ys)
      = runEmit step init xs ++ runEmit step (runState step init xs) ys
  | _,    [],      _  => rfl
  | init, x :: xs, ys =>
      (congrArg ((step init x).2 ++ ·) (runEmit_resumes step (step init x).1 xs ys)).trans
        (appendAssoc (step init x).2
          (runEmit step (step init x).1 xs)
          (runEmit step (runState step (step init x).1 xs) ys)).symm

theorem output_resumes {S B O : Type} (step : S → B → S × List O) (flush : S → List O)
    (init : S) (xs ys : List B) :
    output step flush init (xs ++ ys)
      = runEmit step init xs ++ output step flush (runState step init xs) ys := by
  show runEmit step init (xs ++ ys) ++ flush (runState step init (xs ++ ys))
     = runEmit step init xs ++ (runEmit step (runState step init xs) ys
        ++ flush (runState step (runState step init xs) ys))
  rw [runEmit_resumes, runState_resumes, appendAssoc]

def enc {B : Type} (xs : List B) : List (B × B) := xs.map (fun b => (b, b))

def dec {B : Type} (ys : List (B × B)) : List B := ys.map Prod.fst

theorem lossless_tag {B : Type} : ∀ xs : List B, dec (enc xs) = xs
  | []      => rfl
  | x :: xs => congrArg (x :: ·) (lossless_tag xs)

/-- info: 'Foam.run_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms run_resumes

/-- info: 'Foam.runState_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms runState_resumes

/-- info: 'Foam.appendAssoc' does not depend on any axioms -/
#guard_msgs in #print axioms appendAssoc

/-- info: 'Foam.appendNil' does not depend on any axioms -/
#guard_msgs in #print axioms appendNil

/-- info: 'Foam.runEmit_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms runEmit_resumes

/-- info: 'Foam.output_resumes' does not depend on any axioms -/
#guard_msgs in #print axioms output_resumes

/-- info: 'Foam.lossless_tag' does not depend on any axioms -/
#guard_msgs in #print axioms lossless_tag

end Foam
