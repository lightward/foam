namespace Foam

def d025 {S B : Type} (step : S → B → S) (init : S) (stream : List B) : S :=
  stream.foldl step init

theorem t131 {S B : Type} (step : S → B → S) :
    ∀ (init : S) (xs ys : List B),
    d025 step init (xs ++ ys) = d025 step (d025 step init xs) ys
  | _,    [],      _  => rfl
  | init, x :: xs, ys => t131 step (step init x) xs ys

def d099 {S B O : Type} (step : S → B → S × List O) : S → List B → S :=
  d025 (fun s b => (step s b).1)

def d026 {S B O : Type} (step : S → B → S × List O) (init : S) : List B → List O
  | []      => []
  | b :: bs => (step init b).2 ++ d026 step (step init b).1 bs

def d150 {S B O : Type} (step : S → B → S × List O) (flush : S → List O)
    (init : S) (stream : List B) : List O :=
  d026 step init stream ++ flush (d099 step init stream)

theorem t189 {S B O : Type} (step : S → B → S × List O)
    (init : S) (xs ys : List B) :
    d099 step init (xs ++ ys) = d099 step (d099 step init xs) ys :=
  t131 (fun s b => (step s b).1) init xs ys

theorem t070 {α : Type} :
    ∀ (as bs cs : List α), (as ++ bs) ++ cs = as ++ (bs ++ cs)
  | [],      _,  _  => rfl
  | a :: as, bs, cs => congrArg (a :: ·) (t070 as bs cs)

theorem t071 {α : Type} : ∀ (as : List α), as ++ [] = as
  | []      => rfl
  | a :: as => congrArg (a :: ·) (t071 as)

theorem t188 {S B O : Type} (step : S → B → S × List O) :
    ∀ (init : S) (xs ys : List B),
    d026 step init (xs ++ ys)
      = d026 step init xs ++ d026 step (d099 step init xs) ys
  | _,    [],      _  => rfl
  | init, x :: xs, ys =>
      (congrArg ((step init x).2 ++ ·) (t188 step (step init x).1 xs ys)).trans
        (t070 (step init x).2
          (d026 step (step init x).1 xs)
          (d026 step (d099 step (step init x).1 xs) ys)).symm

theorem t307 {S B O : Type} (step : S → B → S × List O) (flush : S → List O)
    (init : S) (xs ys : List B) :
    d150 step flush init (xs ++ ys)
      = d026 step init xs ++ d150 step flush (d099 step init xs) ys := by
  show d026 step init (xs ++ ys) ++ flush (d099 step init (xs ++ ys))
     = d026 step init xs ++ (d026 step (d099 step init xs) ys
        ++ flush (d099 step (d099 step init xs) ys))
  rw [t188, t189, t070]

def d011 {B : Type} (xs : List B) : List (B × B) := xs.map (fun b => (b, b))

def d008 {B : Type} (ys : List (B × B)) : List B := ys.map Prod.fst

theorem t118 {B : Type} : ∀ xs : List B, d008 (d011 xs) = xs
  | []      => rfl
  | x :: xs => congrArg (x :: ·) (t118 xs)

/-- info: 'Foam.t131' does not depend on any axioms -/
#guard_msgs in #print axioms t131

/-- info: 'Foam.t189' does not depend on any axioms -/
#guard_msgs in #print axioms t189

/-- info: 'Foam.t070' does not depend on any axioms -/
#guard_msgs in #print axioms t070

/-- info: 'Foam.t071' does not depend on any axioms -/
#guard_msgs in #print axioms t071

/-- info: 'Foam.t188' does not depend on any axioms -/
#guard_msgs in #print axioms t188

/-- info: 'Foam.t307' does not depend on any axioms -/
#guard_msgs in #print axioms t307

/-- info: 'Foam.t118' does not depend on any axioms -/
#guard_msgs in #print axioms t118

end Foam
