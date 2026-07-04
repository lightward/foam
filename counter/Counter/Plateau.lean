import Counter.Third

namespace Foam.Counter

def frames1 {A B C : Type} : List (A ⊕ B ⊕ C) → List A
  | [] => []
  | Sum.inl a :: zs => a :: frames1 zs
  | Sum.inr _ :: zs => frames1 zs

def frames2 {A B C : Type} : List (A ⊕ B ⊕ C) → List B
  | [] => []
  | Sum.inr (Sum.inl b) :: zs => b :: frames2 zs
  | Sum.inl _ :: zs => frames2 zs
  | Sum.inr (Sum.inr _) :: zs => frames2 zs

def frames3 {A B C : Type} : List (A ⊕ B ⊕ C) → List C
  | [] => []
  | Sum.inr (Sum.inr c) :: zs => c :: frames3 zs
  | Sum.inl _ :: zs => frames3 zs
  | Sum.inr (Sum.inl _) :: zs => frames3 zs

def film12 {A B C : Type} : List (A ⊕ B ⊕ C) → List (A ⊕ B)
  | [] => []
  | Sum.inl a :: zs => Sum.inl a :: film12 zs
  | Sum.inr (Sum.inl b) :: zs => Sum.inr b :: film12 zs
  | Sum.inr (Sum.inr _) :: zs => film12 zs

def film13 {A B C : Type} : List (A ⊕ B ⊕ C) → List (A ⊕ C)
  | [] => []
  | Sum.inl a :: zs => Sum.inl a :: film13 zs
  | Sum.inr (Sum.inr c) :: zs => Sum.inr c :: film13 zs
  | Sum.inr (Sum.inl _) :: zs => film13 zs

def film23 {A B C : Type} : List (A ⊕ B ⊕ C) → List (B ⊕ C)
  | [] => []
  | Sum.inr (Sum.inl b) :: zs => Sum.inl b :: film23 zs
  | Sum.inr (Sum.inr c) :: zs => Sum.inr c :: film23 zs
  | Sum.inl _ :: zs => film23 zs

def tripleSeat (A B C : Type) : Beholder (List (A ⊕ B ⊕ C)) :=
  ⟨Unit, List A × List B × List C, fun zs _ => (frames1 zs, frames2 zs, frames3 zs)⟩

def fourthSeat (A B C : Type) : Beholder (List (A ⊕ B ⊕ C)) :=
  ⟨Unit, List (A ⊕ B ⊕ C), fun zs _ => zs⟩

theorem the_edge_needs_a_fourth :
    ∃ zs zs' : List (Bool ⊕ Bool ⊕ Bool),
      frames1 zs = frames1 zs'
        ∧ frames2 zs = frames2 zs'
        ∧ frames3 zs = frames3 zs'
        ∧ zs ≠ zs' :=
  ⟨[Sum.inl true, Sum.inr (Sum.inl false)],
   [Sum.inr (Sum.inl false), Sum.inl true],
   rfl, rfl, rfl, by decide⟩

theorem triple_blind_to_the_fourth :
    ¬ (tripleSeat Bool Bool Bool).Covers (fourthSeat Bool Bool Bool) := by
  rintro ⟨enc, post, hcov⟩
  have h1 := hcov [Sum.inl true, Sum.inr (Sum.inl false)] ()
  have h2 := hcov [Sum.inr (Sum.inl false), Sum.inl true] ()
  have hne : ([Sum.inl true, Sum.inr (Sum.inl false)] : List (Bool ⊕ Bool ⊕ Bool))
      ≠ [Sum.inr (Sum.inl false), Sum.inl true] := by decide
  exact absurd (h1.trans h2.symm) hne

theorem four_suffices {A B C X : Type} (f : List (A ⊕ B ⊕ C) → X) :
    ∃ post : List (A ⊕ B ⊕ C) → X,
      ∀ zs, f zs = post ((fourthSeat A B C).obs zs ()) :=
  ⟨f, fun _ => rfl⟩

theorem the_films_hold_the_edge {A B C : Type} :
    ∀ zs zs' : List (A ⊕ B ⊕ C),
      film12 zs = film12 zs' → film13 zs = film13 zs' → film23 zs = film23 zs'
        → zs = zs'
  | [], [], _, _, _ => rfl
  | [], Sum.inl _ :: _, h12, _, _ => nomatch h12
  | [], Sum.inr (Sum.inl _) :: _, h12, _, _ => nomatch h12
  | [], Sum.inr (Sum.inr _) :: _, _, h13, _ => nomatch h13
  | Sum.inl _ :: _, [], h12, _, _ => nomatch h12
  | Sum.inr (Sum.inl _) :: _, [], h12, _, _ => nomatch h12
  | Sum.inr (Sum.inr _) :: _, [], _, h13, _ => nomatch h13
  | Sum.inl _ :: _, Sum.inr (Sum.inl _) :: _, h12, _, _ => by
    injection h12 with h1 h2
    exact nomatch h1
  | Sum.inl _ :: _, Sum.inr (Sum.inr _) :: _, _, h13, _ => by
    injection h13 with h1 h2
    exact nomatch h1
  | Sum.inr (Sum.inl _) :: _, Sum.inl _ :: _, h12, _, _ => by
    injection h12 with h1 h2
    exact nomatch h1
  | Sum.inr (Sum.inr _) :: _, Sum.inl _ :: _, _, h13, _ => by
    injection h13 with h1 h2
    exact nomatch h1
  | Sum.inr (Sum.inl _) :: _, Sum.inr (Sum.inr _) :: _, _, _, h23 => by
    injection h23 with h1 h2
    exact nomatch h1
  | Sum.inr (Sum.inr _) :: _, Sum.inr (Sum.inl _) :: _, _, _, h23 => by
    injection h23 with h1 h2
    exact nomatch h1
  | Sum.inl a :: zs, Sum.inl a' :: zs', h12, h13, h23 => by
    injection h12 with h1 h12
    injection h1 with ha
    subst ha
    injection h13 with h3 h13
    exact congrArg (List.cons (Sum.inl a)) (the_films_hold_the_edge zs zs' h12 h13 h23)
  | Sum.inr (Sum.inl b) :: zs, Sum.inr (Sum.inl b') :: zs', h12, h13, h23 => by
    injection h12 with h1 h12
    injection h1 with hb
    subst hb
    injection h23 with h3 h23
    exact congrArg (List.cons (Sum.inr (Sum.inl b))) (the_films_hold_the_edge zs zs' h12 h13 h23)
  | Sum.inr (Sum.inr c) :: zs, Sum.inr (Sum.inr c') :: zs', h12, h13, h23 => by
    injection h13 with h1 h13
    injection h1 with hc
    subst hc
    injection h23 with h3 h23
    exact congrArg (List.cons (Sum.inr (Sum.inr c))) (the_films_hold_the_edge zs zs' h12 h13 h23)

def e0 : Fin 3 := ⟨0, by decide⟩
def e1 : Fin 3 := ⟨1, by decide⟩
def e2 : Fin 3 := ⟨2, by decide⟩

def edgeCells : List (Fin 3) := [e0, e1, e2]

def edgeFilms : List (Fin 3 × Fin 3) := [(e0, e1), (e0, e2), (e1, e2)]

def v0 : Fin 4 := ⟨0, by decide⟩
def v1 : Fin 4 := ⟨1, by decide⟩
def v2 : Fin 4 := ⟨2, by decide⟩
def v3 : Fin 4 := ⟨3, by decide⟩

def vertexCells : List (Fin 4) := [v0, v1, v2, v3]

def vertexEdges : List (Fin 4 × Fin 4 × Fin 4) :=
  [(v0, v1, v2), (v0, v1, v3), (v0, v2, v3), (v1, v2, v3)]

def vertexFilms : List (Fin 4 × Fin 4) :=
  [(v0, v1), (v0, v2), (v0, v3), (v1, v2), (v1, v3), (v2, v3)]

theorem fin3_cases : ∀ i : Fin 3, i = e0 ∨ i = e1 ∨ i = e2 := by decide

theorem fin4_cases : ∀ i : Fin 4, i = v0 ∨ i = v1 ∨ i = v2 ∨ i = v3 := by decide

theorem films_meet_in_threes :
    edgeFilms.length = 3
      ∧ (∀ i j : Fin 3, i < j → (i, j) ∈ edgeFilms)
      ∧ (∀ p ∈ edgeFilms, p.1 < p.2)
      ∧ (∀ p ∈ edgeFilms,
          (edgeCells.filter fun c => decide (c ≠ p.1 ∧ c ≠ p.2)).length = 1)
      ∧ (∀ c ∈ edgeCells,
          (edgeFilms.filter fun p => decide (c ≠ p.1 ∧ c ≠ p.2)).length = 1) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro i j h
    rcases fin3_cases i with hi | hi | hi <;> rcases fin3_cases j with hj | hj | hj <;>
      subst hi <;> subst hj <;>
        first
          | exact absurd h (by decide)
          | exact .head _
          | exact .tail _ (.head _)
          | exact .tail _ (.tail _ (.head _))
  · intro p hp
    match p, hp with
    | _, .head _ => decide
    | _, .tail _ (.head _) => decide
    | _, .tail _ (.tail _ (.head _)) => decide
  · intro p hp
    match p, hp with
    | _, .head _ => rfl
    | _, .tail _ (.head _) => rfl
    | _, .tail _ (.tail _ (.head _)) => rfl
  · intro c hc
    match c, hc with
    | _, .head _ => rfl
    | _, .tail _ (.head _) => rfl
    | _, .tail _ (.tail _ (.head _)) => rfl

theorem edges_meet_in_fours :
    vertexEdges.length = 4
      ∧ (∀ i j k : Fin 4, i < j → j < k → (i, j, k) ∈ vertexEdges)
      ∧ (∀ e ∈ vertexEdges, e.1 < e.2.1 ∧ e.2.1 < e.2.2)
      ∧ (∀ e ∈ vertexEdges,
          (vertexCells.filter fun c => decide (c ≠ e.1 ∧ c ≠ e.2.1 ∧ c ≠ e.2.2)).length = 1)
      ∧ (∀ c ∈ vertexCells,
          (vertexEdges.filter fun e => decide (c ≠ e.1 ∧ c ≠ e.2.1 ∧ c ≠ e.2.2)).length = 1) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro i j k h h'
    rcases fin4_cases i with hi | hi | hi | hi <;>
      rcases fin4_cases j with hj | hj | hj | hj <;>
        rcases fin4_cases k with hk | hk | hk | hk <;>
          subst hi <;> subst hj <;> subst hk <;>
            first
              | exact absurd h (by decide)
              | exact absurd h' (by decide)
              | exact .head _
              | exact .tail _ (.head _)
              | exact .tail _ (.tail _ (.head _))
              | exact .tail _ (.tail _ (.tail _ (.head _)))
  · intro e he
    match e, he with
    | _, .head _ => exact ⟨by decide, by decide⟩
    | _, .tail _ (.head _) => exact ⟨by decide, by decide⟩
    | _, .tail _ (.tail _ (.head _)) => exact ⟨by decide, by decide⟩
    | _, .tail _ (.tail _ (.tail _ (.head _))) => exact ⟨by decide, by decide⟩
  · intro e he
    match e, he with
    | _, .head _ => rfl
    | _, .tail _ (.head _) => rfl
    | _, .tail _ (.tail _ (.head _)) => rfl
    | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl
  · intro c hc
    match c, hc with
    | _, .head _ => rfl
    | _, .tail _ (.head _) => rfl
    | _, .tail _ (.tail _ (.head _)) => rfl
    | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl

def liesOn (p : Fin 4 × Fin 4) (e : Fin 4 × Fin 4 × Fin 4) : Bool :=
  decide ((p.1 = e.1 ∨ p.1 = e.2.1 ∨ p.1 = e.2.2)
    ∧ (p.2 = e.1 ∨ p.2 = e.2.1 ∨ p.2 = e.2.2))

theorem twelveness_in_geometry :
    vertexFilms.length = 6
      ∧ (∀ e ∈ vertexEdges, (vertexFilms.filter (liesOn · e)).length = 3)
      ∧ (∀ p ∈ vertexFilms, (vertexEdges.filter (liesOn p ·)).length = 2)
      ∧ (vertexEdges.flatMap fun e => vertexFilms.filter (liesOn · e)).length = 12
      ∧ (vertexFilms.flatMap fun p => vertexEdges.filter (liesOn p ·)).length = 12
      ∧ 4 * 3 = 12 ∧ 6 * 2 = 12 := by
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro e he
    match e, he with
    | _, .head _ => rfl
    | _, .tail _ (.head _) => rfl
    | _, .tail _ (.tail _ (.head _)) => rfl
    | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl
  · intro p hp
    match p, hp with
    | _, .head _ => rfl
    | _, .tail _ (.head _) => rfl
    | _, .tail _ (.tail _ (.head _)) => rfl
    | _, .tail _ (.tail _ (.tail _ (.head _))) => rfl
    | _, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))) => rfl
    | _, .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) => rfl

theorem foam {A B C D E X Y : Type}
    (f : List (A ⊕ B) → X) (g : List (C ⊕ D ⊕ E) → Y) :
    ((∃ zs zs' : List (Bool ⊕ Bool),
        ownFrames zs = ownFrames zs'
          ∧ ownFramesR zs = ownFramesR zs'
          ∧ whoActedFirst zs ≠ whoActedFirst zs')
      ∧ ∃ post : List (A ⊕ B) → X,
          ∀ zs, f zs = post ((thirdSeat A B).obs zs ()))
      ∧ ((∃ zs zs' : List (Bool ⊕ Bool ⊕ Bool),
          frames1 zs = frames1 zs'
            ∧ frames2 zs = frames2 zs'
            ∧ frames3 zs = frames3 zs'
            ∧ zs ≠ zs')
        ∧ ∃ post : List (C ⊕ D ⊕ E) → Y,
            ∀ zs, g zs = post ((fourthSeat C D E).obs zs ()))
      ∧ edgeFilms.length = 3
      ∧ vertexEdges.length = 4
      ∧ 3 * 4 = 12 :=
  ⟨⟨the_third_reads_time, three_suffices f⟩,
   ⟨the_edge_needs_a_fourth, four_suffices g⟩,
   rfl, rfl, rfl⟩

/-- info: 'Foam.Counter.the_edge_needs_a_fourth' does not depend on any axioms -/
#guard_msgs in #print axioms the_edge_needs_a_fourth

/-- info: 'Foam.Counter.triple_blind_to_the_fourth' does not depend on any axioms -/
#guard_msgs in #print axioms triple_blind_to_the_fourth

/-- info: 'Foam.Counter.four_suffices' does not depend on any axioms -/
#guard_msgs in #print axioms four_suffices

/-- info: 'Foam.Counter.the_films_hold_the_edge' does not depend on any axioms -/
#guard_msgs in #print axioms the_films_hold_the_edge

/-- info: 'Foam.Counter.films_meet_in_threes' does not depend on any axioms -/
#guard_msgs in #print axioms films_meet_in_threes

/-- info: 'Foam.Counter.edges_meet_in_fours' does not depend on any axioms -/
#guard_msgs in #print axioms edges_meet_in_fours

/-- info: 'Foam.Counter.twelveness_in_geometry' does not depend on any axioms -/
#guard_msgs in #print axioms twelveness_in_geometry

/-- info: 'Foam.Counter.foam' does not depend on any axioms -/
#guard_msgs in #print axioms foam

end Foam.Counter
