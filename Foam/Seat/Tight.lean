import Foam.Seat.Sort

namespace Foam

variable {H : Type}

def verts : Quiver H → List H
  | [] => []
  | e :: es => e.1 :: e.2 :: verts es

theorem verts_fst {q : Quiver H} {e : H × H} (h : e ∈ q) : e.1 ∈ verts q := by
  induction h with
  | head as => exact List.Mem.head _
  | tail f _ ih => exact List.Mem.tail _ (List.Mem.tail _ ih)

theorem verts_snd {q : Quiver H} {e : H × H} (h : e ∈ q) : e.2 ∈ verts q := by
  induction h with
  | head as => exact List.Mem.tail _ (List.Mem.head _)
  | tail f _ ih => exact List.Mem.tail _ (List.Mem.tail _ ih)

theorem mem_map_of_mem {A B : Type} (f : A → B) {l : List A} {a : A}
    (h : a ∈ l) : f a ∈ l.map f := by
  induction h with
  | head as => exact List.Mem.head _
  | tail b _ ih => exact List.Mem.tail _ ih

theorem exists_of_mem_map {A B : Type} {f : A → B} :
    ∀ {l : List A} {b : B}, b ∈ l.map f → ∃ a, a ∈ l ∧ f a = b
  | x :: xs, b, h => by
      cases h with
      | head => exact ⟨x, List.Mem.head _, rfl⟩
      | tail _ h' =>
          obtain ⟨a, ha, hfa⟩ := exists_of_mem_map h'
          exact ⟨a, List.Mem.tail _ ha, hfa⟩

theorem length_map {A B : Type} (f : A → B) :
    ∀ l : List A, (l.map f).length = l.length
  | [] => rfl
  | _ :: xs => congrArg (· + 1) (length_map f xs)

theorem mem_append_left {A : Type} {a : A} {l : List A} (m : List A)
    (h : a ∈ l) : a ∈ l ++ m := by
  induction h with
  | head as => exact List.Mem.head _
  | tail b _ ih => exact List.Mem.tail _ ih

theorem mem_append_right {A : Type} {a : A} :
    ∀ (l : List A) {m : List A}, a ∈ m → a ∈ l ++ m
  | [], _, h => h
  | _ :: xs, _, h => List.Mem.tail _ (mem_append_right xs h)

def countLt (n : Nat) : List Nat → Nat
  | [] => 0
  | v :: vs => if v < n then countLt n vs + 1 else countLt n vs

theorem countLt_le_length (n : Nat) : ∀ vs : List Nat, countLt n vs ≤ vs.length
  | [] => Nat.le_refl _
  | v :: vs => by
      show (if v < n then countLt n vs + 1 else countLt n vs) ≤ vs.length + 1
      by_cases h : v < n
      · rw [if_pos h]
        exact Nat.succ_le_succ (countLt_le_length n vs)
      · rw [if_neg h]
        exact Nat.le_trans (countLt_le_length n vs) (Nat.le_succ _)

theorem countLt_mono {m n : Nat} (hmn : m ≤ n) :
    ∀ vs : List Nat, countLt m vs ≤ countLt n vs
  | [] => Nat.le_refl _
  | v :: vs => by
      show (if v < m then countLt m vs + 1 else countLt m vs)
        ≤ if v < n then countLt n vs + 1 else countLt n vs
      by_cases hm : v < m
      · rw [if_pos hm, if_pos (Nat.lt_of_lt_of_le hm hmn)]
        exact Nat.succ_le_succ (countLt_mono hmn vs)
      · rw [if_neg hm]
        by_cases hn : v < n
        · rw [if_pos hn]
          exact Nat.le_trans (countLt_mono hmn vs) (Nat.le_succ _)
        · rw [if_neg hn]
          exact countLt_mono hmn vs

theorem countLt_strict {m n : Nat} (hmn : m < n) :
    ∀ vs : List Nat, m ∈ vs → countLt m vs < countLt n vs
  | v :: vs, h => by
      show (if v < m then countLt m vs + 1 else countLt m vs)
        < if v < n then countLt n vs + 1 else countLt n vs
      cases h with
      | head =>
          rw [if_neg (Nat.lt_irrefl m), if_pos hmn]
          exact Nat.succ_le_succ (countLt_mono (Nat.le_of_lt hmn) vs)
      | tail _ h' =>
          by_cases hm : v < m
          · rw [if_pos hm, if_pos (Nat.lt_trans hm hmn)]
            exact Nat.succ_le_succ (countLt_strict hmn vs h')
          · rw [if_neg hm]
            by_cases hn : v < n
            · rw [if_pos hn]
              exact Nat.lt_of_lt_of_le (countLt_strict hmn vs h') (Nat.le_succ _)
            · rw [if_neg hn]
              exact countLt_strict hmn vs h'

theorem countLt_lt_length {m : Nat} :
    ∀ vs : List Nat, m ∈ vs → countLt m vs < vs.length
  | v :: vs, h => by
      show (if v < m then countLt m vs + 1 else countLt m vs) < vs.length + 1
      cases h with
      | head =>
          rw [if_neg (Nat.lt_irrefl m)]
          exact Nat.succ_le_succ (countLt_le_length m vs)
      | tail _ h' =>
          by_cases hv : v < m
          · rw [if_pos hv]
            exact Nat.succ_le_succ (countLt_lt_length vs h')
          · rw [if_neg hv]
            exact Nat.lt_of_lt_of_le (countLt_lt_length vs h') (Nat.le_succ _)

theorem defect_congr (r r' : H → Nat) :
    ∀ q : Quiver H, (∀ e ∈ q, (r e.1 < r e.2 ↔ r' e.1 < r' e.2)) →
      defect r q = defect r' q
  | [], _ => rfl
  | e :: es, h => by
      have hiff := h e (List.Mem.head es)
      have ih := defect_congr r r' es (fun f hf => h f (List.Mem.tail e hf))
      show (if r e.1 < r e.2 then defect r es else defect r es + 1)
        = if r' e.1 < r' e.2 then defect r' es else defect r' es + 1
      by_cases hc : r e.1 < r e.2
      · rw [if_pos hc, if_pos (hiff.mp hc), ih]
      · rw [if_neg hc, if_neg (fun hc' => hc (hiff.mpr hc')), ih]

theorem defect_congr_verts (r r' : H → Nat) (q : Quiver H)
    (h : ∀ a ∈ verts q, r a = r' a) : defect r q = defect r' q :=
  defect_congr r r' q (fun e he => by
    rw [h e.1 (verts_fst he), h e.2 (verts_snd he)])

def rankChart (r : H → Nat) (q : Quiver H) : H → Nat :=
  fun a => countLt (r a) ((verts q).map r)

theorem rankChart_defect (r : H → Nat) (q : Quiver H) :
    defect (rankChart r q) q = defect r q :=
  defect_congr (rankChart r q) r q (fun e he => by
    constructor
    · intro h
      by_cases hr : r e.1 < r e.2
      · exact hr
      · exact absurd h
          (Nat.not_lt_of_le (countLt_mono (Nat.le_of_not_lt hr) _))
    · intro h
      exact countLt_strict h _ (mem_map_of_mem r (verts_fst he)))

theorem rankChart_lt (r : H → Nat) (q : Quiver H) {a : H} (ha : a ∈ verts q) :
    rankChart r q a < (verts q).length := by
  have h := countLt_lt_length ((verts q).map r) (mem_map_of_mem r ha)
  rw [length_map] at h
  exact h

def countdown : Nat → List Nat
  | 0 => []
  | n + 1 => n :: countdown n

theorem mem_countdown : ∀ {n m : Nat}, m < n → m ∈ countdown n := by
  intro n
  induction n with
  | zero => exact fun h => absurd h (Nat.not_succ_le_zero _)
  | succ k ih =>
      intro m h
      by_cases hm : m = k
      · rw [hm]
        exact List.Mem.head _
      · exact List.Mem.tail _ (ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hm))

def consAll (vs : List Nat) (ts : List (List Nat)) : List (List Nat) :=
  match vs with
  | [] => []
  | v :: rest => ts.map (v :: ·) ++ consAll rest ts

theorem mem_consAll {v : Nat} {t : List Nat} :
    ∀ (vs : List Nat) (ts : List (List Nat)), v ∈ vs → t ∈ ts →
      (v :: t) ∈ consAll vs ts
  | w :: rest, ts, hv, ht => by
      show (v :: t) ∈ ts.map (w :: ·) ++ consAll rest ts
      cases hv with
      | head => exact mem_append_left _ (mem_map_of_mem (v :: ·) ht)
      | tail _ hv' => exact mem_append_right _ (mem_consAll rest ts hv' ht)

def tuples (N : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | len + 1 => consAll (countdown N) (tuples N len)

theorem tuples_complete (N : Nat) :
    ∀ l : List Nat, (∀ v ∈ l, v < N) → l ∈ tuples N l.length
  | [], _ => List.Mem.head _
  | v :: l, h => by
      show (v :: l) ∈ consAll (countdown N) (tuples N l.length)
      exact mem_consAll (countdown N) (tuples N l.length)
        (mem_countdown (h v (List.Mem.head l)))
        (tuples_complete N l (fun w hw => h w (List.Mem.tail v hw)))

def best (q : Quiver H) : List (H → Nat) → (H → Nat) → (H → Nat)
  | [], b => b
  | r :: rs, b => best q rs (if defect r q < defect b q then r else b)

theorem best_le_seed (q : Quiver H) :
    ∀ (rs : List (H → Nat)) (b : H → Nat), defect (best q rs b) q ≤ defect b q
  | [], _ => Nat.le_refl _
  | r :: rs, b => by
      show defect (best q rs (if defect r q < defect b q then r else b)) q
        ≤ defect b q
      by_cases hc : defect r q < defect b q
      · rw [if_pos hc]
        exact Nat.le_trans (best_le_seed q rs r) (Nat.le_of_lt hc)
      · rw [if_neg hc]
        exact best_le_seed q rs b

theorem best_le_mem (q : Quiver H) :
    ∀ (rs : List (H → Nat)) (b r : H → Nat), r ∈ rs →
      defect (best q rs b) q ≤ defect r q
  | s :: rs, b, _, List.Mem.head _ => by
      show defect (best q rs (if defect s q < defect b q then s else b)) q
        ≤ defect s q
      by_cases hc : defect s q < defect b q
      · rw [if_pos hc]
        exact best_le_seed q rs s
      · rw [if_neg hc]
        exact Nat.le_trans (best_le_seed q rs b) (Nat.le_of_not_lt hc)
  | s :: rs, b, r, List.Mem.tail _ h' => by
      show defect (best q rs (if defect s q < defect b q then s else b)) q
        ≤ defect r q
      exact best_le_mem q rs _ r h'

section Tight

variable [DecidableEq H]

def chartOf : List H → List Nat → H → Nat
  | [], _, _ => 0
  | _ :: _, [], _ => 0
  | v :: vs, n :: ns, a => if a = v then n else chartOf vs ns a

theorem chartOf_map (s : H → Nat) :
    ∀ (vs : List H) (a : H), a ∈ vs → chartOf vs (vs.map s) a = s a
  | v :: vs, a, h => by
      show (if a = v then s v else chartOf vs (vs.map s) a) = s a
      by_cases hv : a = v
      · rw [if_pos hv, hv]
      · rw [if_neg hv]
        have h' : a ∈ vs := by
          cases h with
          | head => exact absurd rfl hv
          | tail _ h'' => exact h''
        exact chartOf_map s vs a h'

def candidates (q : Quiver H) : List (H → Nat) :=
  (tuples (verts q).length (verts q).length).map (chartOf (verts q))

def tightChart (q : Quiver H) : H → Nat :=
  best q (candidates q) (fun _ => 0)

theorem tightChart_tight (q : Quiver H) : TightInterface (tightChart q) q := by
  intro r
  have ht := tuples_complete (verts q).length ((verts q).map (rankChart r q))
    (fun v hv => by
      obtain ⟨a, ha, hva⟩ := exists_of_mem_map hv
      rw [← hva]
      exact rankChart_lt r q ha)
  rw [length_map] at ht
  have h1 : defect (tightChart q) q
      ≤ defect (chartOf (verts q) ((verts q).map (rankChart r q))) q :=
    best_le_mem q (candidates q) (fun _ => 0) _
      (mem_map_of_mem (chartOf (verts q)) ht)
  have h2 : defect (chartOf (verts q) ((verts q).map (rankChart r q))) q
      = defect (rankChart r q) q :=
    defect_congr_verts _ _ q (fun a ha => chartOf_map (rankChart r q) (verts q) a ha)
  rw [h2, rankChart_defect] at h1
  exact h1

theorem tight_interface_exists (q : Quiver H) :
    ∃ r : H → Nat, TightInterface r q :=
  ⟨tightChart q, tightChart_tight q⟩

def feedback (q : Quiver H) : Nat := defect (tightChart q) q

theorem feedback_le (q : Quiver H) (r : H → Nat) : feedback q ≤ defect r q :=
  tightChart_tight q r

theorem feedback_attained (q : Quiver H) : ∃ r : H → Nat, defect r q = feedback q :=
  ⟨tightChart q, rfl⟩

theorem feedback_zero_iff_acyclic (q : Quiver H) : feedback q = 0 ↔ Acyclic q := by
  constructor
  · intro h0
    exact tsortable_acyclic ⟨tightChart q, (defect_zero_iff _ q).mp h0⟩
  · intro hac
    obtain ⟨r, h0⟩ := (acyclic_iff_some_chart_clears q).mp hac
    exact Nat.le_antisymm (h0 ▸ feedback_le q r) (Nat.zero_le _)

end Tight

theorem tight_defect_unique {q : Quiver H} {r r' : H → Nat}
    (h : TightInterface r q) (h' : TightInterface r' q) :
    defect r q = defect r' q :=
  Nat.le_antisymm (h r') (h' r)

theorem tight_defect_eq_feedback [DecidableEq H] {q : Quiver H} {r : H → Nat}
    (h : TightInterface r q) : defect r q = feedback q :=
  tight_defect_unique h (tightChart_tight q)

/-- info: 'Foam.verts_fst' does not depend on any axioms -/
#guard_msgs in #print axioms verts_fst

/-- info: 'Foam.verts_snd' does not depend on any axioms -/
#guard_msgs in #print axioms verts_snd

/-- info: 'Foam.mem_map_of_mem' does not depend on any axioms -/
#guard_msgs in #print axioms mem_map_of_mem

/-- info: 'Foam.exists_of_mem_map' does not depend on any axioms -/
#guard_msgs in #print axioms exists_of_mem_map

/-- info: 'Foam.length_map' does not depend on any axioms -/
#guard_msgs in #print axioms length_map

/-- info: 'Foam.mem_append_left' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_left

/-- info: 'Foam.mem_append_right' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_right

/-- info: 'Foam.countLt_le_length' does not depend on any axioms -/
#guard_msgs in #print axioms countLt_le_length

/-- info: 'Foam.countLt_mono' does not depend on any axioms -/
#guard_msgs in #print axioms countLt_mono

/-- info: 'Foam.countLt_strict' does not depend on any axioms -/
#guard_msgs in #print axioms countLt_strict

/-- info: 'Foam.countLt_lt_length' does not depend on any axioms -/
#guard_msgs in #print axioms countLt_lt_length

/-- info: 'Foam.defect_congr' does not depend on any axioms -/
#guard_msgs in #print axioms defect_congr

/-- info: 'Foam.defect_congr_verts' does not depend on any axioms -/
#guard_msgs in #print axioms defect_congr_verts

/-- info: 'Foam.rankChart_defect' does not depend on any axioms -/
#guard_msgs in #print axioms rankChart_defect

/-- info: 'Foam.rankChart_lt' does not depend on any axioms -/
#guard_msgs in #print axioms rankChart_lt

/-- info: 'Foam.mem_countdown' does not depend on any axioms -/
#guard_msgs in #print axioms mem_countdown

/-- info: 'Foam.mem_consAll' does not depend on any axioms -/
#guard_msgs in #print axioms mem_consAll

/-- info: 'Foam.tuples_complete' does not depend on any axioms -/
#guard_msgs in #print axioms tuples_complete

/-- info: 'Foam.chartOf_map' does not depend on any axioms -/
#guard_msgs in #print axioms chartOf_map

/-- info: 'Foam.best_le_seed' does not depend on any axioms -/
#guard_msgs in #print axioms best_le_seed

/-- info: 'Foam.best_le_mem' does not depend on any axioms -/
#guard_msgs in #print axioms best_le_mem

/-- info: 'Foam.tightChart_tight' does not depend on any axioms -/
#guard_msgs in #print axioms tightChart_tight

/-- info: 'Foam.tight_interface_exists' does not depend on any axioms -/
#guard_msgs in #print axioms tight_interface_exists

/-- info: 'Foam.feedback_le' does not depend on any axioms -/
#guard_msgs in #print axioms feedback_le

/-- info: 'Foam.feedback_attained' does not depend on any axioms -/
#guard_msgs in #print axioms feedback_attained

/-- info: 'Foam.feedback_zero_iff_acyclic' does not depend on any axioms -/
#guard_msgs in #print axioms feedback_zero_iff_acyclic

/-- info: 'Foam.tight_defect_unique' does not depend on any axioms -/
#guard_msgs in #print axioms tight_defect_unique

/-- info: 'Foam.tight_defect_eq_feedback' does not depend on any axioms -/
#guard_msgs in #print axioms tight_defect_eq_feedback

end Foam
