import Foam.Seat.Descend

namespace Foam

variable {H : Type}

def sortedBy (r : H → Nat) (q : Quiver H) : Prop :=
  ∀ e ∈ q, r e.1 < r e.2

def Tsortable (q : Quiver H) : Prop :=
  ∃ r : H → Nat, sortedBy r q

def Acyclic (q : Quiver H) : Prop :=
  ∀ (a : H) (p : Path q a a), p.edges = []

def defect (r : H → Nat) : Quiver H → Nat
  | [] => 0
  | e :: es => if r e.1 < r e.2 then defect r es else defect r es + 1

theorem path_climbs {q : Quiver H} {r : H → Nat} (hs : sortedBy r q) :
    {x y : H} → (p : Path q x y) → p.edges ≠ [] → r x < r y
  | _, _, Path.nil, h => absurd rfl h
  | _, _, Path.cons e Path.nil, _ => hs _ e
  | _, _, Path.cons e (Path.cons e' rest), _ =>
      Nat.lt_trans (hs _ e)
        (path_climbs hs (Path.cons e' rest) (fun h => nomatch h))

theorem tsortable_acyclic {q : Quiver H} : Tsortable q → Acyclic q := by
  rintro ⟨r, hs⟩ a p
  cases hp : p.edges with
  | nil => rfl
  | cons e l =>
      have hlt : r a < r a :=
        path_climbs hs p (fun h => nomatch hp ▸ h)
      exact absurd hlt (Nat.lt_irrefl _)

theorem defect_zero_iff (r : H → Nat) :
    ∀ q : Quiver H, defect r q = 0 ↔ sortedBy r q
  | [] => ⟨(fun _ e he => nomatch he), (fun _ => rfl)⟩
  | e :: es => by
      constructor
      · intro h0 f hf
        by_cases he : r e.1 < r e.2
        · have hshow : defect r (e :: es) = defect r es := by
            show (if r e.1 < r e.2 then defect r es else defect r es + 1) = defect r es
            rw [if_pos he]
          rw [hshow] at h0
          cases hf with
          | head => exact he
          | tail _ hmem => exact ((defect_zero_iff r es).mp h0) f hmem
        · have hshow : defect r (e :: es) = defect r es + 1 := by
            show (if r e.1 < r e.2 then defect r es else defect r es + 1)
              = defect r es + 1
            rw [if_neg he]
          rw [hshow] at h0
          exact Nat.noConfusion h0
      · intro hs
        have he : r e.1 < r e.2 := hs e (List.Mem.head es)
        show (if r e.1 < r e.2 then defect r es else defect r es + 1) = 0
        rw [if_pos he]
        exact (defect_zero_iff r es).mpr (fun f hf => hs f (List.Mem.tail e hf))

theorem defect_deposit_forward (r : H → Nat) (q : Quiver H) (e : H × H)
    (h : r e.1 < r e.2) : defect r (q.deposit e) = defect r q := by
  show (if r e.1 < r e.2 then defect r q else defect r q + 1) = defect r q
  rw [if_pos h]

theorem defect_deposit_backward (r : H → Nat) (q : Quiver H) (e : H × H)
    (h : ¬ r e.1 < r e.2) : defect r (q.deposit e) = defect r q + 1 := by
  show (if r e.1 < r e.2 then defect r q else defect r q + 1) = defect r q + 1
  rw [if_neg h]

theorem defect_deposit_le (r : H → Nat) (q : Quiver H) (e : H × H) :
    defect r q ≤ defect r (q.deposit e) := by
  show defect r q ≤ if r e.1 < r e.2 then defect r q else defect r q + 1
  by_cases h : r e.1 < r e.2
  · rw [if_pos h]
    exact Nat.le_refl _
  · rw [if_neg h]
    exact Nat.le_succ _

def TightInterface (r : H → Nat) (q : Quiver H) : Prop :=
  ∀ r' : H → Nat, defect r q ≤ defect r' q

theorem tight_maintained {q : Quiver H} {r : H → Nat} (ht : TightInterface r q)
    (e : H × H) (h : r e.1 < r e.2) : TightInterface r (q.deposit e) := by
  intro r'
  rw [defect_deposit_forward r q e h]
  exact Nat.le_trans (ht r') (defect_deposit_le r' q e)

theorem cycle_defeats_every_chart {q : Quiver H} {a : H} (p : Path q a a)
    (hp : p.edges ≠ []) (r : H → Nat) : defect r q ≠ 0 :=
  fun h0 =>
    absurd (path_climbs ((defect_zero_iff r q).mp h0) p hp) (Nat.lt_irrefl (r a))

theorem descent_bounded (f : Nat → Nat) (hdec : ∀ n, f (n + 1) < f n) :
    ∀ n, f n + n ≤ f 0
  | 0 => Nat.le_refl _
  | n + 1 => by
      have h1 : f (n + 1) + 1 + n ≤ f n + n :=
        Nat.add_le_add_right (hdec n) n
      have h2 : f (n + 1) + (n + 1) = f (n + 1) + 1 + n := by
        rw [Nat.succ_add, Nat.add_succ]
      rw [h2]
      exact Nat.le_trans h1 (descent_bounded f hdec n)

theorem no_infinite_descent (f : Nat → Nat) (hdec : ∀ n, f (n + 1) < f n) : False :=
  absurd
    (Nat.le_trans (Nat.le_add_left (f 0 + 1) (f (f 0 + 1))) (descent_bounded f hdec (f 0 + 1)))
    (Nat.not_succ_le_self (f 0))

def nmax (m n : Nat) : Nat := if m ≤ n then n else m

theorem le_nmax_left (m n : Nat) : m ≤ nmax m n := by
  show m ≤ if m ≤ n then n else m
  by_cases h : m ≤ n
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    exact Nat.le_refl m

theorem le_nmax_right (m n : Nat) : n ≤ nmax m n := by
  show n ≤ if m ≤ n then n else m
  by_cases h : m ≤ n
  · rw [if_pos h]
    exact Nat.le_refl n
  · rw [if_neg h]
    exact Nat.le_of_lt (Nat.lt_of_not_le h)

theorem nmax_cases (m n : Nat) : nmax m n = m ∨ nmax m n = n := by
  show (if m ≤ n then n else m) = m ∨ (if m ≤ n then n else m) = n
  by_cases h : m ≤ n
  · rw [if_pos h]
    exact Or.inr rfl
  · rw [if_neg h]
    exact Or.inl rfl

def distinct {A : Type} : List A → Prop
  | [] => True
  | x :: xs => ¬ x ∈ xs ∧ distinct xs

def removeOne {A : Type} [DecidableEq A] : List A → A → List A
  | [], _ => []
  | x :: xs, a => if x = a then xs else x :: removeOne xs a

theorem removeOne_length {A : Type} [DecidableEq A] :
    ∀ (l : List A) (a : A), a ∈ l → (removeOne l a).length + 1 = l.length
  | [], _, h => nomatch h
  | x :: xs, a, h => by
      show (if x = a then xs else x :: removeOne xs a).length + 1 = xs.length + 1
      by_cases hx : x = a
      · rw [if_pos hx]
      · rw [if_neg hx]
        have ha : a ∈ xs := by
          cases h with
          | head => exact absurd rfl hx
          | tail _ h' => exact h'
        show (removeOne xs a).length + 1 + 1 = xs.length + 1
        rw [removeOne_length xs a ha]

theorem mem_removeOne {A : Type} [DecidableEq A] :
    ∀ (l : List A) (a x : A), x ∈ l → x ≠ a → x ∈ removeOne l a
  | [], _, _, h, _ => nomatch h
  | y :: ys, a, x, h, hne => by
      show x ∈ if y = a then ys else y :: removeOne ys a
      by_cases hy : y = a
      · rw [if_pos hy]
        cases h with
        | head => exact absurd hy hne
        | tail _ h' => exact h'
      · rw [if_neg hy]
        cases h with
        | head => exact List.Mem.head _
        | tail _ h' => exact List.Mem.tail _ (mem_removeOne ys a x h' hne)

theorem distinct_length_le {A : Type} [DecidableEq A] :
    ∀ (l q : List A), distinct l → (∀ x ∈ l, x ∈ q) → l.length ≤ q.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, q, hd, hsub => by
      have hxq : x ∈ q := hsub x (List.Mem.head xs)
      have hsub' : ∀ y ∈ xs, y ∈ removeOne q x := fun y hy =>
        mem_removeOne q x y (hsub y (List.Mem.tail x hy)) (fun he => hd.1 (he ▸ hy))
      have ih := distinct_length_le xs (removeOne q x) hd.2 hsub'
      show xs.length + 1 ≤ q.length
      rw [← removeOne_length q x hxq]
      exact Nat.succ_le_succ ih

theorem path_to_edge {q : Quiver H} :
    {x y : H} → (p : Path q x y) → {u v : H} → (u, v) ∈ p.edges →
      Nonempty (Path q x u)
  | _, _, Path.nil, _, _, h => nomatch h
  | _, _, Path.cons e rest, u, v, h => by
      cases h with
      | head => exact ⟨Path.nil⟩
      | tail _ h' =>
          obtain ⟨p'⟩ := path_to_edge rest h'
          exact ⟨Path.cons e p'⟩

theorem acyclic_path_distinct {q : Quiver H} (hac : Acyclic q) :
    {x y : H} → (p : Path q x y) → distinct p.edges
  | _, _, Path.nil => trivial
  | _, _, Path.cons e rest => by
      refine ⟨fun hmem => ?_, acyclic_path_distinct hac rest⟩
      obtain ⟨p'⟩ := path_to_edge rest hmem
      exact nomatch hac _ (Path.cons e p')

section Depth

variable [DecidableEq H]

def depthAux (df : H → Nat) : List (H × H) → H → Nat
  | [], _ => 0
  | e :: es, a =>
      if e.1 = a then nmax (df e.2 + 1) (depthAux df es a) else depthAux df es a

def depthFuel (q : Quiver H) : Nat → H → Nat
  | 0, _ => 0
  | f + 1, a => depthAux (depthFuel q f) q a

theorem depthAux_climb (df : H → Nat) :
    ∀ (l : List (H × H)) (a b : H), (a, b) ∈ l → df b + 1 ≤ depthAux df l a
  | [], _, _, h => nomatch h
  | e :: es, a, b, h => by
      show df b + 1 ≤
        if e.1 = a then nmax (df e.2 + 1) (depthAux df es a) else depthAux df es a
      cases h with
      | head =>
          rw [if_pos rfl]
          exact le_nmax_left _ _
      | tail _ h' =>
          by_cases he : e.1 = a
          · rw [if_pos he]
            exact Nat.le_trans (depthAux_climb df es a b h') (le_nmax_right _ _)
          · rw [if_neg he]
            exact depthAux_climb df es a b h'

theorem depthAux_attained (df : H → Nat) :
    ∀ (l : List (H × H)) (a : H),
      depthAux df l a = 0 ∨ ∃ b, (a, b) ∈ l ∧ depthAux df l a = df b + 1
  | [], _ => Or.inl rfl
  | e :: es, a => by
      obtain ⟨x, y⟩ := e
      show (if x = a then nmax (df y + 1) (depthAux df es a) else depthAux df es a) = 0
        ∨ ∃ b, (a, b) ∈ (x, y) :: es
            ∧ (if x = a then nmax (df y + 1) (depthAux df es a) else depthAux df es a)
              = df b + 1
      by_cases hx : x = a
      · subst hx
        rw [if_pos rfl]
        cases nmax_cases (df y + 1) (depthAux df es x) with
        | inl hm =>
            rw [hm]
            exact Or.inr ⟨y, List.Mem.head es, rfl⟩
        | inr hm =>
            rw [hm]
            cases depthAux_attained df es x with
            | inl h0 => exact Or.inl h0
            | inr hex =>
                obtain ⟨b, hb, hval⟩ := hex
                exact Or.inr ⟨b, List.Mem.tail (x, y) hb, hval⟩
      · rw [if_neg hx]
        cases depthAux_attained df es a with
        | inl h0 => exact Or.inl h0
        | inr hex =>
            obtain ⟨b, hb, hval⟩ := hex
            exact Or.inr ⟨b, List.Mem.tail (x, y) hb, hval⟩

theorem depth_realized (q : Quiver H) :
    ∀ (f : Nat) (a : H),
      depthFuel q f a = 0
        ∨ ∃ (z : H) (p : Path q a z), p.edges.length = depthFuel q f a
  | 0, _ => Or.inl rfl
  | f + 1, a => by
      cases depthAux_attained (depthFuel q f) q a with
      | inl h0 => exact Or.inl h0
      | inr hex =>
          obtain ⟨b, hb, hval⟩ := hex
          right
          cases depth_realized q f b with
          | inl h0 =>
              refine ⟨b, Path.cons hb Path.nil, ?_⟩
              show 0 + 1 = depthAux (depthFuel q f) q a
              rw [hval, h0]
          | inr hex' =>
              obtain ⟨z, p, hlen⟩ := hex'
              refine ⟨z, Path.cons hb p, ?_⟩
              show p.edges.length + 1 = depthAux (depthFuel q f) q a
              rw [hval, hlen]

theorem depth_bounded {q : Quiver H} (hac : Acyclic q) (f : Nat) (a : H) :
    depthFuel q f a ≤ q.length := by
  cases depth_realized q f a with
  | inl h0 =>
      rw [h0]
      exact Nat.zero_le _
  | inr hex =>
      obtain ⟨z, p, hlen⟩ := hex
      rw [← hlen]
      exact distinct_length_le p.edges q (acyclic_path_distinct hac p)
        (fun e he => reach_within_quiver p e he)

theorem depth_lower {q : Quiver H} :
    {a z : H} → (p : Path q a z) → (f : Nat) → p.edges.length ≤ f →
      p.edges.length ≤ depthFuel q f a
  | _, _, Path.nil, _, _ => Nat.zero_le _
  | _, _, Path.cons e rest, 0, hle => absurd hle (Nat.not_succ_le_zero _)
  | _, _, Path.cons e rest, f + 1, hle => by
      have ih := depth_lower rest f (Nat.le_of_succ_le_succ hle)
      show rest.edges.length + 1 ≤ depthAux (depthFuel q f) q _
      exact Nat.le_trans (Nat.succ_le_succ ih) (depthAux_climb (depthFuel q f) q _ _ e)

theorem depth_stable {q : Quiver H} (hac : Acyclic q) (a : H) :
    depthFuel q (q.length + 1) a ≤ depthFuel q q.length a := by
  cases depth_realized q (q.length + 1) a with
  | inl h0 =>
      rw [h0]
      exact Nat.zero_le _
  | inr hex =>
      obtain ⟨z, p, hlen⟩ := hex
      rw [← hlen]
      exact depth_lower p q.length
        (distinct_length_le p.edges q (acyclic_path_distinct hac p)
          (fun e he => reach_within_quiver p e he))

theorem depth_antisorts {q : Quiver H} (hac : Acyclic q) :
    ∀ e ∈ q, depthFuel q (q.length + 1) e.2 < depthFuel q (q.length + 1) e.1 := by
  intro e he
  exact Nat.le_trans (Nat.succ_le_succ (depth_stable hac e.2))
    (depthAux_climb (depthFuel q q.length) q e.1 e.2 he)

end Depth

def Path.relabel {q1 q2 : Quiver H} (h : ∀ e, e ∈ q1 → e ∈ q2) :
    {x y : H} → Path q1 x y → Path q2 x y
  | _, _, Path.nil => Path.nil
  | _, _, Path.cons e rest => Path.cons (h _ e) (Path.relabel h rest)

theorem Path.relabel_edges {q1 q2 : Quiver H} (h : ∀ e, e ∈ q1 → e ∈ q2) :
    {x y : H} → (p : Path q1 x y) → (p.relabel h).edges = p.edges
  | _, _, Path.nil => rfl
  | _, _, Path.cons _ rest =>
      congrArg (_ :: ·) (Path.relabel_edges h rest)

theorem length_append {A : Type} :
    ∀ (xs ys : List A), (xs ++ ys).length = xs.length + ys.length
  | [], ys => (Nat.zero_add ys.length).symm
  | x :: xs, ys => by
      show (xs ++ ys).length + 1 = xs.length + 1 + ys.length
      rw [length_append xs ys, Nat.succ_add]

theorem reverse_edges_length {q : Quiver H} :
    {x y : H} → (p : Path q x y) → p.reverse.edges.length = p.edges.length
  | _, _, Path.nil => rfl
  | _, _, Path.cons e rest => by
      show (rest.reverse.comp (Path.cons (mem_reverse e) Path.nil)).edges.length
        = rest.edges.length + 1
      rw [Path.edges_comp, length_append, reverse_edges_length rest]
      rfl

theorem acyclic_reverse {q : Quiver H} (hac : Acyclic q) : Acyclic q.reverse := by
  intro a p
  have hmem : ∀ e, e ∈ q.reverse.reverse → e ∈ q :=
    fun e he => Quiver.reverse_reverse q ▸ he
  have hnil : (p.reverse.relabel hmem).edges = [] := hac a (p.reverse.relabel hmem)
  rw [Path.relabel_edges] at hnil
  have hlen : p.edges.length = 0 := by
    rw [← reverse_edges_length p, hnil]
    rfl
  cases hp : p.edges with
  | nil => rfl
  | cons e l =>
      rw [hp] at hlen
      exact Nat.noConfusion hlen

theorem acyclic_tsortable [DecidableEq H] {q : Quiver H} (hac : Acyclic q) :
    Tsortable q := by
  refine ⟨depthFuel q.reverse (q.reverse.length + 1), ?_⟩
  intro e he
  exact depth_antisorts (acyclic_reverse hac) (e.2, e.1) (mem_reverse he)

theorem tsortable_iff_acyclic [DecidableEq H] (q : Quiver H) :
    Tsortable q ↔ Acyclic q :=
  ⟨tsortable_acyclic, acyclic_tsortable⟩

theorem acyclic_iff_some_chart_clears [DecidableEq H] (q : Quiver H) :
    Acyclic q ↔ ∃ r : H → Nat, defect r q = 0 := by
  constructor
  · intro hac
    obtain ⟨r, hs⟩ := acyclic_tsortable hac
    exact ⟨r, (defect_zero_iff r q).mpr hs⟩
  · rintro ⟨r, h0⟩
    exact tsortable_acyclic ⟨r, (defect_zero_iff r q).mp h0⟩

/-- info: 'Foam.path_climbs' does not depend on any axioms -/
#guard_msgs in #print axioms path_climbs

/-- info: 'Foam.tsortable_acyclic' does not depend on any axioms -/
#guard_msgs in #print axioms tsortable_acyclic

/-- info: 'Foam.defect_zero_iff' does not depend on any axioms -/
#guard_msgs in #print axioms defect_zero_iff

/-- info: 'Foam.defect_deposit_forward' does not depend on any axioms -/
#guard_msgs in #print axioms defect_deposit_forward

/-- info: 'Foam.defect_deposit_backward' does not depend on any axioms -/
#guard_msgs in #print axioms defect_deposit_backward

/-- info: 'Foam.defect_deposit_le' does not depend on any axioms -/
#guard_msgs in #print axioms defect_deposit_le

/-- info: 'Foam.tight_maintained' does not depend on any axioms -/
#guard_msgs in #print axioms tight_maintained

/-- info: 'Foam.cycle_defeats_every_chart' does not depend on any axioms -/
#guard_msgs in #print axioms cycle_defeats_every_chart

/-- info: 'Foam.descent_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms descent_bounded

/-- info: 'Foam.no_infinite_descent' does not depend on any axioms -/
#guard_msgs in #print axioms no_infinite_descent

/-- info: 'Foam.distinct_length_le' does not depend on any axioms -/
#guard_msgs in #print axioms distinct_length_le

/-- info: 'Foam.path_to_edge' does not depend on any axioms -/
#guard_msgs in #print axioms path_to_edge

/-- info: 'Foam.acyclic_path_distinct' does not depend on any axioms -/
#guard_msgs in #print axioms acyclic_path_distinct

/-- info: 'Foam.depthAux_climb' does not depend on any axioms -/
#guard_msgs in #print axioms depthAux_climb

/-- info: 'Foam.depthAux_attained' does not depend on any axioms -/
#guard_msgs in #print axioms depthAux_attained

/-- info: 'Foam.depth_realized' does not depend on any axioms -/
#guard_msgs in #print axioms depth_realized

/-- info: 'Foam.depth_bounded' does not depend on any axioms -/
#guard_msgs in #print axioms depth_bounded

/-- info: 'Foam.depth_lower' does not depend on any axioms -/
#guard_msgs in #print axioms depth_lower

/-- info: 'Foam.depth_stable' does not depend on any axioms -/
#guard_msgs in #print axioms depth_stable

/-- info: 'Foam.depth_antisorts' does not depend on any axioms -/
#guard_msgs in #print axioms depth_antisorts

/-- info: 'Foam.acyclic_reverse' does not depend on any axioms -/
#guard_msgs in #print axioms acyclic_reverse

/-- info: 'Foam.acyclic_tsortable' does not depend on any axioms -/
#guard_msgs in #print axioms acyclic_tsortable

/-- info: 'Foam.tsortable_iff_acyclic' does not depend on any axioms -/
#guard_msgs in #print axioms tsortable_iff_acyclic

/-- info: 'Foam.acyclic_iff_some_chart_clears' does not depend on any axioms -/
#guard_msgs in #print axioms acyclic_iff_some_chart_clears

end Foam
