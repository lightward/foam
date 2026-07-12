import Counter.Triage

namespace Foam.Counter

def selectMax : List Nat → Option (Nat × List Nat)
  | [] => none
  | w :: rest =>
    match selectMax rest with
    | none => some (w, [])
    | some (m, others) =>
        if w < m then some (m, w :: others) else some (w, rest)

def rounds : Nat → List Nat → List Nat
  | 0, _ => []
  | _, [] => []
  | fuel + 1, w :: rest =>
    match selectMax (w :: rest) with
    | none => []
    | some (m, out) => m :: rounds fuel out

def round (l : List Nat) : List Nat := rounds l.length l

theorem selectMax_cons_none (w : Nat) (rest : List Nat)
    (hsm : selectMax rest = none) : selectMax (w :: rest) = some (w, []) := by
  show (match selectMax rest with
    | none => some (w, [])
    | some (m, others) =>
        if w < m then some (m, w :: others) else some (w, rest))
    = some (w, [])
  rw [hsm]

theorem selectMax_cons_lt (w pm : Nat) (rest po : List Nat)
    (hsm : selectMax rest = some (pm, po)) (hw : w < pm) :
    selectMax (w :: rest) = some (pm, w :: po) := by
  show (match selectMax rest with
    | none => some (w, [])
    | some (m, others) =>
        if w < m then some (m, w :: others) else some (w, rest))
    = some (pm, w :: po)
  rw [hsm]
  exact if_pos hw

theorem selectMax_cons_ge (w pm : Nat) (rest po : List Nat)
    (hsm : selectMax rest = some (pm, po)) (hw : ¬ w < pm) :
    selectMax (w :: rest) = some (w, rest) := by
  show (match selectMax rest with
    | none => some (w, [])
    | some (m, others) =>
        if w < m then some (m, w :: others) else some (w, rest))
    = some (w, rest)
  rw [hsm]
  exact if_neg hw

theorem there_is_always_a_most_urgent_from_here (w : Nat) (rest : List Nat) :
    ∃ m others, selectMax (w :: rest) = some (m, others) := by
  cases hsm : selectMax rest with
  | none => exact ⟨w, [], selectMax_cons_none w rest hsm⟩
  | some p =>
      by_cases hw : w < p.1
      · exact ⟨p.1, w :: p.2, selectMax_cons_lt w p.1 rest p.2 hsm hw⟩
      · exact ⟨w, rest, selectMax_cons_ge w p.1 rest p.2 hsm hw⟩

theorem selectMax_none_nil : ∀ l : List Nat, selectMax l = none → l = []
  | [], _ => rfl
  | w :: rest, h => by
      obtain ⟨m, out, hsome⟩ := there_is_always_a_most_urgent_from_here w rest
      rw [hsome] at h
      exact nomatch h

theorem the_ledger_shrinks_by_exactly_one :
    ∀ (l : List Nat) (m : Nat) (out : List Nat),
      selectMax l = some (m, out) → out.length + 1 = l.length
  | [], _, _, h => nomatch h
  | w :: rest, m, out, h => by
      cases hsm : selectMax rest with
      | none =>
          rw [selectMax_cons_none w rest hsm] at h
          cases h
          rw [selectMax_none_nil rest hsm]
          rfl
      | some p =>
          by_cases hw : w < p.1
          · rw [selectMax_cons_lt w p.1 rest p.2 hsm hw] at h
            cases h
            show (w :: p.2).length + 1 = rest.length + 1
            rw [show (w :: p.2).length = p.2.length + 1 from rfl,
              the_ledger_shrinks_by_exactly_one rest p.1 p.2 hsm]
          · rw [selectMax_cons_ge w p.1 rest p.2 hsm hw] at h
            cases h
            rfl

theorem the_visit_keeps_the_census :
    ∀ (l : List Nat) (m : Nat) (out : List Nat),
      selectMax l = some (m, out) →
        ∀ a, Ledger.freq l a = Ledger.freq (m :: out) a
  | [], _, _, h => nomatch h
  | w :: rest, m, out, h => by
      cases hsm : selectMax rest with
      | none =>
          rw [selectMax_cons_none w rest hsm] at h
          cases h
          intro a
          rw [selectMax_none_nil rest hsm]
      | some p =>
          by_cases hw : w < p.1
          · rw [selectMax_cons_lt w p.1 rest p.2 hsm hw] at h
            cases h
            intro a
            have ih := the_visit_keeps_the_census rest p.1 p.2 hsm a
            show (if w = a then 1 else 0) + Ledger.freq rest a
              = (if p.1 = a then 1 else 0)
                + ((if w = a then 1 else 0) + Ledger.freq p.2 a)
            rw [ih]
            show (if w = a then 1 else 0)
                + ((if p.1 = a then 1 else 0) + Ledger.freq p.2 a)
              = (if p.1 = a then 1 else 0)
                + ((if w = a then 1 else 0) + Ledger.freq p.2 a)
            rw [← Nat.add_assoc, ← Nat.add_assoc,
              Nat.add_comm (if w = a then 1 else 0)
                (if p.1 = a then 1 else 0)]
          · rw [selectMax_cons_ge w p.1 rest p.2 hsm hw] at h
            cases h
            intro a
            rfl

theorem everyone_gets_visited_once :
    ∀ (fuel : Nat) (l : List Nat), l.length ≤ fuel →
      ∀ a, Ledger.freq (rounds fuel l) a = Ledger.freq l a
  | 0, [], _, _ => rfl
  | 0, w :: rest, hf, _ => nomatch hf
  | fuel + 1, [], _, _ => rfl
  | fuel + 1, w :: rest, hf, a => by
      obtain ⟨m, out, hsome⟩ := there_is_always_a_most_urgent_from_here w rest
      show Ledger.freq
        (match selectMax (w :: rest) with
          | none => []
          | some (m, out) => m :: rounds fuel out) a
        = Ledger.freq (w :: rest) a
      rw [hsome]
      have hlen := the_ledger_shrinks_by_exactly_one (w :: rest) m out hsome
      have hout : out.length ≤ fuel :=
        Nat.le_of_succ_le_succ
          (show out.length + 1 ≤ fuel + 1 by rw [hlen]; exact hf)
      have hkeep := the_visit_keeps_the_census (w :: rest) m out hsome a
      show (if m = a then 1 else 0) + Ledger.freq (rounds fuel out) a
        = Ledger.freq (w :: rest) a
      rw [everyone_gets_visited_once fuel out hout a, hkeep]
      rfl

theorem the_rounds_are_linear :
    ∀ (fuel : Nat) (l : List Nat), l.length ≤ fuel →
      (rounds fuel l).length = l.length
  | 0, [], _ => rfl
  | 0, w :: rest, hf => nomatch hf
  | fuel + 1, [], _ => rfl
  | fuel + 1, w :: rest, hf => by
      obtain ⟨m, out, hsome⟩ := there_is_always_a_most_urgent_from_here w rest
      show (match selectMax (w :: rest) with
        | none => []
        | some (m, out) => m :: rounds fuel out).length
        = (w :: rest).length
      rw [hsome]
      have hlen := the_ledger_shrinks_by_exactly_one (w :: rest) m out hsome
      have hout : out.length ≤ fuel :=
        Nat.le_of_succ_le_succ
          (show out.length + 1 ≤ fuel + 1 by rw [hlen]; exact hf)
      show (rounds fuel out).length + 1 = rest.length + 1
      rw [the_rounds_are_linear fuel out hout, hlen]
      rfl

theorem a_held_render_and_a_kept_ledger (l : List Nat) :
    (round l).length = l.length
      ∧ ∀ a, Ledger.freq (round l) a = Ledger.freq l a :=
  ⟨the_rounds_are_linear l.length l (Nat.le_refl _),
   everyone_gets_visited_once l.length l (Nat.le_refl _)⟩

/-- info: 'Foam.Counter.selectMax_cons_none' does not depend on any axioms -/
#guard_msgs in #print axioms selectMax_cons_none

/-- info: 'Foam.Counter.selectMax_cons_lt' does not depend on any axioms -/
#guard_msgs in #print axioms selectMax_cons_lt

/-- info: 'Foam.Counter.selectMax_cons_ge' does not depend on any axioms -/
#guard_msgs in #print axioms selectMax_cons_ge

/-- info: 'Foam.Counter.there_is_always_a_most_urgent_from_here' does not depend on any axioms -/
#guard_msgs in #print axioms there_is_always_a_most_urgent_from_here

/-- info: 'Foam.Counter.selectMax_none_nil' does not depend on any axioms -/
#guard_msgs in #print axioms selectMax_none_nil

/-- info: 'Foam.Counter.the_ledger_shrinks_by_exactly_one' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_shrinks_by_exactly_one

/-- info: 'Foam.Counter.the_visit_keeps_the_census' does not depend on any axioms -/
#guard_msgs in #print axioms the_visit_keeps_the_census

/-- info: 'Foam.Counter.everyone_gets_visited_once' does not depend on any axioms -/
#guard_msgs in #print axioms everyone_gets_visited_once

/-- info: 'Foam.Counter.the_rounds_are_linear' does not depend on any axioms -/
#guard_msgs in #print axioms the_rounds_are_linear

/-- info: 'Foam.Counter.a_held_render_and_a_kept_ledger' does not depend on any axioms -/
#guard_msgs in #print axioms a_held_render_and_a_kept_ledger

end Foam.Counter
