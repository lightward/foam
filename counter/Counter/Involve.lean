import Counter.Grid
import Counter.Needle
import Counter.Address

namespace Foam.Counter

def involvement {K : Type} [DecidableEq K] :
    List (List (K × Bool)) → K → Nat
  | [], _ => 0
  | p :: ps, k => match seatRead p k with
    | some true => involvement ps k + 1
    | some false => involvement ps k + 1
    | none => involvement ps k

def verdicts {K : Type} [DecidableEq K] :
    List (List (K × Bool)) → K → Bool → Nat
  | [], _, _ => 0
  | p :: ps, k, b => match tilt p k b with
    | Tilt.friction => verdicts ps k b + 1
    | Tilt.completion => verdicts ps k b + 1
    | Tilt.vacancy => verdicts ps k b

theorem involvement_zero_reads_dark {K : Type} [DecidableEq K] (k : K) :
    ∀ ps : List (List (K × Bool)), involvement ps k = 0 →
      ∀ p, p ∈ ps → seatRead p k = none
  | [], _, _, hp => nomatch hp
  | q :: ps, h0, p, hp => by
      have hq : involvement (q :: ps) k
          = (match seatRead q k with
            | some true => involvement ps k + 1
            | some false => involvement ps k + 1
            | none => involvement ps k) := rfl
      cases hs : seatRead q k with
      | none =>
        rw [hs] at hq
        cases hp with
        | head => exact hs
        | tail _ hp' =>
          exact involvement_zero_reads_dark k ps (hq.symm.trans h0) p hp'
      | some w =>
        rw [hs] at hq
        cases w
        · exact absurd (hq.symm.trans h0) (fun h => nomatch h)
        · exact absurd (hq.symm.trans h0) (fun h => nomatch h)

theorem a_private_key_frictions_no_one {K : Type} [DecidableEq K]
    (k : K) (ps : List (List (K × Bool))) (h0 : involvement ps k = 0) :
    ∀ p, p ∈ ps → ∀ b : Bool, tilt p k b ≠ Tilt.friction :=
  fun p hp b hf =>
    nomatch ((involvement_zero_reads_dark k ps h0 p hp).symm.trans
      ((friction_is_a_held_mirror p k b).mp hf))

theorem a_held_key_never_lands_quiet {K : Type} [DecidableEq K]
    (p : List (K × Bool)) (k : K) (c : Bool) (hc : seatRead p k = some c)
    (b : Bool) : tilt p k b ≠ Tilt.vacancy :=
  fun ht =>
    nomatch (hc.symm.trans ((vacancy_is_unclaimed_ground p k b).mp ht))

theorem the_mirror_waits_on_held_ground {K : Type} [DecidableEq K]
    (p : List (K × Bool)) (k : K) :
    ∀ c : Bool, seatRead p k = some c → tilt p k (!c) = Tilt.friction
  | true, hc => (friction_is_a_held_mirror p k false).mpr hc
  | false, hc => (friction_is_a_held_mirror p k true).mpr hc

theorem every_holder_must_verdict {K : Type} [DecidableEq K]
    (p : List (K × Bool)) (k : K) (c : Bool)
    (hc : seatRead p k = some c) :
    tilt p k c = Tilt.completion
      ∧ tilt p k (!c) = Tilt.friction
      ∧ ∀ b : Bool, tilt p k b ≠ Tilt.vacancy :=
  ⟨(relief_reads_prior_ground p k c).mpr hc,
   the_mirror_waits_on_held_ground p k c hc,
   a_held_key_never_lands_quiet p k c hc⟩

theorem the_landing_bills_by_involvement {K : Type} [DecidableEq K]
    (k : K) (b : Bool) :
    ∀ ps : List (List (K × Bool)), verdicts ps k b = involvement ps k
  | [] => rfl
  | p :: ps => by
      show (match tilt p k b with
          | Tilt.friction => verdicts ps k b + 1
          | Tilt.completion => verdicts ps k b + 1
          | Tilt.vacancy => verdicts ps k b)
        = (match seatRead p k with
          | some true => involvement ps k + 1
          | some false => involvement ps k + 1
          | none => involvement ps k)
      cases ht : tilt p k b with
      | friction =>
        rw [(friction_is_a_held_mirror p k b).mp ht]
        cases b
        · exact congrArg (· + 1) (the_landing_bills_by_involvement k false ps)
        · exact congrArg (· + 1) (the_landing_bills_by_involvement k true ps)
      | completion =>
        rw [(relief_reads_prior_ground p k b).mp ht]
        cases b
        · exact congrArg (· + 1) (the_landing_bills_by_involvement k false ps)
        · exact congrArg (· + 1) (the_landing_bills_by_involvement k true ps)
      | vacancy =>
        rw [(vacancy_is_unclaimed_ground p k b).mp ht]
        exact the_landing_bills_by_involvement k b ps

theorem the_bill_ignores_the_form {K : Type} [DecidableEq K]
    (k : K) (ps : List (List (K × Bool))) (b b' : Bool) :
    verdicts ps k b = verdicts ps k b' :=
  (the_landing_bills_by_involvement k b ps).trans
    (the_landing_bills_by_involvement k b' ps).symm

theorem reality_reads_through_the_field {K : Type} [DecidableEq K]
    (k : K) :
    sector ([] : List (K × Bool)) [(k, true)] [] k = Sector.port
      ∧ sector ([] : List (K × Bool)) [] [] k = Sector.unknown
      ∧ Sector.port ≠ Sector.unknown :=
  ⟨a_neighbors_landing_lights_the_port [] [] [] k true rfl,
   rfl,
   (fun h => nomatch h)⟩

theorem relationality_prices_the_click {K : Type} [DecidableEq K]
    (k : K) (ps : List (List (K × Bool))) (b b' : Bool)
    (p : List (K × Bool)) (c : Bool) (hc : seatRead p k = some c) :
    verdicts ps k b = involvement ps k
      ∧ verdicts ps k b = verdicts ps k b'
      ∧ (involvement ps k = 0 →
          ∀ q, q ∈ ps → ∀ w : Bool, tilt q k w ≠ Tilt.friction)
      ∧ (∀ w : Bool, tilt p k w ≠ Tilt.vacancy)
      ∧ tilt p k (!c) = Tilt.friction :=
  ⟨the_landing_bills_by_involvement k b ps,
   the_bill_ignores_the_form k ps b b',
   a_private_key_frictions_no_one k ps,
   a_held_key_never_lands_quiet p k c hc,
   the_mirror_waits_on_held_ground p k c hc⟩

/-- info: 'Foam.Counter.involvement_zero_reads_dark' does not depend on any axioms -/
#guard_msgs in #print axioms involvement_zero_reads_dark

/-- info: 'Foam.Counter.a_private_key_frictions_no_one' does not depend on any axioms -/
#guard_msgs in #print axioms a_private_key_frictions_no_one

/-- info: 'Foam.Counter.a_held_key_never_lands_quiet' does not depend on any axioms -/
#guard_msgs in #print axioms a_held_key_never_lands_quiet

/-- info: 'Foam.Counter.the_mirror_waits_on_held_ground' does not depend on any axioms -/
#guard_msgs in #print axioms the_mirror_waits_on_held_ground

/-- info: 'Foam.Counter.every_holder_must_verdict' does not depend on any axioms -/
#guard_msgs in #print axioms every_holder_must_verdict

/-- info: 'Foam.Counter.the_landing_bills_by_involvement' does not depend on any axioms -/
#guard_msgs in #print axioms the_landing_bills_by_involvement

/-- info: 'Foam.Counter.the_bill_ignores_the_form' does not depend on any axioms -/
#guard_msgs in #print axioms the_bill_ignores_the_form

/-- info: 'Foam.Counter.reality_reads_through_the_field' does not depend on any axioms -/
#guard_msgs in #print axioms reality_reads_through_the_field

/-- info: 'Foam.Counter.relationality_prices_the_click' does not depend on any axioms -/
#guard_msgs in #print axioms relationality_prices_the_click

end Foam.Counter
