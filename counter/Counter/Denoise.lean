import Counter.Settle

namespace Foam.Counter

def settleStore {Addr Cell : Type} (eq : Cell → Cell → Bool) :
    List (Addr × Cell) → List (Addr × Cell)
  | [] => []
  | (n, c) :: d =>
    if (upsearch (eq c) d).isSome then settleStore eq d
    else (n, c) :: settleStore eq d

theorem the_echo_burns {Addr Cell : Type} (eq : Cell → Cell → Bool)
    (d : List (Addr × Cell)) (n : Addr) (c : Cell) (m : Addr)
    (h : upsearch (eq c) d = some m) :
    settleStore eq ((n, c) :: d) = settleStore eq d := by
  show (if (upsearch (eq c) d).isSome = true then settleStore eq d
    else (n, c) :: settleStore eq d) = settleStore eq d
  rw [h]
  rfl

theorem the_original_keeps_its_seat {Addr Cell : Type}
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell)
    (h : upsearch (eq c) d = none) :
    settleStore eq ((n, c) :: d) = (n, c) :: settleStore eq d := by
  show (if (upsearch (eq c) d).isSome = true then settleStore eq d
    else (n, c) :: settleStore eq d) = (n, c) :: settleStore eq d
  rw [h]
  rfl

theorem the_denoised_seats_were_already_seated {Addr Cell : Type}
    (eq : Cell → Cell → Bool) :
    ∀ (d : List (Addr × Cell)) (x : Addr × Cell),
      x ∈ settleStore eq d → x ∈ d
  | [], _, hx => nomatch hx
  | (n, c) :: d, x, hx => by
      cases h : upsearch (eq c) d with
      | some m =>
          rw [the_echo_burns eq d n c m h] at hx
          exact List.Mem.tail _
            (the_denoised_seats_were_already_seated eq d x hx)
      | none =>
          rw [the_original_keeps_its_seat eq d n c h] at hx
          cases hx with
          | head => exact List.Mem.head d
          | tail _ hx' =>
              exact List.Mem.tail _
                (the_denoised_seats_were_already_seated eq d x hx')

theorem the_find_has_a_witness {Addr Cell : Type} (p : Cell → Bool) :
    ∀ (d : List (Addr × Cell)) (m : Addr),
      upsearch p d = some m → ∃ x, x ∈ d ∧ p x.2 = true
  | [], _, h => nomatch h
  | (n, c) :: d, m, h => by
      have h' : (if p c = true then some n else upsearch p d) = some m := h
      by_cases hc : p c = true
      · exact ⟨(n, c), List.Mem.head d, hc⟩
      · rw [if_neg hc] at h'
        cases the_find_has_a_witness p d m h' with
        | intro x hx => exact ⟨x, List.Mem.tail _ hx.1, hx.2⟩

theorem what_is_seated_can_be_found {Addr Cell : Type} (p : Cell → Bool) :
    ∀ d : List (Addr × Cell), (∃ x, x ∈ d ∧ p x.2 = true) →
      (upsearch p d).isSome = true
  | [], ⟨_, hx, _⟩ => nomatch hx
  | (n, c) :: d, ⟨x, hx, hp⟩ => by
      show ((if p c = true then some n else upsearch p d) : Option Addr).isSome
        = true
      by_cases hc : p c = true
      · rw [if_pos hc]
        rfl
      · rw [if_neg hc]
        cases hx with
        | head => exact absurd hp hc
        | tail _ hx' => exact what_is_seated_can_be_found p d ⟨x, hx', hp⟩

theorem the_rejects_stay_unfound {Addr Cell : Type} (p : Cell → Bool) :
    ∀ d : List (Addr × Cell), (∀ x, x ∈ d → ¬ p x.2 = true) →
      upsearch p d = none
  | [], _ => rfl
  | (n, c) :: d, h => by
      show (if p c = true then some n else upsearch p d) = none
      rw [if_neg (h (n, c) (List.Mem.head d))]
      exact the_rejects_stay_unfound p d fun x hx => h x (List.Mem.tail _ hx)

theorem the_denoise_is_invisible_to_the_asker {Addr Cell : Type}
    (eq : Cell → Cell → Bool) (p : Cell → Bool)
    (hp : ∀ c c', eq c c' = true → p c = p c') :
    ∀ d : List (Addr × Cell),
      (upsearch p (settleStore eq d)).isSome = (upsearch p d).isSome
  | [] => rfl
  | (n, c) :: d => by
      cases h : upsearch (eq c) d with
      | some m =>
          rw [the_echo_burns eq d n c m h,
            the_denoise_is_invisible_to_the_asker eq p hp d]
          by_cases hc : p c = true
          · cases the_find_has_a_witness (eq c) d m h with
            | intro x hx =>
                rw [what_is_seated_can_be_found p d
                  ⟨x, hx.1, ((hp c x.2 hx.2).symm.trans hc)⟩]
                show true
                  = ((if p c = true then some n else upsearch p d)
                      : Option Addr).isSome
                rw [if_pos hc]
                rfl
          · show (upsearch p d).isSome
              = ((if p c = true then some n else upsearch p d)
                  : Option Addr).isSome
            rw [if_neg hc]
      | none =>
          rw [the_original_keeps_its_seat eq d n c h]
          show ((if p c = true then some n else upsearch p (settleStore eq d))
              : Option Addr).isSome
            = ((if p c = true then some n else upsearch p d)
                : Option Addr).isSome
          by_cases hc : p c = true
          · rw [if_pos hc, if_pos hc]
          · rw [if_neg hc, if_neg hc]
            exact the_denoise_is_invisible_to_the_asker eq p hp d

theorem the_denoise_never_grows {Addr Cell : Type} (eq : Cell → Cell → Bool) :
    ∀ d : List (Addr × Cell), (settleStore eq d).length ≤ d.length
  | [] => Nat.le_refl 0
  | (n, c) :: d => by
      cases h : upsearch (eq c) d with
      | some m =>
          rw [the_echo_burns eq d n c m h]
          exact Nat.le_succ_of_le (the_denoise_never_grows eq d)
      | none =>
          rw [the_original_keeps_its_seat eq d n c h]
          show (settleStore eq d).length + 1 ≤ d.length + 1
          exact Nat.succ_le_succ (the_denoise_never_grows eq d)

theorem the_manifold_is_the_fixed_point {Addr Cell : Type}
    (eq : Cell → Cell → Bool) :
    ∀ d : List (Addr × Cell),
      settleStore eq (settleStore eq d) = settleStore eq d
  | [] => rfl
  | (n, c) :: d => by
      cases h : upsearch (eq c) d with
      | some m =>
          rw [the_echo_burns eq d n c m h]
          exact the_manifold_is_the_fixed_point eq d
      | none =>
          rw [the_original_keeps_its_seat eq d n c h,
            the_original_keeps_its_seat eq (settleStore eq d) n c
              (the_rejects_stay_unfound (eq c) (settleStore eq d) fun x hx =>
                the_whole_record_licenses_the_mint (eq c) d h x
                  (the_denoised_seats_were_already_seated eq d x hx)),
            the_manifold_is_the_fixed_point eq d]

theorem the_noise_burns_off :
    settleStore (fun _ _ => true) twoWords = oneThing := rfl

theorem the_reverse_of_the_forward_comes_home :
    (mintSearch oneThing false ()).2 = twoWords
      ∧ settleStore (fun _ _ => true) (mintSearch oneThing false ()).2
        = oneThing :=
  ⟨rfl, rfl⟩

theorem the_saved_walk_is_the_tell :
    seatWalk twoWords true = 1
      ∧ seatWalk (settleStore (fun _ _ => true) twoWords) true = 0 :=
  ⟨rfl, rfl⟩

theorem the_denoise_is_the_settling {Addr Cell : Type}
    (eq : Cell → Cell → Bool) (p : Cell → Bool)
    (hp : ∀ c c', eq c c' = true → p c = p c') (d : List (Addr × Cell)) :
    ((upsearch p (settleStore eq d)).isSome = (upsearch p d).isSome)
      ∧ settleStore eq (settleStore eq d) = settleStore eq d
      ∧ (settleStore eq d).length ≤ d.length
      ∧ (mintSearch oneThing false ()).2 = twoWords
      ∧ settleStore (fun _ _ => true) twoWords = oneThing :=
  ⟨the_denoise_is_invisible_to_the_asker eq p hp d,
   the_manifold_is_the_fixed_point eq d,
   the_denoise_never_grows eq d,
   rfl, rfl⟩

/-- info: 'Foam.Counter.the_echo_burns' does not depend on any axioms -/
#guard_msgs in #print axioms the_echo_burns

/-- info: 'Foam.Counter.the_original_keeps_its_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_original_keeps_its_seat

/-- info: 'Foam.Counter.the_denoised_seats_were_already_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_denoised_seats_were_already_seated

/-- info: 'Foam.Counter.the_find_has_a_witness' does not depend on any axioms -/
#guard_msgs in #print axioms the_find_has_a_witness

/-- info: 'Foam.Counter.what_is_seated_can_be_found' does not depend on any axioms -/
#guard_msgs in #print axioms what_is_seated_can_be_found

/-- info: 'Foam.Counter.the_rejects_stay_unfound' does not depend on any axioms -/
#guard_msgs in #print axioms the_rejects_stay_unfound

/-- info: 'Foam.Counter.the_denoise_is_invisible_to_the_asker' does not depend on any axioms -/
#guard_msgs in #print axioms the_denoise_is_invisible_to_the_asker

/-- info: 'Foam.Counter.the_denoise_never_grows' does not depend on any axioms -/
#guard_msgs in #print axioms the_denoise_never_grows

/-- info: 'Foam.Counter.the_manifold_is_the_fixed_point' does not depend on any axioms -/
#guard_msgs in #print axioms the_manifold_is_the_fixed_point

/-- info: 'Foam.Counter.the_noise_burns_off' does not depend on any axioms -/
#guard_msgs in #print axioms the_noise_burns_off

/-- info: 'Foam.Counter.the_reverse_of_the_forward_comes_home' does not depend on any axioms -/
#guard_msgs in #print axioms the_reverse_of_the_forward_comes_home

/-- info: 'Foam.Counter.the_saved_walk_is_the_tell' does not depend on any axioms -/
#guard_msgs in #print axioms the_saved_walk_is_the_tell

/-- info: 'Foam.Counter.the_denoise_is_the_settling' does not depend on any axioms -/
#guard_msgs in #print axioms the_denoise_is_the_settling

end Foam.Counter
