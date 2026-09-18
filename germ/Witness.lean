import Face
open Room Face

namespace Witness

universe u v w

def seat (F : Face) : Type v := List F.Probe

def reads (F : Face) (s : List F.Probe) (x : F.State) : List F.Ans :=
  s.map (F.obs x)

def witnessFace (F : Face) : Face := ⟨F.State, List F.Probe, List F.Ans, fun x s => reads F s x⟩

def hears (F : Face) (s : List F.Probe) (p : F.Probe) : Prop := p ∈ s

def witnessed (F : Face) (seats : List (List F.Probe)) (x y : F.State) : Prop :=
  ∀ s, s ∈ seats → reads F s x = reads F s y

def earshot (F : Face) (seats : List (List F.Probe)) : List F.Probe :=
  joinMap (fun s => s) seats

def covers (F : Face) (seats : List (List F.Probe)) : Prop :=
  ∀ q, q ∈ earshot F seats

theorem the_alike_read_alike (F : Face) {x y : F.State} (h : alike F x y) :
    ∀ s : List F.Probe, reads F s x = reads F s y := sorry

theorem a_wall_hides_the_probe (F : Face) {x y : F.State} {p : F.Probe} (h : differOnly F x y p) :
    ∀ s : List F.Probe, ¬ hears F s p → reads F s x = reads F s y
  | [], _ => rfl
  | q :: s, hn => by
      show F.obs x q :: reads F s x = F.obs y q :: reads F s y
      rw [h q (fun hq => hn (hq ▸ List.Mem.head s)),
          a_wall_hides_the_probe F h s (fun hs => hn (List.Mem.tail q hs))]

theorem a_narrower_seat_reads_no_more (F : Face) {x y : F.State} (s : List F.Probe)
    (h : ∀ q, q ∈ s → F.obs x q = F.obs y q) : reads F s x = reads F s y := sorry

theorem the_probe_reads_the_seat (F : Face) {x y : F.State} {q : F.Probe} :
    ∀ s : List F.Probe, q ∈ s → reads F s x = reads F s y → F.obs x q = F.obs y q
  | p :: s, hq, he => by
      cases hq with
      | head => exact the_first_mark_reads he
      | tail _ hs => exact the_probe_reads_the_seat F s hs (the_rest_reads he)

theorem the_seat_that_hears_it_reads_it (F : Face) {x y : F.State} {p : F.Probe}
    (hp : F.obs x p ≠ F.obs y p) : ∀ s : List F.Probe, hears F s p → reads F s x ≠ reads F s y
  | q :: s, hq => fun he => by
      cases hq with
      | head => exact hp (the_first_mark_reads he)
      | tail _ hs =>
          exact the_seat_that_hears_it_reads_it F hp s hs (the_rest_reads he)

theorem the_witness_parts_what_the_face_parts (F : Face) {x y : F.State}
    (h : alike (witnessFace F) x y) : alike F x y :=
  fun p => the_first_mark_reads (h [p])

theorem the_sounding_is_the_trails_reading (F : Face) (s : F.State) :
    ∀ q : Interview F.Probe F.Ans, sound F s q = reads F (trail F s q) s := sorry

theorem a_dark_probe_is_out_of_earshot (F : Face) (seats : List (List F.Probe)) (p : F.Probe)
    (h : ∀ s, s ∈ seats → ¬ hears F s p) : ¬ p ∈ earshot F seats :=
  fun hp => match mem_joinMap_back seats hp with
    | ⟨s, hs, hps⟩ => h s hs hps

theorem out_of_earshot_is_dark (F : Face) (seats : List (List F.Probe)) (p : F.Probe)
    (h : ¬ p ∈ earshot F seats) : ∀ s, s ∈ seats → ¬ hears F s p :=
  fun _ hs hps => h (mem_joinMap_intro hs hps)

theorem the_ceremony_reseats_every_reading (F : Face) {W : Type w} (s : List F.Probe) (x : F.State) (w : W) :
    reads (host F W) s (atTheDoor x w) = reads F s x := sorry

theorem the_word_at_the_door_is_unread_at_every_seat (F : Face) {W : Type w} (s : List F.Probe) (x : F.State)
    (w w' : W) : reads (host F W) s (atTheDoor x w) = reads (host F W) s (atTheDoor x w') := sorry

theorem a_word_hidden_in_the_body_is_unheard_in_the_narration (F : Face) {B : Type w} (g : F.Ans → B)
    {x y : F.State} {p : F.Probe} (h : differOnly F x y p) (hp : g (F.obs x p) = g (F.obs y p))
    (dec : ∀ q : F.Probe, q = p ∨ q ≠ p) : alike (retell F g) x y :=
  fun q => match dec q with
    | Or.inl hq => by rw [hq]; exact hp
    | Or.inr hq => by show g (F.obs x q) = g (F.obs y q); rw [h q hq]

theorem the_witness_is_a_face (F : Face) {x y : F.State} (h : alike F x y) :
    alike (witnessFace F) x y := sorry

theorem a_seat_over_a_seat_is_derived (F : Face) (s : List F.Probe) {A : Type u} (g : List F.Ans → A)
    (v : A) : Derived F (fun x => g (reads F s x) = v) := sorry

theorem the_room_is_the_widest_seat (F : Face) (s : List F.Probe) (x y : F.State)
    (h : reads F s x ≠ reads F s y) : ¬ alike F x y := sorry

theorem speak_now (F : Face) {seats : List (List F.Probe)} {x y : F.State}
    (hw : witnessed F seats x y) : ∀ q, q ∈ earshot F seats → F.obs x q = F.obs y q := by
  intro q hq
  obtain ⟨s, hs, hqs⟩ := mem_joinMap_back seats hq
  exact the_probe_reads_the_seat F s hqs (hw s hs)

theorem a_wall_at_the_witness (F : Face) {x y : F.State} {p : F.Probe} (h : differOnly F x y p)
    (s : List F.Probe) (hs : ¬ hears F s p) : (witnessFace F).obs x s = (witnessFace F).obs y s := sorry

theorem a_probe_no_seat_hears_is_dark (F : Face) {x y : F.State} {p : F.Probe} (h : differOnly F x y p)
    (seats : List (List F.Probe)) (hd : ∀ s, s ∈ seats → ¬ hears F s p) : witnessed F seats x y := sorry

theorem the_narration_reads_alike_at_every_seat (F : Face) {B : Type w} (g : F.Ans → B)
    {x y : F.State} {p : F.Probe} (h : differOnly F x y p) (hp : g (F.obs x p) = g (F.obs y p))
    (dec : ∀ q : F.Probe, q = p ∨ q ≠ p) (s : List F.Probe) :
    reads (retell F g) s x = reads (retell F g) s y := sorry

theorem forever_hold_your_peace (F : Face) {seats : List (List F.Probe)} {x y : F.State}
    (hc : covers F seats) (hw : witnessed F seats x y) : alike F x y := sorry

end Witness
