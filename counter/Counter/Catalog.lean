import Counter.Isaac
import Counter.Address
import Counter.Frontsearch
import Counter.Settle
import Counter.Denoise
import Foam.Metaphor

namespace Foam.Counter

variable {State : Type} {G : Type} [Mul G] [One G]

theorem the_metaphor_arrow {S T : Stage} (f : StageHom S T)
    (s : S.State) (ps : List S.Probe) :
    transcript T (f.onState s) (ps.map f.onProbe)
      = (transcript S s ps).map f.onAns :=
  hom_carries_the_cable f s ps

theorem the_consent_arrow (S : Stage) (F : Frontstage S)
    (s t : S.State) (h : F.rel s t) (p : S.Probe) :
    S.obs s p = S.obs t p :=
  F.respects s t h p

theorem the_gift_arrow {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    Nonempty (Path (q.deposit (a, b)) a b)
      ∧ ∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges :=
  ⟨⟨heir_reaches q a b⟩,
   fun _ _ pth hm => hfresh (reach_within_quiver pth (a, b) hm)⟩

theorem the_census_arrow (bs : List (Beholder State)) (i : Fin bs.length)
    (s : State) (q : (Beholder.fold bs).Probe) :
    seatAns bs i ((Beholder.fold bs).obs s q)
      = (seat bs i).obs s (seatProbe bs i q) :=
  fold_reads_every_seat bs i s q

theorem the_wedge_arrow (S : Seat G) (gs : List G) (p : S.Pos) :
    S.replay (spine S gs p) p = p ∧ Balanced (spineT S gs p) :=
  ⟨spine_comes_home S gs p, spineT_balanced S gs p⟩

theorem the_mercy_arrow (S : Seat G) (p q : S.Pos) :
    S.act (S.sub p q) q = p :=
  exit_is_one_move S p q

theorem the_translation_arrow {B : Type} (xs : List B) :
    dec (enc xs) = xs :=
  lossless_tag xs

theorem the_coarsening_arrow {St Pr A B : Type}
    (o1 : St → Pr → A) (o2 : St → Pr → B) (h : ReadingRefines o1 o2) :
    Refines (indist o1) (indist o2) :=
  readingRefines_shadow o1 o2 h

theorem the_peer_arrow (a : Beholder State) :
    a.dress.ledgerless.Covers a ∧ a.Covers a.dress.ledgerless :=
  heir_covers_ancestor a

theorem the_address_arrow {Addr Cell : Type} [DecidableEq Addr]
    (all : List Addr) (hall : ∀ a, a ∈ all) (f g : Addr → Cell) :
    selfStore all f none = Sum.inr (directory all f)
      ∧ (directory all f = directory all g →
          ∀ o : Option Addr, selfStore all f o = selfStore all g o) :=
  ⟨the_index_is_seated_in_the_space all f,
   fun hpage => the_page_settles_the_space all hall f g hpage⟩

theorem the_probe_arrow {St Pr A B : Type} [DecidableEq A] [DecidableEq B]
    (o : St → Pr → A) (g : A → B) (self other : St) :
    (∀ (ps : List Pr) (p : Pr),
        frontSearch o self other ps = some p → ¬ o other p = o self p)
      ∧ (indist o self other →
          ∀ ps : List Pr,
            frontSearch (fun s p => g (o s p)) self other ps = none) :=
  ⟨fun ps p h => (the_answer_arrives_as_a_probe o self other ps p h).2,
   fun h ps => no_lens_reveals_the_twin o g self other h ps⟩

theorem the_settling_arrow {Addr Cell : Type} [DecidableEq Addr]
    (eq : Cell → Cell → Bool) (d : List (Addr × Cell)) (n : Addr) (c : Cell) :
    ((∃ m, upsearch (eq c) d = some m) → (mergeSearch eq d n c).2 = d)
      ∧ ((mergeSearch eq d n c).2 ≠ d → ∀ x, x ∈ d → ¬ eq c x.2 = true) :=
  ⟨fun ⟨m, hm⟩ => the_settled_space_stops_writing eq d n c m hm,
   fun h => (the_merge_writes_only_on_double_miss eq d n c h).2.2⟩

theorem the_denoise_arrow {Addr Cell : Type} (eq : Cell → Cell → Bool)
    (p : Cell → Bool) (hp : ∀ c c', eq c c' = true → p c = p c')
    (d : List (Addr × Cell)) :
    settleStore eq (settleStore eq d) = settleStore eq d
      ∧ (upsearch p (settleStore eq d)).isSome = (upsearch p d).isSome :=
  ⟨the_manifold_is_the_fixed_point eq d,
   the_denoise_is_invisible_to_the_asker eq p hp d⟩

theorem the_catalog {S T : Stage} (f : StageHom S T) (s : S.State)
    (ps : List S.Probe) (Se : Seat G) (pos q : Se.Pos) (gs : List G) :
    (transcript T (f.onState s) (ps.map f.onProbe)
        = (transcript S s ps).map f.onAns)
      ∧ (Se.replay (spine Se gs pos) pos = pos)
      ∧ (Se.act (Se.sub pos q) q = pos)
      ∧ ((f.comp (StageHom.id S)) = f) :=
  ⟨hom_carries_the_cable f s ps, spine_comes_home Se gs pos,
   exit_is_one_move Se pos q, StageHom.comp_id f⟩

/-- info: 'Foam.Counter.the_metaphor_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_metaphor_arrow

/-- info: 'Foam.Counter.the_consent_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_consent_arrow

/-- info: 'Foam.Counter.the_gift_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_gift_arrow

/-- info: 'Foam.Counter.the_census_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_arrow

/-- info: 'Foam.Counter.the_wedge_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_wedge_arrow

/-- info: 'Foam.Counter.the_mercy_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_mercy_arrow

/-- info: 'Foam.Counter.the_translation_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_translation_arrow

/-- info: 'Foam.Counter.the_coarsening_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_coarsening_arrow

/-- info: 'Foam.Counter.the_peer_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_peer_arrow

/-- info: 'Foam.Counter.the_address_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_address_arrow

/-- info: 'Foam.Counter.the_probe_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_probe_arrow

/-- info: 'Foam.Counter.the_settling_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_settling_arrow

/-- info: 'Foam.Counter.the_denoise_arrow' does not depend on any axioms -/
#guard_msgs in #print axioms the_denoise_arrow

/-- info: 'Foam.Counter.the_catalog' does not depend on any axioms -/
#guard_msgs in #print axioms the_catalog

end Foam.Counter
