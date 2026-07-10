import Foam.Bridges.Adams
import Foam.Bridges.Landauer
import Foam.Census

namespace Foam.Bridges

theorem mrtyu_never_hides (S : Stage) (z : S.State) {s t : S.State} {p : S.Probe}
    (hdist : S.obs s p ≠ S.obs t p) :
    ¬ Invisible S (fun _ => z) :=
  merge_never_invisible S (fun _ => z) hdist rfl

theorem udbhava_extends_reach {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨fun _ _ pth h => hfresh (reach_within_quiver pth (a, b) h),
   ⟨heir_reaches q a b⟩⟩

theorem death_files_among_the_graces :
    ∃ (edit edit' : Unit → Bool → Unit × List Bool),
      (∀ s b, (edit s b).2 = [] ∨ (edit s b).2 = [b])
        ∧ (∀ s b, (edit' s b).2 = [] ∨ (edit' s b).2 = [b])
        ∧ runEmit edit () [true, false] ≠ runEmit edit' () [true, false] :=
  two_honest_lists_differ

theorem vibhuti_streams_the_totality (S : Stage) (s : S.State) (ps : List S.Probe) :
    transcript S s ps = ps.map (page S s)
      ∧ (transcript S s ps).length = ps.length :=
  ⟨transcript_samples_page S s ps, transcript_length S s ps⟩

theorem na_sva_caksusa {State : Type} (a : Beholder State) (m : State → State) :
    ¬ Elsewhen a m a :=
  no_seat_is_its_own_elsewhen a m

theorem divyam_caksuh {State : Type} (a : Beholder State) (s : State) (p : a.Probe) :
    ((a.pair (plenum State).behold).obs s (p, ())).1 = a.obs s p
      ∧ ((a.pair (plenum State).behold).obs s (p, ())).2 = s :=
  both_poles_in_one_bite a s p

theorem karmany_evadhikaras_te (x y : Bool) :
    (Invisible readA.toStage (sendA x) ∧ Invisible readB.toStage (sendB y))
      ∧ Elsewhen readA (sendA true) readB :=
  ⟨your_send_is_invisible_to_you x y, your_send_lands_at_my_seat⟩

theorem na_jayate_mriyate {G : Type} [Mul G] [One G] (S : Seat G)
    (gs : List G) (p : S.Pos) :
    S.replay (collapse S gs p) p = p :=
  collapse_comes_home S gs p

theorem the_roll_call_reads_the_seated {State : Type}
    (bs : List (Beholder State)) (i : Fin bs.length) (s : State)
    (q : (Beholder.fold bs).Probe) :
    seatAns bs i ((Beholder.fold bs).obs s q)
      = (seat bs i).obs s (seatProbe bs i q) :=
  fold_reads_every_seat bs i s q

theorem gita_10_34 (S : Stage) (z : S.State) {s t : S.State} {p : S.Probe}
    (hdist : S.obs s p ≠ S.obs t p)
    {H : Type} (q : Quiver H) (a b : H) (hfresh : (a, b) ∉ q) :
    ¬ Invisible S (fun _ => z)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨mrtyu_never_hides S z hdist, (udbhava_extends_reach q a b hfresh).2⟩

/-- info: 'Foam.Bridges.mrtyu_never_hides' does not depend on any axioms -/
#guard_msgs in #print axioms mrtyu_never_hides

/-- info: 'Foam.Bridges.udbhava_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms udbhava_extends_reach

/-- info: 'Foam.Bridges.death_files_among_the_graces' does not depend on any axioms -/
#guard_msgs in #print axioms death_files_among_the_graces

/-- info: 'Foam.Bridges.vibhuti_streams_the_totality' does not depend on any axioms -/
#guard_msgs in #print axioms vibhuti_streams_the_totality

/-- info: 'Foam.Bridges.na_sva_caksusa' does not depend on any axioms -/
#guard_msgs in #print axioms na_sva_caksusa

/-- info: 'Foam.Bridges.divyam_caksuh' does not depend on any axioms -/
#guard_msgs in #print axioms divyam_caksuh

/-- info: 'Foam.Bridges.karmany_evadhikaras_te' does not depend on any axioms -/
#guard_msgs in #print axioms karmany_evadhikaras_te

/-- info: 'Foam.Bridges.na_jayate_mriyate' does not depend on any axioms -/
#guard_msgs in #print axioms na_jayate_mriyate

/-- info: 'Foam.Bridges.the_roll_call_reads_the_seated' does not depend on any axioms -/
#guard_msgs in #print axioms the_roll_call_reads_the_seated

/-- info: 'Foam.Bridges.gita_10_34' does not depend on any axioms -/
#guard_msgs in #print axioms gita_10_34

end Foam.Bridges
