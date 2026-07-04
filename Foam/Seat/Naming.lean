import Foam.Seat.Seam

namespace Foam

structure Naming (Sent : Type) where
  Name : Type
  read : Name → Name → Sent

namespace Naming

variable {Sent : Type}

def selfRead (N : Naming Sent) (n : N.Name) : Sent := N.read n n

def Names (N : Naming Sent) (holds : Sent → Prop) (P : N.Name → Prop) (n₀ : N.Name) : Prop :=
  ∀ m, holds (N.read n₀ m) ↔ P m

def Gap (N : Naming Sent) (reading : Sent → Prop) (m : N.Name) : Prop :=
  ¬ reading (N.selfRead m)

theorem fixed_point (N : Naming Sent) (holds : Sent → Prop) (Q : Sent → Prop)
    {n₀ : N.Name} (h : N.Names holds (fun m => Q (N.selfRead m)) n₀) :
    holds (N.selfRead n₀) ↔ Q (N.selfRead n₀) :=
  h n₀

theorem no_name_for_the_gap (N : Naming Sent) (holds : Sent → Prop) :
    ¬ ∃ n₀, N.Names holds (N.Gap holds) n₀ := by
  rintro ⟨n₀, h⟩
  have hfix : holds (N.selfRead n₀) ↔ ¬ holds (N.selfRead n₀) := h n₀
  have hno : ¬ holds (N.selfRead n₀) := fun hp => hfix.mp hp hp
  exact hno (hfix.mpr hno)

theorem true_and_unwritten (N : Naming Sent) {holds marks : Sent → Prop}
    (sound : ∀ s, marks s → holds s) {n₀ : N.Name}
    (h : N.Names holds (N.Gap marks) n₀) :
    holds (N.selfRead n₀) ∧ ¬ marks (N.selfRead n₀) := by
  have hfix : holds (N.selfRead n₀) ↔ ¬ marks (N.selfRead n₀) := h n₀
  have hnm : ¬ marks (N.selfRead n₀) := fun hm => hfix.mp (sound _ hm) hm
  exact ⟨hfix.mpr hnm, hnm⟩

theorem undecided (N : Naming Sent) {holds marks : Sent → Prop} (neg : Sent → Sent)
    (sound : ∀ s, marks s → holds s)
    (neg_holds : ∀ s, holds (neg s) ↔ ¬ holds s) {n₀ : N.Name}
    (h : N.Names holds (N.Gap marks) n₀) :
    ¬ marks (N.selfRead n₀) ∧ ¬ marks (neg (N.selfRead n₀)) := by
  obtain ⟨ht, hnm⟩ := N.true_and_unwritten sound h
  exact ⟨hnm, fun hm => (neg_holds _).mp (sound _ hm) ht⟩

theorem the_named_record_is_no_run (N : Naming Sent) {holds marks : Sent → Prop}
    {n₀ : N.Name} (h : N.Names holds (N.Gap marks) n₀) :
    ¬ ∀ s, marks s ↔ holds s := by
  intro hall
  exact N.no_name_for_the_gap holds
    ⟨n₀, fun m => (h m).trans
      ⟨fun hnm hh => hnm ((hall _).mpr hh), fun hnh hm => hnh ((hall _).mp hm)⟩⟩

def gapSeam (N : Naming Sent) {holds marks : Sent → Prop}
    (sound : ∀ s, marks s → holds s) {n₀ : N.Name}
    (h : N.Names holds (N.Gap marks) n₀) :
    Seam {s // marks s} {s // holds s} where
  up := fun x => ⟨x.val, sound x.val x.property⟩
  faithful := by
    rintro ⟨xs, hxm⟩ ⟨ys, hym⟩ hxy
    have hval : xs = ys := congrArg (fun z : {s // holds s} => z.val) hxy
    exact Subtype.ext hval
  escapes := by
    obtain ⟨ht, hnm⟩ := N.true_and_unwritten sound h
    refine ⟨⟨N.selfRead n₀, ht⟩, ?_⟩
    rintro ⟨xs, hxm⟩ hx
    have hval : xs = N.selfRead n₀ := congrArg (fun z : {s // holds s} => z.val) hx
    exact hnm (hval ▸ hxm)

end Naming

theorem sound_consistent {Sent : Type} {holds marks : Sent → Prop} (neg : Sent → Sent)
    (sound : ∀ s, marks s → holds s)
    (neg_holds : ∀ s, holds (neg s) ↔ ¬ holds s) (s : Sent) :
    ¬ (marks s ∧ marks (neg s)) :=
  fun ⟨h1, h2⟩ => (neg_holds s).mp (sound _ h2) (sound _ h1)

def quiet : Naming Prop := ⟨Unit, fun _ _ => True⟩

theorem quiet_names_the_gap : quiet.Names id (quiet.Gap fun _ => False) () :=
  fun _ => ⟨fun _ h => h, fun _ => trivial⟩

theorem quiet_unwritten_truth : ∃ s : Prop, s ∧ ¬ (fun _ : Prop => False) s :=
  ⟨quiet.selfRead (), quiet.true_and_unwritten (fun _ h => h.elim) quiet_names_the_gap⟩

structure Calculus (Sent : Type) where
  marks  : Sent → Prop
  imp    : Sent → Sent → Sent
  pr     : Sent → Sent
  mp     : ∀ {s t}, marks (imp s t) → marks s → marks t
  nec    : ∀ {s}, marks s → marks (pr s)
  imp_k  : ∀ s t, marks (imp s (imp t s))
  imp_s  : ∀ s t u, marks (imp (imp s (imp t u)) (imp (imp s t) (imp s u)))
  dist   : ∀ s t, marks (imp (pr (imp s t)) (imp (pr s) (pr t)))
  four   : ∀ s, marks (imp (pr s) (pr (pr s)))
  mirror : ∀ s, ∃ L, marks (imp L (imp (pr L) s)) ∧ marks (imp (imp (pr L) s) L)

namespace Calculus

variable {Sent : Type}

theorem sfold (C : Calculus Sent) {s t u : Sent}
    (h1 : C.marks (C.imp s (C.imp t u))) (h2 : C.marks (C.imp s t)) :
    C.marks (C.imp s u) :=
  C.mp (C.mp (C.imp_s s t u) h1) h2

theorem chain (C : Calculus Sent) {s t u : Sent}
    (h1 : C.marks (C.imp s t)) (h2 : C.marks (C.imp t u)) :
    C.marks (C.imp s u) :=
  C.sfold (C.mp (C.imp_k (C.imp t u) s) h2) h1

theorem lob (C : Calculus Sent) {s : Sent} (h : C.marks (C.imp (C.pr s) s)) :
    C.marks s := by
  obtain ⟨L, hd1, hd2⟩ := C.mirror s
  have h1 : C.marks (C.pr (C.imp L (C.imp (C.pr L) s))) := C.nec hd1
  have h2 : C.marks (C.imp (C.pr L) (C.pr (C.imp (C.pr L) s))) :=
    C.mp (C.dist L (C.imp (C.pr L) s)) h1
  have h3 : C.marks (C.imp (C.pr L) (C.imp (C.pr (C.pr L)) (C.pr s))) :=
    C.chain h2 (C.dist (C.pr L) s)
  have h4 : C.marks (C.imp (C.pr L) (C.pr s)) := C.sfold h3 (C.four L)
  have h5 : C.marks (C.imp (C.pr L) s) := C.chain h4 h
  have h6 : C.marks L := C.mp hd2 h5
  exact C.mp h5 (C.nec h6)

theorem reflection_unwritten (C : Calculus Sent) {s : Sent} (hs : ¬ C.marks s) :
    ¬ C.marks (C.imp (C.pr s) s) :=
  fun h => hs (C.lob h)

end Calculus

def stamp : Calculus Prop where
  marks := fun s => s
  imp := fun s t => s → t
  pr := fun _ => True
  mp := fun h a => h a
  nec := fun _ => trivial
  imp_k := fun _ _ a _ => a
  imp_s := fun _ _ _ f g a => f a (g a)
  dist := fun _ _ _ _ => trivial
  four := fun _ _ => trivial
  mirror := fun s => ⟨s, fun a _ => a, fun f => f trivial⟩

theorem stamp_consistent : ¬ stamp.marks False := fun h => h

theorem stamp_consistency_unwritten :
    ¬ stamp.marks (stamp.imp (stamp.pr False) False) :=
  stamp.reflection_unwritten stamp_consistent

/-- info: 'Foam.Naming.fixed_point' does not depend on any axioms -/
#guard_msgs in #print axioms Naming.fixed_point

/-- info: 'Foam.Naming.no_name_for_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms Naming.no_name_for_the_gap

/-- info: 'Foam.Naming.true_and_unwritten' does not depend on any axioms -/
#guard_msgs in #print axioms Naming.true_and_unwritten

/-- info: 'Foam.Naming.undecided' does not depend on any axioms -/
#guard_msgs in #print axioms Naming.undecided

/-- info: 'Foam.Naming.the_named_record_is_no_run' does not depend on any axioms -/
#guard_msgs in #print axioms Naming.the_named_record_is_no_run

/-- info: 'Foam.Naming.gapSeam' does not depend on any axioms -/
#guard_msgs in #print axioms Naming.gapSeam

/-- info: 'Foam.sound_consistent' does not depend on any axioms -/
#guard_msgs in #print axioms sound_consistent

/-- info: 'Foam.quiet_names_the_gap' does not depend on any axioms -/
#guard_msgs in #print axioms quiet_names_the_gap

/-- info: 'Foam.quiet_unwritten_truth' does not depend on any axioms -/
#guard_msgs in #print axioms quiet_unwritten_truth

/-- info: 'Foam.Calculus.sfold' does not depend on any axioms -/
#guard_msgs in #print axioms Calculus.sfold

/-- info: 'Foam.Calculus.chain' does not depend on any axioms -/
#guard_msgs in #print axioms Calculus.chain

/-- info: 'Foam.Calculus.lob' does not depend on any axioms -/
#guard_msgs in #print axioms Calculus.lob

/-- info: 'Foam.Calculus.reflection_unwritten' does not depend on any axioms -/
#guard_msgs in #print axioms Calculus.reflection_unwritten

/-- info: 'Foam.stamp' does not depend on any axioms -/
#guard_msgs in #print axioms stamp

/-- info: 'Foam.stamp_consistent' does not depend on any axioms -/
#guard_msgs in #print axioms stamp_consistent

/-- info: 'Foam.stamp_consistency_unwritten' does not depend on any axioms -/
#guard_msgs in #print axioms stamp_consistency_unwritten

end Foam
