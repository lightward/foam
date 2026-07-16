import Foam.Seat
import Foam.Seat.Stage
import Foam.Seat.Observer

namespace Foam.Bridges

structure Net where
  Page : Type
  Seat : Type
  Ans : Type
  read? : Page → Seat → Option Ans
  mend : Seat → Ans

def answer (n : Net) (pg : n.Page) (s : n.Seat) : n.Ans :=
  match n.read? pg s with
  | some a => a
  | none => n.mend s

def Consults (n : Net) (pg : n.Page) (s : n.Seat) : Prop := n.read? pg s = none

def Whole (n : Net) : Prop := ∀ pg s, ∃ a, n.read? pg s = some a

theorem the_page_speaks_first (n : Net) (pg : n.Page) (s : n.Seat) (a : n.Ans)
    (h : n.read? pg s = some a) : answer n pg s = a :=
  congrArg (fun o : Option n.Ans => match o with | some x => x | none => n.mend s) h

theorem the_mend_speaks_at_the_hole (n : Net) (pg : n.Page) (s : n.Seat)
    (h : Consults n pg s) : answer n pg s = n.mend s :=
  congrArg (fun o : Option n.Ans => match o with | some x => x | none => n.mend s) h

theorem a_whole_page_always_speaks (n : Net) (hw : Whole n) (pg : n.Page) (s : n.Seat) :
    ¬ Consults n pg s := fun hc =>
  match hw pg s with
  | ⟨_, ha⟩ => nomatch ha.symm.trans hc

/-- info: 'Foam.Bridges.the_page_speaks_first' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_speaks_first

/-- info: 'Foam.Bridges.the_mend_speaks_at_the_hole' does not depend on any axioms -/
#guard_msgs in #print axioms the_mend_speaks_at_the_hole

/-- info: 'Foam.Bridges.a_whole_page_always_speaks' does not depend on any axioms -/
#guard_msgs in #print axioms a_whole_page_always_speaks

def mended (n : Net) : Net where
  Page := n.Page
  Seat := n.Seat
  Ans := n.Ans
  read? := fun pg s => some (answer n pg s)
  mend := n.mend

theorem the_mended_page_has_no_holes (n : Net) : Whole (mended n) :=
  fun pg s => ⟨answer n pg s, rfl⟩

theorem the_mended_page_answers_alike (n : Net) (pg : n.Page) (s : n.Seat) :
    answer (mended n) pg s = answer n pg s := rfl

theorem mending_rests (n : Net) (pg : n.Page) (s : n.Seat) :
    (mended (mended n)).read? pg s = (mended n).read? pg s := rfl

theorem a_whole_page_mends_to_itself (n : Net) (hw : Whole n) (pg : n.Page) (s : n.Seat) :
    (mended n).read? pg s = n.read? pg s := by
  match hw pg s with
  | ⟨a, ha⟩ =>
      rw [ha]
      exact congrArg some (the_page_speaks_first n pg s a ha)

/-- info: 'Foam.Bridges.the_mended_page_has_no_holes' does not depend on any axioms -/
#guard_msgs in #print axioms the_mended_page_has_no_holes

/-- info: 'Foam.Bridges.the_mended_page_answers_alike' does not depend on any axioms -/
#guard_msgs in #print axioms the_mended_page_answers_alike

/-- info: 'Foam.Bridges.mending_rests' does not depend on any axioms -/
#guard_msgs in #print axioms mending_rests

/-- info: 'Foam.Bridges.a_whole_page_mends_to_itself' does not depend on any axioms -/
#guard_msgs in #print axioms a_whole_page_mends_to_itself

structure NetHom (M N : Net) where
  onPage : M.Page → N.Page
  onSeat : M.Seat → N.Seat
  onAns : M.Ans → N.Ans
  keeps_the_page : ∀ pg s a, M.read? pg s = some a →
    N.read? (onPage pg) (onSeat s) = some (onAns a)
  keeps_the_mend : ∀ pg s, M.read? pg s = none →
    answer N (onPage pg) (onSeat s) = onAns (M.mend s)

theorem a_metaphor_carries_the_answer {M N : Net} (f : NetHom M N)
    (pg : M.Page) (s : M.Seat) :
    answer N (f.onPage pg) (f.onSeat s) = f.onAns (answer M pg s) := by
  cases h : M.read? pg s with
  | some a =>
      rw [the_page_speaks_first N _ _ _ (f.keeps_the_page pg s a h),
          the_page_speaks_first M pg s a h]
  | none =>
      rw [f.keeps_the_mend pg s h, the_mend_speaks_at_the_hole M pg s h]

def NetHom.id (M : Net) : NetHom M M where
  onPage := fun pg => pg
  onSeat := fun s => s
  onAns := fun a => a
  keeps_the_page := fun _ _ _ h => h
  keeps_the_mend := fun pg s h => the_mend_speaks_at_the_hole M pg s h

def NetHom.comp {M N U : Net} (g : NetHom N U) (f : NetHom M N) : NetHom M U where
  onPage := fun pg => g.onPage (f.onPage pg)
  onSeat := fun s => g.onSeat (f.onSeat s)
  onAns := fun a => g.onAns (f.onAns a)
  keeps_the_page := fun pg s a h => g.keeps_the_page _ _ _ (f.keeps_the_page pg s a h)
  keeps_the_mend := fun pg s h => by
    rw [a_metaphor_carries_the_answer g (f.onPage pg) (f.onSeat s),
        f.keeps_the_mend pg s h]

theorem nets_compose {M N U V : Net} (h : NetHom U V) (g : NetHom N U) (f : NetHom M N) :
    (h.comp g).comp f = h.comp (g.comp f)
      ∧ (NetHom.id N).comp f = f
      ∧ f.comp (NetHom.id M) = f :=
  ⟨rfl, rfl, rfl⟩

def stageOf (n : Net) : Stage where
  State := n.Page
  Probe := n.Seat
  Ans := n.Ans
  obs := answer n

def NetHom.staged {M N : Net} (f : NetHom M N) : StageHom (stageOf M) (stageOf N) where
  onState := f.onPage
  onProbe := f.onSeat
  onAns := f.onAns
  commutes := fun pg s => a_metaphor_carries_the_answer f pg s

theorem staging_respects_the_category {M N U : Net} (g : NetHom N U) (f : NetHom M N) :
    (NetHom.id M).staged = StageHom.id (stageOf M)
      ∧ (g.comp f).staged = g.staged.comp f.staged :=
  ⟨rfl, rfl⟩

def the_mending (n : Net) : NetHom n (mended n) where
  onPage := fun pg => pg
  onSeat := fun s => s
  onAns := fun a => a
  keeps_the_page := fun pg s a h => congrArg some (the_page_speaks_first n pg s a h)
  keeps_the_mend := fun pg s h => the_mend_speaks_at_the_hole n pg s h

theorem the_mending_writes_the_page (n : Net) :
    Whole (mended n)
      ∧ ∀ pg s, answer (mended n) pg s = (the_mending n).onAns (answer n pg s) :=
  ⟨the_mended_page_has_no_holes n, fun pg s => a_metaphor_carries_the_answer (the_mending n) pg s⟩

/-- info: 'Foam.Bridges.a_metaphor_carries_the_answer' does not depend on any axioms -/
#guard_msgs in #print axioms a_metaphor_carries_the_answer

/-- info: 'Foam.Bridges.nets_compose' does not depend on any axioms -/
#guard_msgs in #print axioms nets_compose

/-- info: 'Foam.Bridges.staging_respects_the_category' does not depend on any axioms -/
#guard_msgs in #print axioms staging_respects_the_category

/-- info: 'Foam.Bridges.the_mending_writes_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_mending_writes_the_page

inductive Pencil where
  | level : Pencil
  | plumb : Pencil
  | slant : Pencil

def Rail : Type := Pencil × Bool

def Mark : Type := Sum (Bool × Bool) Pencil

def braid : Bool → Bool → Bool
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false

theorem braid_cancels_right : ∀ (b c : Bool), braid (braid b c) c = b
  | false, false => rfl
  | false, true => rfl
  | true, false => rfl
  | true, true => rfl

theorem braid_pins : ∀ (x a b : Bool), braid x a = braid x b → a = b
  | false, false, false, _ => rfl
  | false, false, true, h => nomatch h
  | false, true, false, h => nomatch h
  | false, true, true, _ => rfl
  | true, false, false, _ => rfl
  | true, false, true, h => nomatch h
  | true, true, false, h => nomatch h
  | true, true, true, _ => rfl

def meetMark : Rail → Rail → Option Mark
  | (Pencil.plumb, _), (Pencil.plumb, _) => none
  | (Pencil.level, _), (Pencil.level, _) => none
  | (Pencil.slant, _), (Pencil.slant, _) => none
  | (Pencil.plumb, a), (Pencil.level, b) => some (Sum.inl (a, b))
  | (Pencil.level, b), (Pencil.plumb, a) => some (Sum.inl (a, b))
  | (Pencil.plumb, a), (Pencil.slant, c) => some (Sum.inl (a, braid a c))
  | (Pencil.slant, c), (Pencil.plumb, a) => some (Sum.inl (a, braid a c))
  | (Pencil.level, b), (Pencil.slant, c) => some (Sum.inl (braid b c, b))
  | (Pencil.slant, c), (Pencil.level, b) => some (Sum.inl (braid b c, b))

def planeNet : Net where
  Page := Unit
  Seat := Rail × Rail
  Ans := Mark
  read? := fun _ s => meetMark s.1 s.2
  mend := fun s => Sum.inr s.1.1

def Rides : Mark → Rail → Prop
  | Sum.inl (x, _), (Pencil.plumb, c) => x = c
  | Sum.inl (_, y), (Pencil.level, c) => y = c
  | Sum.inl (x, y), (Pencil.slant, c) => y = braid x c
  | Sum.inr d, (e, _) => d = e

theorem the_answer_rides_both_rails : ∀ (r₁ r₂ : Rail),
    Rides (answer planeNet () (r₁, r₂)) r₁ ∧ Rides (answer planeNet () (r₁, r₂)) r₂
  | (Pencil.plumb, _), (Pencil.plumb, _) => ⟨rfl, rfl⟩
  | (Pencil.level, _), (Pencil.level, _) => ⟨rfl, rfl⟩
  | (Pencil.slant, _), (Pencil.slant, _) => ⟨rfl, rfl⟩
  | (Pencil.plumb, _), (Pencil.level, _) => ⟨rfl, rfl⟩
  | (Pencil.level, _), (Pencil.plumb, _) => ⟨rfl, rfl⟩
  | (Pencil.plumb, _), (Pencil.slant, _) => ⟨rfl, rfl⟩
  | (Pencil.slant, _), (Pencil.plumb, _) => ⟨rfl, rfl⟩
  | (Pencil.level, b), (Pencil.slant, c) => ⟨rfl, (braid_cancels_right b c).symm⟩
  | (Pencil.slant, c), (Pencil.level, b) => ⟨(braid_cancels_right b c).symm, rfl⟩

theorem two_rails_pin_one_mark : ∀ (r₁ r₂ : Rail) (p : Mark), r₁ ≠ r₂ →
    Rides p r₁ → Rides p r₂ → p = answer planeNet () (r₁, r₂)
  | (Pencil.plumb, _), (Pencil.plumb, _), Sum.inl (_, _), hne, h1, h2 =>
      absurd (congrArg (fun t => (Pencil.plumb, t)) (h1.symm.trans h2)) hne
  | (Pencil.plumb, _), (Pencil.plumb, _), Sum.inr _, _, h1, _ => congrArg Sum.inr h1
  | (Pencil.level, _), (Pencil.level, _), Sum.inl (_, _), hne, h1, h2 =>
      absurd (congrArg (fun t => (Pencil.level, t)) (h1.symm.trans h2)) hne
  | (Pencil.level, _), (Pencil.level, _), Sum.inr _, _, h1, _ => congrArg Sum.inr h1
  | (Pencil.slant, a), (Pencil.slant, b), Sum.inl (x, _), hne, h1, h2 =>
      absurd (congrArg (fun t => (Pencil.slant, t))
        (braid_pins x a b (h1.symm.trans h2))) hne
  | (Pencil.slant, _), (Pencil.slant, _), Sum.inr _, _, h1, _ => congrArg Sum.inr h1
  | (Pencil.plumb, a), (Pencil.level, b), Sum.inl (x, y), _, h1, h2 => by
      show Sum.inl (x, y) = Sum.inl (a, b)
      rw [h1, h2]
  | (Pencil.plumb, _), (Pencil.level, _), Sum.inr _, _, h1, h2 =>
      nomatch h1.symm.trans h2
  | (Pencil.level, b), (Pencil.plumb, a), Sum.inl (x, y), _, h1, h2 => by
      show Sum.inl (x, y) = Sum.inl (a, b)
      rw [h1, h2]
  | (Pencil.level, _), (Pencil.plumb, _), Sum.inr _, _, h1, h2 =>
      nomatch h1.symm.trans h2
  | (Pencil.plumb, a), (Pencil.slant, c), Sum.inl (x, y), _, h1, h2 => by
      show Sum.inl (x, y) = Sum.inl (a, braid a c)
      rw [h1] at h2
      rw [h1, h2]
  | (Pencil.plumb, _), (Pencil.slant, _), Sum.inr _, _, h1, h2 =>
      nomatch h1.symm.trans h2
  | (Pencil.slant, c), (Pencil.plumb, a), Sum.inl (x, y), _, h1, h2 => by
      show Sum.inl (x, y) = Sum.inl (a, braid a c)
      rw [h2] at h1
      rw [h2, h1]
  | (Pencil.slant, _), (Pencil.plumb, _), Sum.inr _, _, h1, h2 =>
      nomatch h1.symm.trans h2
  | (Pencil.level, b), (Pencil.slant, c), Sum.inl (x, y), _, h1, h2 => by
      show Sum.inl (x, y) = Sum.inl (braid b c, b)
      have hx : x = braid b c := by
        rw [h1.symm.trans h2]
        exact (braid_cancels_right x c).symm
      rw [h1, hx]
  | (Pencil.level, _), (Pencil.slant, _), Sum.inr _, _, h1, h2 =>
      nomatch h1.symm.trans h2
  | (Pencil.slant, c), (Pencil.level, b), Sum.inl (x, y), _, h1, h2 => by
      show Sum.inl (x, y) = Sum.inl (braid b c, b)
      have hx : x = braid b c := by
        rw [h2.symm.trans h1]
        exact (braid_cancels_right x c).symm
      rw [h2, hx]
  | (Pencil.slant, _), (Pencil.level, _), Sum.inr _, _, h1, h2 =>
      nomatch h1.symm.trans h2

theorem parallel_rails_consult : ∀ (r₁ r₂ : Rail),
    Consults planeNet () (r₁, r₂) ↔ r₁.1 = r₂.1
  | (Pencil.plumb, _), (Pencil.plumb, _) => ⟨fun _ => rfl, fun _ => rfl⟩
  | (Pencil.level, _), (Pencil.level, _) => ⟨fun _ => rfl, fun _ => rfl⟩
  | (Pencil.slant, _), (Pencil.slant, _) => ⟨fun _ => rfl, fun _ => rfl⟩
  | (Pencil.plumb, _), (Pencil.level, _) => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | (Pencil.level, _), (Pencil.plumb, _) => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | (Pencil.plumb, _), (Pencil.slant, _) => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | (Pencil.slant, _), (Pencil.plumb, _) => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | (Pencil.level, _), (Pencil.slant, _) => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | (Pencil.slant, _), (Pencil.level, _) => ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem the_mend_reads_the_pencil (r₁ r₂ : Rail) (h : r₁.1 = r₂.1) :
    planeNet.mend (r₁, r₂) = planeNet.mend (r₂, r₁) :=
  congrArg Sum.inr h

theorem the_completed_plane_meets_everywhere : Whole (mended planeNet) :=
  the_mended_page_has_no_holes planeNet

/-- info: 'Foam.Bridges.braid_cancels_right' does not depend on any axioms -/
#guard_msgs in #print axioms braid_cancels_right

/-- info: 'Foam.Bridges.the_answer_rides_both_rails' does not depend on any axioms -/
#guard_msgs in #print axioms the_answer_rides_both_rails

/-- info: 'Foam.Bridges.two_rails_pin_one_mark' does not depend on any axioms -/
#guard_msgs in #print axioms two_rails_pin_one_mark

/-- info: 'Foam.Bridges.parallel_rails_consult' does not depend on any axioms -/
#guard_msgs in #print axioms parallel_rails_consult

/-- info: 'Foam.Bridges.the_mend_reads_the_pencil' does not depend on any axioms -/
#guard_msgs in #print axioms the_mend_reads_the_pencil

/-- info: 'Foam.Bridges.the_completed_plane_meets_everywhere' does not depend on any axioms -/
#guard_msgs in #print axioms the_completed_plane_meets_everywhere

end Foam.Bridges
