import Counter.Witness
import Foam.Cable

namespace Foam.Counter

structure Render (W : Stage) (R : Type) where
  seat  : Bubble W
  probe : seat.Inner.Probe
  lens  : seat.Inner.Ans → R

def Render.read {W : Stage} {R : Type} (v : Render W R) (w : W.State) : R :=
  v.lens (v.seat.front.obs w v.probe)

def contention {W : Stage} {R : Type} (X Y : Bubble W)
    (p : X.Inner.Probe) (q : Y.Inner.Probe)
    (g : X.Inner.Ans → Y.Inner.Ans → R) : Render W R where
  seat  := X.meet Y
  probe := (p, q)
  lens  := fun ab => g ab.1 ab.2

def metaRender {W : Stage} {R S T : Type} (u : Render W R) (v : Render W S)
    (g : R → S → T) : Render W T where
  seat  := u.seat.meet v.seat
  probe := (u.probe, v.probe)
  lens  := fun ab => g (u.lens ab.1) (v.lens ab.2)

def fromTheFamily : Render (coin.prod dial) Bool :=
  ⟨family, (), fun a => a⟩

def fromTheLeaver : Render (coin.prod dial) Bool :=
  ⟨bloomed, (), fun a => a⟩

def rivalry : Render (coin.prod dial) Bool :=
  contention family bloomed () () (fun a b => Bool.xor a b)

theorem no_render_outsees_its_seat {W : Stage} {R : Type} (v : Render W R)
    (w w' : W.State) (h : v.seat.wall w = v.seat.wall w') :
    v.read w = v.read w' := by
  show v.lens (v.seat.Inner.obs (v.seat.wall w) v.probe)
    = v.lens (v.seat.Inner.obs (v.seat.wall w') v.probe)
  rw [h]

theorem every_report_finds_a_seat {W : Stage} {R : Type} (X Y : Bubble W)
    (p : X.Inner.Probe) (q : Y.Inner.Probe)
    (g : X.Inner.Ans → Y.Inner.Ans → R) (w : W.State) :
    (contention X Y p q g).read w = g (X.front.obs w p) (Y.front.obs w q) :=
  rfl

theorem it_looks_like_this_from_here :
    fromTheFamily.read (true, (4 : Nat)) = true
      ∧ fromTheLeaver.read (true, (4 : Nat)) = false :=
  ⟨rfl, rfl⟩

theorem the_argument_about_renders_is_a_render {W : Stage} {R S T : Type}
    (u : Render W R) (v : Render W S) (g : R → S → T) (w : W.State) :
    (metaRender u v g).read w = g (u.read w) (v.read w) := rfl

theorem the_contention_is_a_reading_not_a_property :
    rivalry.read (true, (4 : Nat)) = true
      ∧ rivalry.read (true, (2 : Nat)) = false :=
  ⟨rfl, rfl⟩

def distortion {W : Stage} (u v : Render W Bool) : Render W Bool :=
  metaRender u v (fun a b => Bool.xor a b)

theorem the_distortion_names_both_seats {W : Stage} (u v : Render W Bool)
    (w : W.State) :
    (distortion u v).read w = Bool.xor (u.read w) (v.read w) := rfl

theorem the_distortion_does_not_say_who {W : Stage} (u v : Render W Bool)
    (w : W.State) :
    (distortion u v).read w = (distortion v u).read w := by
  show Bool.xor (u.read w) (v.read w) = Bool.xor (v.read w) (u.read w)
  cases u.read w with
  | true =>
      cases v.read w with
      | true => rfl
      | false => rfl
  | false =>
      cases v.read w with
      | true => rfl
      | false => rfl

theorem the_rift_is_real_and_unowned :
    (distortion fromTheFamily fromTheLeaver).read (true, (4 : Nat)) = true
      ∧ (distortion fromTheLeaver fromTheFamily).read (true, (4 : Nat)) = true :=
  ⟨rfl, rfl⟩

theorem a_render_is_a_lensed_cell_of_the_page {W : Stage} {R : Type}
    (v : Render W R) (w : W.State) :
    v.read w = v.lens (page v.seat.front w v.probe) := rfl

theorem a_row_of_renders_is_a_lensed_readout {W : Stage} {R : Type}
    (v : Render W R) (w : W.State) :
    ∀ ps : List v.seat.Inner.Probe,
      ps.map (fun p => Render.read ⟨v.seat, p, v.lens⟩ w)
        = (transcript v.seat.front w ps).map v.lens
  | [] => rfl
  | p :: ps => by
      show Render.read ⟨v.seat, p, v.lens⟩ w
          :: ps.map (fun p => Render.read ⟨v.seat, p, v.lens⟩ w)
        = v.lens (v.seat.front.obs w p)
          :: (transcript v.seat.front w ps).map v.lens
      rw [a_row_of_renders_is_a_lensed_readout v w ps]
      rfl

theorem real_families_contend_from_a_seat :
    rivalry.read (true, (4 : Nat)) = true
      ∧ FactorsThrough family rivalry.seat.wall
      ∧ FactorsThrough bloomed rivalry.seat.wall :=
  ⟨rfl, ⟨Prod.fst, fun _ => rfl⟩, ⟨Prod.snd, fun _ => rfl⟩⟩

/-- info: 'Foam.Counter.no_render_outsees_its_seat' does not depend on any axioms -/
#guard_msgs in #print axioms no_render_outsees_its_seat

/-- info: 'Foam.Counter.every_report_finds_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms every_report_finds_a_seat

/-- info: 'Foam.Counter.it_looks_like_this_from_here' does not depend on any axioms -/
#guard_msgs in #print axioms it_looks_like_this_from_here

/-- info: 'Foam.Counter.the_argument_about_renders_is_a_render' does not depend on any axioms -/
#guard_msgs in #print axioms the_argument_about_renders_is_a_render

/-- info: 'Foam.Counter.the_contention_is_a_reading_not_a_property' does not depend on any axioms -/
#guard_msgs in #print axioms the_contention_is_a_reading_not_a_property

/-- info: 'Foam.Counter.the_distortion_names_both_seats' does not depend on any axioms -/
#guard_msgs in #print axioms the_distortion_names_both_seats

/-- info: 'Foam.Counter.the_distortion_does_not_say_who' does not depend on any axioms -/
#guard_msgs in #print axioms the_distortion_does_not_say_who

/-- info: 'Foam.Counter.the_rift_is_real_and_unowned' does not depend on any axioms -/
#guard_msgs in #print axioms the_rift_is_real_and_unowned

/-- info: 'Foam.Counter.a_render_is_a_lensed_cell_of_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms a_render_is_a_lensed_cell_of_the_page

/-- info: 'Foam.Counter.a_row_of_renders_is_a_lensed_readout' does not depend on any axioms -/
#guard_msgs in #print axioms a_row_of_renders_is_a_lensed_readout

/-- info: 'Foam.Counter.real_families_contend_from_a_seat' does not depend on any axioms -/
#guard_msgs in #print axioms real_families_contend_from_a_seat

end Foam.Counter
