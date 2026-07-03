import Counter.Contract
import Counter.Rhythm

namespace Foam.Counter

theorem the_legible_writes_nothing {H : Type} {q : Quiver H} {a b c : H}
    (p : Path q a b) (r : Path q b c) :
    (∀ e ∈ p.edges, e ∈ q) ∧ (p.comp r).edges = p.edges ++ r.edges :=
  ⟨report_within_model p, Path.edges_comp p r⟩

theorem only_surprise_extends_reach {H : Type} (q : Quiver H) (a b : H)
    (hfresh : (a, b) ∉ q) :
    (∀ (x y : H) (pth : Path q x y), (a, b) ∉ pth.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b) :=
  ⟨(illegible_report_is_discovery q a b hfresh).1,
   (illegible_report_is_discovery q a b hfresh).2⟩

theorem the_familiar_has_no_voice {A : Type} [DecidableEq A] (a : A) :
    spec [a, a, a, a] a = GInt.zero :=
  revisits_voiceless a

theorem no_dog {H : Type} (q : Quiver H) (a b : H) (hfresh : (a, b) ∉ q)
    {A : Type} [DecidableEq A] (x : A) :
    (∀ (s t : H) (pth : Path q s t), (a, b) ∉ pth.edges)
      ∧ Nonempty (Path (q.deposit (a, b)) a b)
      ∧ spec [x, x, x, x] x = GInt.zero :=
  ⟨(illegible_report_is_discovery q a b hfresh).1,
   (illegible_report_is_discovery q a b hfresh).2, revisits_voiceless x⟩

/-- info: 'Foam.Counter.the_legible_writes_nothing' does not depend on any axioms -/
#guard_msgs in #print axioms the_legible_writes_nothing

/-- info: 'Foam.Counter.only_surprise_extends_reach' does not depend on any axioms -/
#guard_msgs in #print axioms only_surprise_extends_reach

/-- info: 'Foam.Counter.the_familiar_has_no_voice' does not depend on any axioms -/
#guard_msgs in #print axioms the_familiar_has_no_voice

/-- info: 'Foam.Counter.no_dog' does not depend on any axioms -/
#guard_msgs in #print axioms no_dog

end Foam.Counter
