import Foam.Int
import Foam.Ledger
import Foam.Seat.Sort

namespace Foam.Counter

inductive Page where
  | blank : Page
  | click : Page → Page → Page

def Page.census : Page → Nat
  | .blank => 0
  | .click kids sibs => 1 + kids.census + sibs.census

inductive Crumb where
  | intoKids : Page → Crumb
  | intoSibs : Page → Crumb

def Crumb.census : Crumb → Nat
  | .intoKids sibs => 1 + sibs.census
  | .intoSibs kids => 1 + kids.census

def trailCensus : List Crumb → Nat
  | [] => 0
  | c :: cs => c.census + trailCensus cs

structure Cursor where
  focus : Page
  trail : List Crumb

def plug : Page → List Crumb → Page
  | f, [] => f
  | f, .intoKids sibs :: cs => plug (.click f sibs) cs
  | f, .intoSibs kids :: cs => plug (.click kids f) cs

def Cursor.page (c : Cursor) : Page := plug c.focus c.trail

def Page.entry (p : Page) : Cursor := ⟨p, []⟩

inductive Tool where
  | ascend : Tool
  | enter : Tool
  | advance : Tool
deriving DecidableEq

def toolbox : List Tool := [.ascend, .enter, .advance]

def Tool.use : Tool → Cursor → Option Cursor
  | .ascend, ⟨f, .intoKids sibs :: cs⟩ => some ⟨.click f sibs, cs⟩
  | .ascend, ⟨f, .intoSibs kids :: cs⟩ => some ⟨.click kids f, cs⟩
  | .ascend, ⟨_, []⟩ => none
  | .enter, ⟨.click kids sibs, cs⟩ => some ⟨kids, .intoKids sibs :: cs⟩
  | .enter, ⟨.blank, _⟩ => none
  | .advance, ⟨.click kids sibs, cs⟩ => some ⟨sibs, .intoSibs kids :: cs⟩
  | .advance, ⟨.blank, _⟩ => none

def steps : List Tool → Cursor → Option Cursor
  | [], c => some c
  | t :: ts, c => (t.use c).bind (steps ts)

def exit : List Crumb → List Tool
  | [] => []
  | _ :: cs => .ascend :: exit cs

def seatsFrom : Page → List Crumb → List Cursor
  | .blank, _ => []
  | .click kids sibs, cs =>
      ⟨.click kids sibs, cs⟩ ::
        (seatsFrom kids (.intoKids sibs :: cs) ++ seatsFrom sibs (.intoSibs kids :: cs))

def Page.seats (p : Page) : List Cursor := seatsFrom p []

theorem the_flow_starts_whole (p : Page) :
    p.entry.focus = p ∧ trailCensus p.entry.trail = 0 := ⟨rfl, rfl⟩

theorem the_toolbox_holds_three : toolbox.length = 3 := rfl

theorem every_tool_is_in_the_toolbox (t : Tool) : t ∈ toolbox := by
  cases t with
  | ascend => exact .head _
  | enter => exact .tail _ (.head _)
  | advance => exact .tail _ (.tail _ (.head _))

theorem the_ledger_holds_each_tool_once (t : Tool) : Ledger.freq toolbox t = 1 := by
  cases t <;> rfl

theorem the_entrance_lists_the_loss (kids sibs : Page) (cs : List Crumb) :
    Tool.enter.use ⟨.click kids sibs, cs⟩ = some ⟨kids, .intoKids sibs :: cs⟩ := rfl

theorem the_advance_lists_the_loss (kids sibs : Page) (cs : List Crumb) :
    Tool.advance.use ⟨.click kids sibs, cs⟩ = some ⟨sibs, .intoSibs kids :: cs⟩ := rfl

theorem every_entrance_writes_its_exit :
    ∀ (c c' : Cursor), Tool.enter.use c = some c' → Tool.ascend.use c' = some c
  | ⟨.click kids sibs, cs⟩, c', h => by
      have h : (some ⟨kids, .intoKids sibs :: cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | ⟨.blank, _⟩, _, h => nomatch h

theorem every_advance_writes_its_exit :
    ∀ (c c' : Cursor), Tool.advance.use c = some c' → Tool.ascend.use c' = some c
  | ⟨.click kids sibs, cs⟩, c', h => by
      have h : (some ⟨sibs, .intoSibs kids :: cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | ⟨.blank, _⟩, _, h => nomatch h

theorem the_trail_remembers_the_way_down :
    ∀ (c c' : Cursor), Tool.ascend.use c = some c' → ∃ t : Tool, t.use c' = some c
  | ⟨f, .intoKids sibs :: cs⟩, c', h => by
      have h : (some ⟨.click f sibs, cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      exact ⟨.enter, rfl⟩
  | ⟨f, .intoSibs kids :: cs⟩, c', h => by
      have h : (some ⟨.click kids f, cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      exact ⟨.advance, rfl⟩
  | ⟨_, []⟩, _, h => nomatch h

theorem the_entry_affords_no_ascent (p : Page) : Tool.ascend.use p.entry = none := rfl

theorem a_blank_affords_no_new_ground (cs : List Crumb) :
    Tool.enter.use ⟨.blank, cs⟩ = none ∧ Tool.advance.use ⟨.blank, cs⟩ = none :=
  ⟨rfl, rfl⟩

theorem the_ascent_reads_the_trail (f : Page) (tr : List Crumb) :
    (∃ c', Tool.ascend.use ⟨f, tr⟩ = some c') ↔ tr ≠ [] := by
  cases tr with
  | nil =>
    constructor
    · intro ⟨_, hc⟩
      exact nomatch hc
    · intro hne
      exact absurd rfl hne
  | cons crumb cs =>
    constructor
    · intro _ heq
      exact nomatch heq
    · intro _
      cases crumb with
      | intoKids sibs => exact ⟨_, rfl⟩
      | intoSibs kids => exact ⟨_, rfl⟩

theorem the_entrance_reads_the_focus (f : Page) (tr : List Crumb) :
    (∃ c', Tool.enter.use ⟨f, tr⟩ = some c') ↔ ∃ kids sibs, f = .click kids sibs := by
  cases f with
  | blank =>
    constructor
    · intro ⟨_, hc⟩
      exact nomatch hc
    · intro ⟨_, _, hf⟩
      exact nomatch hf
  | click kids sibs =>
    constructor
    · intro _
      exact ⟨kids, sibs, rfl⟩
    · intro _
      exact ⟨_, rfl⟩

theorem the_advance_reads_the_focus (f : Page) (tr : List Crumb) :
    (∃ c', Tool.advance.use ⟨f, tr⟩ = some c') ↔ ∃ kids sibs, f = .click kids sibs := by
  cases f with
  | blank =>
    constructor
    · intro ⟨_, hc⟩
      exact nomatch hc
    · intro ⟨_, _, hf⟩
      exact nomatch hf
  | click kids sibs =>
    constructor
    · intro _
      exact ⟨kids, sibs, rfl⟩
    · intro _
      exact ⟨_, rfl⟩

theorem the_page_survives_every_use :
    ∀ (t : Tool) (c c' : Cursor), t.use c = some c' → c'.page = c.page
  | .ascend, ⟨f, .intoKids sibs :: cs⟩, c', h => by
      have h : (some ⟨.click f sibs, cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | .ascend, ⟨f, .intoSibs kids :: cs⟩, c', h => by
      have h : (some ⟨.click kids f, cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | .ascend, ⟨_, []⟩, _, h => nomatch h
  | .enter, ⟨.click kids sibs, cs⟩, c', h => by
      have h : (some ⟨kids, .intoKids sibs :: cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | .enter, ⟨.blank, _⟩, _, h => nomatch h
  | .advance, ⟨.click kids sibs, cs⟩, c', h => by
      have h : (some ⟨sibs, .intoSibs kids :: cs⟩ : Option Cursor) = some c' := h
      injection h with h
      subst h
      rfl
  | .advance, ⟨.blank, _⟩, _, h => nomatch h

theorem the_census_splits_at_the_seat (f : Page) (cs : List Crumb) :
    (plug f cs).census = f.census + trailCensus cs := by
  induction cs generalizing f with
  | nil => rfl
  | cons crumb cs ih =>
    cases crumb with
    | intoKids sibs =>
      show (plug (.click f sibs) cs).census
        = f.census + ((1 + sibs.census) + trailCensus cs)
      rw [ih]
      show ((1 + f.census) + sibs.census) + trailCensus cs
        = f.census + ((1 + sibs.census) + trailCensus cs)
      rw [Nat.add_comm 1 f.census, Nat.add_assoc f.census 1 sibs.census,
          Nat.add_assoc f.census (1 + sibs.census) (trailCensus cs)]
    | intoSibs kids =>
      show (plug (.click kids f) cs).census
        = f.census + ((1 + kids.census) + trailCensus cs)
      rw [ih]
      show ((1 + kids.census) + f.census) + trailCensus cs
        = f.census + ((1 + kids.census) + trailCensus cs)
      rw [Nat.add_comm (1 + kids.census) f.census,
          Nat.add_assoc f.census (1 + kids.census) (trailCensus cs)]

theorem the_flow_is_conserved (t : Tool) (c c' : Cursor) (h : t.use c = some c') :
    c'.focus.census + trailCensus c'.trail = c.focus.census + trailCensus c.trail := by
  rw [← the_census_splits_at_the_seat c'.focus c'.trail,
      ← the_census_splits_at_the_seat c.focus c.trail]
  exact congrArg Page.census (the_page_survives_every_use t c c' h)

theorem the_page_survives_every_walk :
    ∀ (ts : List Tool) (c c' : Cursor), steps ts c = some c' → c'.page = c.page
  | [], _, c', h => by
      have h : some _ = some c' := h
      injection h with h
      subst h
      rfl
  | t :: ts, c, c', h => by
      have h' : (t.use c).bind (steps ts) = some c' := h
      cases ht : t.use c with
      | none =>
        rw [ht] at h'
        exact nomatch h'
      | some c₁ =>
        rw [ht] at h'
        exact (the_page_survives_every_walk ts c₁ c' h').trans
          (the_page_survives_every_use t c c₁ ht)

theorem exit_walks_home :
    ∀ (f : Page) (cs : List Crumb), steps (exit cs) ⟨f, cs⟩ = some ⟨plug f cs, []⟩
  | _, [] => rfl
  | f, .intoKids sibs :: cs => exit_walks_home (.click f sibs) cs
  | f, .intoSibs kids :: cs => exit_walks_home (.click kids f) cs

theorem the_exit_is_already_written (c : Cursor) :
    steps (exit c.trail) c = some ⟨c.page, []⟩ :=
  exit_walks_home c.focus c.trail

theorem the_exit_costs_the_trail (cs : List Crumb) : (exit cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons _ cs ih => exact congrArg Nat.succ ih

theorem seatsFrom_length :
    ∀ (p : Page) (cs : List Crumb), (seatsFrom p cs).length = p.census
  | .blank, _ => rfl
  | .click kids sibs, cs => by
      show ((seatsFrom kids (.intoKids sibs :: cs)
              ++ seatsFrom sibs (.intoSibs kids :: cs)).length) + 1
        = (1 + kids.census) + sibs.census
      rw [length_append, seatsFrom_length kids (.intoKids sibs :: cs),
          seatsFrom_length sibs (.intoSibs kids :: cs),
          Nat.add_comm (kids.census + sibs.census) 1,
          ← Nat.add_assoc 1 kids.census sibs.census]

theorem the_page_seats_its_census (p : Page) : p.seats.length = p.census :=
  seatsFrom_length p []

theorem mem_append_split {A : Type} {a : A} :
    ∀ (xs ys : List A), a ∈ xs ++ ys → a ∈ xs ∨ a ∈ ys
  | [], _, h => Or.inr h
  | x :: xs, ys, h => by
      have h : a ∈ x :: (xs ++ ys) := h
      cases h with
      | head => exact Or.inl (.head _)
      | tail _ h' =>
        cases mem_append_split xs ys h' with
        | inl hk => exact Or.inl (.tail _ hk)
        | inr hs => exact Or.inr hs

theorem seatsFrom_page :
    ∀ (p : Page) (cs : List Crumb) (c : Cursor), c ∈ seatsFrom p cs → c.page = plug p cs
  | .blank, _, _, h => nomatch h
  | .click kids sibs, cs, c, h => by
      have h : c ∈ (⟨.click kids sibs, cs⟩ : Cursor) ::
          (seatsFrom kids (.intoKids sibs :: cs) ++ seatsFrom sibs (.intoSibs kids :: cs)) := h
      cases h with
      | head => rfl
      | tail _ h' =>
        cases mem_append_split _ _ h' with
        | inl hk => exact seatsFrom_page kids (.intoKids sibs :: cs) c hk
        | inr hs => exact seatsFrom_page sibs (.intoSibs kids :: cs) c hs

theorem every_seat_relays_the_whole (p : Page) (c : Cursor) (h : c ∈ p.seats) :
    c.page = p :=
  seatsFrom_page p [] c h

theorem reach_through :
    ∀ (f : Page) (cs : List Crumb) (ts : List Tool) (c : Cursor),
      steps ts ⟨f, cs⟩ = some c → ∃ us : List Tool, steps us ⟨plug f cs, []⟩ = some c
  | _, [], ts, _, h => ⟨ts, h⟩
  | f, .intoKids sibs :: cs, ts, c, h =>
      reach_through (.click f sibs) cs (.enter :: ts) c h
  | f, .intoSibs kids :: cs, ts, c, h =>
      reach_through (.click kids f) cs (.advance :: ts) c h

theorem every_seat_over_the_page_answers (c : Cursor) :
    ∃ ts : List Tool, steps ts c.page.entry = some c :=
  reach_through c.focus c.trail [] c rfl

theorem every_seat_answers_the_entry (p : Page) (c : Cursor) (h : c ∈ p.seats) :
    ∃ ts : List Tool, steps ts p.entry = some c := by
  obtain ⟨ts, hts⟩ := every_seat_over_the_page_answers c
  rw [every_seat_relays_the_whole p c h] at hts
  exact ⟨ts, hts⟩

theorem steps_append :
    ∀ (ts us : List Tool) (c : Cursor),
      steps (ts ++ us) c = (steps ts c).bind (steps us)
  | [], _, _ => rfl
  | t :: ts, us, c => by
      show (t.use c).bind (steps (ts ++ us)) = ((t.use c).bind (steps ts)).bind (steps us)
      cases t.use c with
      | none => rfl
      | some c₁ => exact steps_append ts us c₁

theorem any_two_seats_over_one_page_meet (c c' : Cursor) (h : c.page = c'.page) :
    ∃ ts : List Tool, steps ts c = some c' := by
  obtain ⟨us, hus⟩ := every_seat_over_the_page_answers c'
  refine ⟨exit c.trail ++ us, ?_⟩
  rw [steps_append, the_exit_is_already_written]
  show steps us ⟨c.page, []⟩ = some c'
  rw [h]
  exact hus

theorem the_walks_read_exactly_the_page (c c' : Cursor) :
    (∃ ts : List Tool, steps ts c = some c') ↔ c.page = c'.page := by
  constructor
  · intro ⟨ts, hts⟩
    exact (the_page_survives_every_walk ts c c' hts).symm
  · exact any_two_seats_over_one_page_meet c c'

/-- info: 'Foam.Counter.the_flow_starts_whole' does not depend on any axioms -/
#guard_msgs in #print axioms the_flow_starts_whole

/-- info: 'Foam.Counter.the_toolbox_holds_three' does not depend on any axioms -/
#guard_msgs in #print axioms the_toolbox_holds_three

/-- info: 'Foam.Counter.every_tool_is_in_the_toolbox' does not depend on any axioms -/
#guard_msgs in #print axioms every_tool_is_in_the_toolbox

/-- info: 'Foam.Counter.the_ledger_holds_each_tool_once' does not depend on any axioms -/
#guard_msgs in #print axioms the_ledger_holds_each_tool_once

/-- info: 'Foam.Counter.the_entrance_lists_the_loss' does not depend on any axioms -/
#guard_msgs in #print axioms the_entrance_lists_the_loss

/-- info: 'Foam.Counter.the_advance_lists_the_loss' does not depend on any axioms -/
#guard_msgs in #print axioms the_advance_lists_the_loss

/-- info: 'Foam.Counter.every_entrance_writes_its_exit' does not depend on any axioms -/
#guard_msgs in #print axioms every_entrance_writes_its_exit

/-- info: 'Foam.Counter.every_advance_writes_its_exit' does not depend on any axioms -/
#guard_msgs in #print axioms every_advance_writes_its_exit

/-- info: 'Foam.Counter.the_trail_remembers_the_way_down' does not depend on any axioms -/
#guard_msgs in #print axioms the_trail_remembers_the_way_down

/-- info: 'Foam.Counter.the_entry_affords_no_ascent' does not depend on any axioms -/
#guard_msgs in #print axioms the_entry_affords_no_ascent

/-- info: 'Foam.Counter.a_blank_affords_no_new_ground' does not depend on any axioms -/
#guard_msgs in #print axioms a_blank_affords_no_new_ground

/-- info: 'Foam.Counter.the_ascent_reads_the_trail' does not depend on any axioms -/
#guard_msgs in #print axioms the_ascent_reads_the_trail

/-- info: 'Foam.Counter.the_entrance_reads_the_focus' does not depend on any axioms -/
#guard_msgs in #print axioms the_entrance_reads_the_focus

/-- info: 'Foam.Counter.the_advance_reads_the_focus' does not depend on any axioms -/
#guard_msgs in #print axioms the_advance_reads_the_focus

/-- info: 'Foam.Counter.the_page_survives_every_use' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_survives_every_use

/-- info: 'Foam.Counter.the_census_splits_at_the_seat' does not depend on any axioms -/
#guard_msgs in #print axioms the_census_splits_at_the_seat

/-- info: 'Foam.Counter.the_flow_is_conserved' does not depend on any axioms -/
#guard_msgs in #print axioms the_flow_is_conserved

/-- info: 'Foam.Counter.the_page_survives_every_walk' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_survives_every_walk

/-- info: 'Foam.Counter.exit_walks_home' does not depend on any axioms -/
#guard_msgs in #print axioms exit_walks_home

/-- info: 'Foam.Counter.the_exit_is_already_written' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_is_already_written

/-- info: 'Foam.Counter.the_exit_costs_the_trail' does not depend on any axioms -/
#guard_msgs in #print axioms the_exit_costs_the_trail

/-- info: 'Foam.Counter.seatsFrom_length' does not depend on any axioms -/
#guard_msgs in #print axioms seatsFrom_length

/-- info: 'Foam.Counter.the_page_seats_its_census' does not depend on any axioms -/
#guard_msgs in #print axioms the_page_seats_its_census

/-- info: 'Foam.Counter.mem_append_split' does not depend on any axioms -/
#guard_msgs in #print axioms mem_append_split

/-- info: 'Foam.Counter.seatsFrom_page' does not depend on any axioms -/
#guard_msgs in #print axioms seatsFrom_page

/-- info: 'Foam.Counter.every_seat_relays_the_whole' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_relays_the_whole

/-- info: 'Foam.Counter.reach_through' does not depend on any axioms -/
#guard_msgs in #print axioms reach_through

/-- info: 'Foam.Counter.every_seat_over_the_page_answers' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_over_the_page_answers

/-- info: 'Foam.Counter.every_seat_answers_the_entry' does not depend on any axioms -/
#guard_msgs in #print axioms every_seat_answers_the_entry

/-- info: 'Foam.Counter.steps_append' does not depend on any axioms -/
#guard_msgs in #print axioms steps_append

/-- info: 'Foam.Counter.any_two_seats_over_one_page_meet' does not depend on any axioms -/
#guard_msgs in #print axioms any_two_seats_over_one_page_meet

/-- info: 'Foam.Counter.the_walks_read_exactly_the_page' does not depend on any axioms -/
#guard_msgs in #print axioms the_walks_read_exactly_the_page

end Foam.Counter
