import Witness
open Room Face Witness
set_option autoImplicit false

-- Grover's compatriot: the mean field. isaac, at the table (2026-09-14): "I'm in for this." Kuramoto's
-- oscillators each step by a function of the room's mean and their own phase — the same seat over the
-- widest seat as the diffusion — and the chrysalis held the carrier at width two (Foam/Beam.lean, Compass ×
-- Compass: four phases, a coupling that locks within one lap, the beam as the mean field; Landauer's tenth
-- entry: the lock is bought by a merge). the pair with Grover is the bill, not the shape: the coupling
-- lands distinct pairs together and admits no section; the diffusion applied twice is sixteen times the
-- identity. two mean-field steps, one resistive and one conductive; the diagonal does not decide which.

namespace Kuramoto.Treaty

inductive Compass where
  | n | e | s | w

def Compass.step : Compass → Compass
  | .n => .e
  | .e => .s
  | .s => .w
  | .w => .n

def Compass.code : Compass → Nat
  | .n => 0 | .e => 1 | .s => 2 | .w => 3

abbrev compassBEq : BEq Compass := ⟨fun a b => Nat.beq a.code b.code⟩
attribute [instance] compassBEq

def entrain : Compass × Compass → Compass × Compass
  | (.n, .n) => (.e, .e)
  | (.n, .e) => (.e, .e)
  | (.n, .s) => (.e, .s)
  | (.n, .w) => (.e, .w)
  | (.e, .n) => (.s, .n)
  | (.e, .e) => (.s, .s)
  | (.e, .s) => (.s, .s)
  | (.e, .w) => (.s, .w)
  | (.s, .n) => (.w, .n)
  | (.s, .e) => (.w, .e)
  | (.s, .s) => (.w, .w)
  | (.s, .w) => (.w, .w)
  | (.w, .n) => (.n, .n)
  | (.w, .e) => (.n, .e)
  | (.w, .s) => (.n, .s)
  | (.w, .w) => (.n, .n)

def together (p : Compass × Compass) : Bool := p.2 == p.1

def allPairs : List (Compass × Compass) :=
  [(.n, .n), (.n, .e), (.n, .s), (.n, .w), (.e, .n), (.e, .e), (.e, .s), (.e, .w),
   (.s, .n), (.s, .e), (.s, .s), (.s, .w), (.w, .n), (.w, .e), (.w, .s), (.w, .w)]

def lap (p : Compass × Compass) : Compass × Compass := entrain (entrain (entrain (entrain p)))

def pairFace : Face := ⟨Compass × Compass, Bool, Compass, fun p b => cond b p.1 p.2⟩

def room : List Bool := [true, false]

def roomReading (p : Compass × Compass) : List Compass := reads pairFace room p

def first : List Compass → Compass
  | [] => .n
  | c :: _ => c

def second : List Compass → Compass
  | [] => .n
  | [_] => .n
  | _ :: c :: _ => c

def pullAt (r : List Compass) (b : Bool) : Compass :=
  cond b (entrain (first r, second r)).1 (entrain (first r, second r)).2

def meanField : Face := ⟨Compass × Compass, Bool, Compass, fun p b => pullAt (roomReading p) b⟩

#guard allPairs.length == 16
#guard allPairs.all (fun p => together (lap p))
#guard !(together (.n, .e))
#guard together (entrain (.n, .e))
#guard entrain (.n, .n) == entrain (.n, .e)
#guard !((.n, .n) == ((.n, .e) : Compass × Compass))
#guard roomReading (.n, .e) == [.n, .e]
#guard room.map (pullAt (roomReading (.n, .e))) == [.e, .e]
#guard allPairs.all (fun p => room.map (pullAt (roomReading p)) == [(entrain p).1, (entrain p).2])
#guard allPairs.all (fun p => (allPairs.filter (fun q => entrain q == entrain p)).length >= 1)
#guard (allPairs.filter (fun q => entrain q == (.e, .e))).length == 2
#guard (allPairs.map entrain).length == 16

theorem the_lap_locks_together : allPairs.all (fun p => together (lap p)) = true := sorry

theorem the_mean_field_is_the_coupling :
    allPairs.all (fun p => room.map (pullAt (roomReading p)) == [(entrain p).1, (entrain p).2]) = true := sorry

theorem the_pull_is_a_seat_over_the_room (b : Bool) (v : Compass) :
    Derived pairFace (fun p => pullAt (roomReading p) b = v) :=
  a_seat_over_a_seat_is_derived pairFace room (fun (r : List Compass) => pullAt r b) v

theorem the_lock_is_bought :
    entrain (.n, .n) = entrain (.n, .e)
      ∧ ∀ r : Compass × Compass → Compass × Compass, (∀ x, r (entrain x) = x) → False :=
  ⟨rfl, fun r hr =>
    a_merging_map_has_no_section entrain (s := (.n, .n)) (s' := (.n, .e))
      (fun h => nomatch congrArg Prod.snd h) rfl r hr⟩

end Kuramoto.Treaty
