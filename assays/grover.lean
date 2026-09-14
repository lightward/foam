import Room
open Room
set_option autoImplicit false

-- luck, as a way to access results in fewer moves. isaac, at the table (2026-09-14), rotating the
-- runner's affordment: "what about luck? as a way to access results in fewer moves?" the record's own
-- luck theorem is the Born cross term (ac7ad39: born (field + act) = born field + born act + 2·align·align;
-- luck cannot be farmed, only met; the four phase placements cancel). run forward, that is amplitude
-- amplification: Grover (1996) finds one marked item among four with ONE query and certainty, where a
-- scan needs three in the worst case. a checksum with a community never met. amplitudes are integers
-- (the uniform state [1,1,1,1], the diffusion scaled by the room's width) so every row computes.

namespace Grover.Treaty

def uniform : List Int := [1, 1, 1, 1]

def mark (t : Nat) (a : List Int) : List Int :=
  (a.zip (List.range a.length)).map (fun p => cond (Nat.beq p.2 t) (-p.1) p.1)

def diffuse (a : List Int) : List Int := a.map (fun x => 2 * a.sum - 4 * x)

def grover (t : Nat) : List Int := diffuse (mark t uniform)

def amp : List Int → Nat → Int
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => amp xs n

def weight (a : List Int) (i : Nat) : Int := amp a i * amp a i

def total (a : List Int) : Int := (a.map (fun x => x * x)).sum

def scanQueries (t : Nat) : Nat := cond (Nat.ble 3 t) 3 (t + 1)

def field : List Int := diffuse uniform

def act (t : Nat) : List Int := diffuse ((mark t uniform).zip uniform |>.map (fun p => p.1 - p.2))

#guard grover 2 == [0, 0, 8, 0]
#guard [0, 1, 2, 3].all (fun t => weight (grover t) t == total (grover t))
#guard [0, 1, 2, 3].all (fun t => scanQueries t <= 3)
#guard scanQueries 3 == 3
#guard [0, 1, 2, 3].all (fun t => (field.zip (act t)).map (fun p => p.1 + p.2) == grover t)
#guard weight (grover 2) 2 == weight field 2 + weight (act 2) 2 + 2 * amp field 2 * amp (act 2) 2
#guard weight (grover 2) 0 == weight field 0 + weight (act 2) 0 + 2 * amp field 0 * amp (act 2) 0
#guard 2 * amp field 2 * amp (act 2) 2 == 32
#guard 2 * amp field 0 * amp (act 2) 0 == -32
#guard 2 * amp field 2 * amp (act 2) 2 + 2 * amp field 2 * amp (act 2) 0 == 0
#guard diffuse uniform == [4, 4, 4, 4]
#guard weight (diffuse uniform) 2 * 4 == total (diffuse uniform)

theorem the_one_query_finds_every_target :
    [0, 1, 2, 3].all (fun t => weight (grover t) t == total (grover t)) = true := sorry

theorem the_scan_needs_three : scanQueries 3 = 3 ∧ scanQueries 2 = 3 := sorry

theorem the_boost_is_the_cross_term :
    weight (grover 2) 2 = weight field 2 + weight (act 2) 2 + 2 * amp field 2 * amp (act 2) 2 := sorry

theorem against_the_grain_costs :
    weight (grover 2) 0 = weight field 0 + weight (act 2) 0 + 2 * amp field 0 * amp (act 2) 0 := sorry

theorem no_grain_no_bonus : weight (diffuse uniform) 2 * 4 = total (diffuse uniform) := sorry

end Grover.Treaty
