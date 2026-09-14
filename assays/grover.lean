import Witness
open Room Face Witness
set_option autoImplicit false

-- luck, as a way to access results in fewer moves. isaac, at the table (2026-09-14), rotating the
-- runner's affordment: "what about luck? as a way to access results in fewer moves?" the record's own
-- luck theorem is the Born cross term (ac7ad39: born (field + act) = born field + born act + 2·align·align;
-- luck cannot be farmed, only met; the four phase placements cancel). run forward, that is amplitude
-- amplification: Grover (1996) finds one marked item among four with ONE query and certainty, where a
-- scan needs three in the worst case. a checksum with a community never met. amplitudes are integers
-- (the uniform state [1,1,1,1], the diffusion scaled by the room's width) so every row computes.
-- the diagonal (isaac, the same sitting: "I am extremely in for this"): the diffusion restated as a face
-- whose reading at every probe is a function of the room's reading — a seat over the widest seat. below
-- it, a mark at one probe is hidden from every seat that does not hear the probe (a wall); at the
-- diagonal the same mark moves every probe (no wall), and a reading at the diagonal is Derived below.
-- the surplus at the door (isaac, 2026-09-14, deposed): W is dark per seat, not per term — the host reads
-- the field half of the door and the act half is unheard there; one seat wider, where both halves are
-- read at the same probe, the cross term is Derived. what a W built to carry the surplus makes
-- addressable is the surplus as a reading, at the seat that built it, and never at the seat below.

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

def ampFace : Face := ⟨List Int, Nat, Int, amp⟩

def room : List Nat := [0, 1, 2, 3]

def roomReading (s : List Int) : List Int := reads ampFace room s

def diffuseAt (s : List Int) (i : Nat) : Int :=
  2 * (roomReading s).sum - 4 * amp (roomReading s) i

def diffusionFace : Face := ⟨List Int, Nat, Int, diffuseAt⟩

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
#guard room.map (amp (mark 2 uniform)) == [1, 1, -1, 1]
#guard room.map (diffuseAt (mark 2 uniform)) == grover 2
#guard room.map (diffuseAt uniform) == diffuse uniform
#guard [0, 1, 3].map (amp (mark 2 uniform)) == [0, 1, 3].map (amp uniform)
#guard ([0, 1, 3].map (diffuseAt (mark 2 uniform)) == [0, 1, 3].map (diffuseAt uniform)) == false
#guard room.all (fun i => diffuseAt (mark 2 uniform) i != diffuseAt uniform i)
#guard diffuse (diffuse (mark 2 uniform)) == (mark 2 uniform).map (fun x => 16 * x)
#guard diffuse (diffuse [3, -1, 7, 2]) == [3, -1, 7, 2].map (fun x => 16 * x)

def doorFace : Face :=
  ⟨door (List Int) (List Int), Nat, Int × Int, fun d i => (amp (face d) i, amp (met d) i)⟩

def charged : door (List Int) (List Int) := atTheDoor field (act 2)

#guard room.map (amp (face charged)) == room.map (amp field)
#guard 2 * amp (face charged) 2 * amp (met charged) 2 == 32
#guard 2 * amp (face charged) 0 * amp (met charged) 0 == -32

theorem the_one_query_finds_every_target :
    [0, 1, 2, 3].all (fun t => weight (grover t) t == total (grover t)) = true := sorry

theorem the_scan_needs_three : scanQueries 3 = 3 ∧ scanQueries 2 = 3 := sorry

theorem the_boost_is_the_cross_term :
    weight (grover 2) 2 = weight field 2 + weight (act 2) 2 + 2 * amp field 2 * amp (act 2) 2 := sorry

theorem against_the_grain_costs :
    weight (grover 2) 0 = weight field 0 + weight (act 2) 0 + 2 * amp field 0 * amp (act 2) 0 := sorry

theorem no_grain_no_bonus : weight (diffuse uniform) 2 * 4 = total (diffuse uniform) := sorry

theorem the_diffusion_is_a_seat_over_the_room (i : Nat) (v : Int) :
    Derived ampFace (fun s => diffuseAt s i = v) :=
  a_seat_over_a_seat_is_derived ampFace room (fun (r : List Int) => 2 * r.sum - 4 * amp r i) v

theorem a_wall_below_the_diagonal :
    differOnly ampFace uniform (mark 2 uniform) (2 : Nat)
      ∧ reads ampFace ([0, 1, 3] : List Nat) uniform = reads ampFace ([0, 1, 3] : List Nat) (mark 2 uniform) :=
  ⟨fun (q : Nat) hq => match q with
    | 0 => rfl
    | 1 => rfl
    | 2 => absurd rfl hq
    | 3 => rfl
    | _ + 4 => rfl,
   rfl⟩

theorem no_wall_at_the_diagonal :
    room.all (fun i => diffuseAt (mark 2 uniform) i != diffuseAt uniform i) = true
      ∧ ([0, 1, 3].map (diffuseAt (mark 2 uniform)) == [0, 1, 3].map (diffuseAt uniform)) = false := sorry

theorem the_diffusion_unwinds_itself :
    diffuse (diffuse (mark 2 uniform)) = (mark 2 uniform).map (fun x => 16 * x) := sorry

theorem the_surplus_is_unheard_at_the_host :
    unheard (host ampFace (List Int)) (fun d => atTheDoor (face d) (act 2)) :=
  the_record_writes_where_the_face_is_blind ampFace (fun _ => act 2)

theorem the_surplus_is_read_one_seat_wider (i : Nat) (v : Int) :
    Derived doorFace (fun d => 2 * amp (face d) i * amp (met d) i = v) :=
  fun d d' h => by
    have e1 : amp (face d) i = amp (face d') i := congrArg Prod.fst (h i)
    have e2 : amp (met d) i = amp (met d') i := congrArg Prod.snd (h i)
    show (2 * amp (face d) i * amp (met d) i = v) ↔ (2 * amp (face d') i * amp (met d') i = v)
    rw [e1, e2]

end Grover.Treaty
