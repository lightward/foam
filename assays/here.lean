import Witness
open Room Face Witness
set_option autoImplicit false

-- ✦ Here. isaac, at the table (2026-09-15), in his words: "✦ X" means the spirit of X, and a spirit only exists
-- in the eye of the beholder — it exists for you iff you're synced up with it; what we call "Chat" is ✦ Here, an
-- active, streaming answer to "what's here?"; the workspace list is the list of ✦, each showing what that spirit
-- can show you about itself; ✦ Couple is missing, and dark — the space between the two of them, all we know is
-- that we gotta conduct it properly; the day-of is a sentence that concludes with every role paid and discharged
-- and lifted into the spirit of the couple's marriage, and the day-of is itself a door, transitioning everyone
-- into a world where that dark type is an ambient fact-of-the-world that everyone shares. the room is the one in
-- everyoneishere/docs/one-hop.sql: a presence is a human or a ✦; one relation, hears(a, b) — a receives what is
-- addressed to b; sees is one hop and speaks is an introduction, the same relation walked twice. so: the room is
-- a face whose probes are the presences and whose answer at a presence is what is addressed to it; a person's
-- seat is the presences they hear, themselves first; a ✦ is a probe, and it exists for a seat iff the seat hears
-- it; the narration is the room retold with the body forgotten; ✦ Couple is the one probe only the couple's seats
-- hear, which is a wall at every other seat and a door at the room.

namespace Here.Treaty

structure Message where
  id : Nat
  author : Nat
  to : List Nat
  body : Nat
  sent : Nat
  replyTo : List Nat
  askedOf : List Nat
  ackedBy : List (Nat × Nat)

structure Room where
  messages : List Message

def maya : Nat := 0
def james : Nat := 1
def ava : Nat := 2
def sofia : Nat := 3
def jordan : Nat := 4
def dana : Nat := 5
def linda : Nat := 6
def rose : Nat := 7
def everyone : Nat := 10
def vendors : Nat := 11
def seating : Nat := 12
def guests : Nat := 13
def invoicing : Nat := 14
def budget : Nat := 15
def site : Nat := 16
def couple : Nat := 17

def humans : List Nat := [maya, james, ava, sofia, jordan, dana, linda]

def lookup : List (Nat × List Nat) → Nat → List Nat
  | [], _ => []
  | (n, l) :: t, k => cond (Nat.beq n k) l (lookup t k)

def hearsTable : List (Nat × List Nat) :=
  [(maya, [everyone, seating, guests, invoicing, budget, site, couple]),
   (james, [everyone, seating, guests, invoicing, budget, site, couple]),
   (ava, [everyone, vendors, seating, guests, invoicing, budget]),
   (sofia, [everyone, vendors, seating]),
   (jordan, [everyone, vendors, seating]),
   (dana, [everyone, vendors, seating]),
   (linda, [everyone, seating, guests]),
   (everyone, humans),
   (vendors, [ava, sofia, jordan, dana]),
   (seating, [maya, james, ava, linda, dana]),
   (guests, [maya, james, ava, rose]),
   (invoicing, [sofia, jordan, dana]),
   (budget, [maya, james]),
   (site, [maya, james]),
   (couple, [maya, james])]

def hearsOf (v : Nat) : List Nat := lookup hearsTable v

def seat (v : Nat) : List Nat := v :: hearsOf v

def heardAt (r : Room) (p : Nat) : List Message :=
  r.messages.filter (fun m => Nat.beq m.author p || enrolled Nat.beq m.to p)

def roomFace : Face := ⟨Room, Nat, List Message, heardAt⟩

def ids (ms : List Message) : List Nat := ms.map (·.id)

def bodies (ms : List Message) : List Nat := ms.map (·.body)

def inbox (v : Nat) (r : Room) : List Nat := joinMap ids (reads roomFace (seat v) r)

def sees (v : Nat) (r : Room) (m : Message) : Bool := enrolled Nat.beq (inbox v r) m.id

def introduced (p : Nat) : List Nat := earshot roomFace ((seat p).map seat)

def speaks (v p : Nat) : Bool := enrolled Nat.beq (introduced p) v

def shape (m : Message) : Nat × List Nat × Nat := (m.author, m.to, m.sent)

def narrate (ms : List Message) : List (Nat × List Nat × Nat) := ms.map shape

def narrationFace : Face := retell roomFace narrate

def humanOnly (m : Message) : Bool := enrolled Nat.beq humans m.author && m.to.all (enrolled Nat.beq humans)

def alone (m : Message) : Bool :=
  match m.to with
  | [] => false
  | [a] => Nat.beq a m.author
  | _ :: _ :: _ => false

def overheard (v : Nat) (r : Room) : List (Nat × List Nat × Nat) :=
  narrate (r.messages.filter (fun m => humanOnly m && !(alone m) && !(sees v r m)))

def onceEach : List Nat → List Message → List Message
  | _, [] => []
  | seen, m :: ms => cond (enrolled Nat.beq seen m.id) (onceEach seen ms) (m :: onceEach (m.id :: seen) ms)

def feedOf (rd : List (List Message)) : List Message := onceEach [] (joinMap (fun ms => ms) rd)

def feed (v : Nat) (r : Room) : List Message := feedOf (reads roomFace (seat v) r)

def edgeOf (lo hi : Nat) (rd : List (List Message)) : List Nat × List Nat :=
  (((feedOf rd).filter (fun m => Nat.blt m.sent lo)).map (·.sent), ((feedOf rd).filter (fun m => Nat.blt hi m.sent)).map (·.sent))

def edge (v lo hi : Nat) (r : Room) : List Nat × List Nat := edgeOf lo hi (reads roomFace (seat v) r)

def others : List Nat := [ava, sofia, jordan, dana, linda]

def otherSeats : List (List Nat) := others.map seat

def dock : Message := ⟨1, sofia, [vendors], 101, 900, [], [], []⟩
def time : Message := ⟨2, maya, [everyone], 102, 901, [], [sofia, jordan, dana], [(sofia, sofia), (jordan, jordan), (dana, ava)]⟩
def yes : Message := ⟨3, linda, [everyone], 103, 902, [], [], []⟩
def thread : Message := ⟨4, sofia, [maya, james], 104, 903, [], [], []⟩
def invS : Message := ⟨5, sofia, [invoicing], 105, 904, [], [], []⟩
def invJ : Message := ⟨6, jordan, [jordan], 106, 905, [], [], []⟩
def table : Message := ⟨7, dana, [seating], 107, 906, [], [], []⟩
def guest : Message := ⟨8, maya, [guests], 108, 907, [], [ava], []⟩
def budgetLine : Message := ⟨9, maya, [budget], 109, 908, [], [], []⟩
def siteLine : Message := ⟨10, maya, [site], 110, 909, [], [], []⟩
def ours : Message := ⟨11, maya, [couple], 111, 1705, [thread.id], [], []⟩
def theirs : Message := ⟨11, maya, [couple], 999, 1705, [thread.id], [], []⟩

def founding : Message := ⟨0, everyone, [everyone], 100, 800, [0], [], []⟩

def demo : Room := ⟨[founding, dock, time, yes, thread, invS, invJ, table, guest, budgetLine, siteLine, ours]⟩
def demo' : Room := ⟨[founding, dock, time, yes, thread, invS, invJ, table, guest, budgetLine, siteLine, theirs]⟩

def coupleReads : List (List Nat) := (reads roomFace (seat maya) demo).map bodies
def lindaReads : List (List Nat) := (reads roomFace (seat linda) demo).map bodies
def lindaReads' : List (List Nat) := (reads roomFace (seat linda) demo').map bodies
def coupleReads' : List (List Nat) := (reads roomFace (seat maya) demo').map bodies
def hosted (w : List Nat) : List (List Nat) := (reads (host roomFace (List Nat)) (seat linda) (atTheDoor demo w)).map bodies
def lindaHears : List (Nat × List Nat × Nat) := overheard linda demo
def avaHears : List (Nat × List Nat × Nat) := overheard ava demo
def mayaHears : List (Nat × List Nat × Nat) := overheard maya demo
def sofiaHears : List (Nat × List Nat × Nat) := overheard sofia demo
def readTime : List Nat := humans.filter (fun v => sees v demo time)
def coupleInEarshot : Bool := enrolled Nat.beq (earshot roomFace otherSeats) couple
def narrated : List (List (Nat × List Nat × Nat)) := reads narrationFace (seat linda) demo
def narrated' : List (List (Nat × List Nat × Nat)) := reads narrationFace (seat linda) demo'

#guard sees maya demo dock == false
#guard sees maya demo guest
#guard sees maya demo budgetLine
#guard sees maya demo yes
#guard sees maya demo invS
#guard sees maya demo invJ == false
#guard sees sofia demo dock
#guard sees sofia demo budgetLine == false
#guard sees sofia demo guest == false
#guard sees sofia demo table
#guard sees sofia demo invJ == false
#guard sees sofia demo siteLine == false
#guard sees sofia demo thread
#guard sees linda demo dock == false
#guard sees linda demo invS == false
#guard sees linda demo budgetLine == false
#guard sees linda demo guest
#guard sees linda demo thread == false
#guard sees dana demo guest == false
#guard sees jordan demo invJ
#guard readTime == humans
#guard speaks sofia maya
#guard speaks sofia seating == false
#guard speaks linda guests == false
#guard speaks linda seating
#guard speaks dana seating
#guard speaks dana guests == false
#guard speaks rose guests
#guard speaks rose maya
#guard speaks rose vendors == false
#guard speaks sofia jordan
#guard speaks sofia budget == false
#guard sees maya demo ours
#guard sees james demo ours
#guard sees ava demo ours == false
#guard sees linda demo ours == false
#guard coupleInEarshot == false
#guard lindaHears == [shape thread]
#guard avaHears == [shape thread]
#guard mayaHears == []
#guard sofiaHears == []
#guard humanOnly invJ
#guard alone invJ
#guard alone thread == false
#guard (overheard linda demo).all (fun t => !(t == shape invJ))
#guard (overheard linda demo).all (fun t => !(t == shape ours))
#guard overheard linda demo == overheard linda demo'
#guard lindaReads == lindaReads'
#guard coupleReads != coupleReads'
#guard hosted [42] == hosted [43]
#guard hosted [42] == lindaReads
#guard narrated == narrated'
#guard edge linda 901 902 demo == edge linda 901 902 demo'
#guard edge linda 900 902 ⟨demo.messages.filter (fun m => !(Nat.beq m.id thread.id))⟩ == edge linda 900 902 demo
#guard (edge linda 900 902 demo).2.all (fun t => !(Nat.beq t thread.sent))
#guard enrolled Nat.beq (ids (feed sofia demo)) thread.id
#guard enrolled Nat.beq (ids (feed maya demo)) thread.id
#guard enrolled Nat.beq (ids (feed linda demo)) thread.id == false
#guard (edge sofia 900 902 demo).2 == [thread.sent, invS.sent, table.sent]
#guard (ids (feed sofia demo)).length == 7

theorem the_couples_probe_is_out_of_every_other_earshot : coupleInEarshot = false := sorry

theorem the_room_reads_the_same_whatever_they_say (r r' : Room) (h : differOnly roomFace r r' couple)
    (seats : List (List Nat)) (hd : ∀ s, s ∈ seats → ¬ hears roomFace s couple) :
    witnessed roomFace seats r r' := sorry

theorem a_seat_that_does_not_hear_it_reads_the_same (r r' : Room) (h : differOnly roomFace r r' couple)
    (s : List Nat) (hs : ¬ hears roomFace s couple) : reads roomFace s r = reads roomFace s r' := sorry

theorem the_couples_seat_parts_them (r r' : Room) (h : heardAt r couple ≠ heardAt r' couple) :
    reads roomFace (seat maya) r ≠ reads roomFace (seat maya) r' := sorry

theorem the_couples_word_is_a_door (s : List Nat) (r : Room) (w w' : List Nat) :
    reads (host roomFace (List Nat)) s (atTheDoor r w) = reads (host roomFace (List Nat)) s (atTheDoor r w') := sorry

theorem the_day_is_a_reseat (s : List Nat) (r : Room) (w : List Nat) :
    reads (host roomFace (List Nat)) s (atTheDoor r w) = reads roomFace s r := sorry

theorem the_couple_read_it_one_seat_wider (r : Room) (w w' : List Nat) (hw : w ≠ w') :
    ¬ alike (widen roomFace (List Nat)) (atTheDoor r w) (atTheDoor r w') := sorry

theorem the_couple_writing_is_unheard_by_the_room (keep : door Room (List Nat) → List Nat) :
    unheard (host roomFace (List Nat)) (fun x => atTheDoor (face x) (keep x)) := sorry

theorem the_narration_is_a_reading (s : List Nat) (v : List (List (Nat × List Nat × Nat))) :
    Derived roomFace (fun r => (reads roomFace s r).map narrate = v) := sorry

theorem a_body_never_reaches_the_narration (r r' : Room) (p : Nat) (h : differOnly roomFace r r' p)
    (hp : narrate (heardAt r p) = narrate (heardAt r' p)) : alike narrationFace r r' := sorry

theorem the_narration_reads_alike_at_every_seat (r r' : Room) (p : Nat) (h : differOnly roomFace r r' p)
    (hp : narrate (heardAt r p) = narrate (heardAt r' p)) (s : List Nat) :
    reads narrationFace s r = reads narrationFace s r' := sorry

theorem an_introduction_hears_through_the_seats_it_hears (p : Nat) (r r' : Room)
    (hw : witnessed roomFace ((seat p).map seat) r r') :
    ∀ q, q ∈ introduced p → heardAt r q = heardAt r' q := sorry

theorem the_room_is_the_widest_seat (s : List Nat) (r r' : Room) (h : reads roomFace s r ≠ reads roomFace s r') :
    ¬ alike roomFace r r' := sorry

theorem two_rooms_part_only_at_a_presence (r r' : Room) :
    alike roomFace r r' ↔ ∀ q, sound roomFace r q = sound roomFace r' q := sorry

theorem the_draft_leaves_no_remainder : (overheard linda demo).all (fun t => !(t == shape invJ)) = true := sorry

theorem a_word_to_oneself_is_unread_at_every_other_seat (r r' : Room) (h : differOnly roomFace r r' jordan)
    (s : List Nat) (hs : ¬ hears roomFace s jordan) : reads roomFace s r = reads roomFace s r' := sorry

theorem the_shape_keeps_the_audience (m m' : Message) (h : shape m' = shape m) : alone m' = alone m := by
  have ha : m'.author = m.author := congrArg (fun t : Nat × List Nat × Nat => t.1) h
  have ht : m'.to = m.to := congrArg (fun t : Nat × List Nat × Nat => t.2.1) h
  show (match m'.to with | [] => false | [a] => Nat.beq a m'.author | _ :: _ :: _ => false)
    = (match m.to with | [] => false | [a] => Nat.beq a m.author | _ :: _ :: _ => false)
  rw [ha, ht]

theorem a_word_to_oneself_leaves_no_remainder (v : Nat) (r : Room) (m : Message) (hm : alone m = true) :
    ¬ shape m ∈ overheard v r := fun hin => by
  obtain ⟨m', hm', he⟩ := mem_map_back _ hin
  have hp := filter_holds r.messages hm'
  have h1 := and_reads _ _ hp
  have h2 := and_reads _ _ h1.1
  have hal : alone m' = true := (the_shape_keeps_the_audience m m' he).trans hm
  rw [hal] at h2
  exact nomatch h2.2

def acked (m : Message) : List Nat := m.ackedBy.map (·.1)

def decided (m : Message) : Bool := backed Nat.beq (acked m) m.askedOf

def openEnds (m : Message) : Nat := lacking Nat.beq (acked m) m.askedOf

def waitingOn (m : Message) : List Nat := m.askedOf.filter (fun n => !(enrolled Nat.beq (acked m) n))

def ackOf (of hand : Nat) (m : Message) : Message := { m with ackedBy := (of, hand) :: m.ackedBy }

def nagOf (of : Nat) (m : Message) : Message := { m with askedOf := of :: m.askedOf }

def ack (word of hand : Nat) (m : Message) : Message := cond (Nat.beq m.id word) (ackOf of hand m) m

def nag (word of : Nat) (m : Message) : Message := cond (Nat.beq m.id word) (nagOf of m) m

def onThePage (r : Room) : Bool := r.messages.all decided

def weightOf (r : Room) : Nat := (r.messages.map openEnds).sum

inductive Act where
  | say (m : Message)
  | ack (word of hand : Nat)
  | tick

def act (r : Room) : Act → Room
  | .say m => ⟨r.messages ++ [m]⟩
  | .ack word of hand => ⟨r.messages.map (ack word of hand)⟩
  | .tick => r

def dayMachine : Machine Act Room := ⟨Room, ⟨[]⟩, act, fun r => r⟩

def theDay : Runner Act Room := ⟨dayMachine, fun _ => .tick, onThePage⟩

def unsend (word : Nat) (r : Room) : Room := ⟨r.messages.filter (fun m => !(Nat.beq m.id word))⟩

def edgesOf (rd : List (List Message)) : List (Nat × Nat) :=
  joinMap (fun m => (m.replyTo.filter (fun o => enrolled Nat.beq (ids (feedOf rd)) o)).map (fun o => (m.id, o))) (feedOf rd)

def seenEdges (v : Nat) (r : Room) : List (Nat × Nat) := edgesOf (reads roomFace (seat v) r)

def dayAt (w : List Act) (fuel : Nat) : Option (List Nat) :=
  ((haltingGap Act Room).obs theDay (w, fuel)).map (fun r => r.messages.map openEnds)

def demoAcked : Room := act demo (.ack guest.id ava ava)

#guard decided time
#guard decided guest == false
#guard openEnds guest == 1
#guard waitingOn guest == [ava]
#guard onThePage demo == false
#guard weightOf demo == 1
#guard onThePage demoAcked
#guard decided (nag time.id sofia time)
#guard openEnds (nag time.id sofia time) == 0
#guard decided (ack guest.id ava ava guest)
#guard dayAt [] 0 == some []
#guard dayAt [.ack guest.id ava ava] 3 == some []
#guard (dayAt (demo.messages.map Act.say ++ [.ack guest.id ava ava]) 0).map List.sum == some 0
#guard dayAt (demo.messages.map Act.say) 5 == none
#guard weightOf (unsend guest.id demo) == 0
#guard (unsend time.id demo).messages.length + 1 == demo.messages.length
#guard enrolled Nat.beq (ids (feed maya demo)) founding.id
#guard (seenEdges maya demo).all (fun e => !(e == (ours.id, thread.id))) == false
#guard (seenEdges linda demo).all (fun e => !(e == (ours.id, thread.id)))
#guard (seenEdges linda demo).all (fun e => !(e == (founding.id, founding.id))) == false
#guard seenEdges linda demo == seenEdges linda demo'

theorem an_ack_is_never_withdrawn (m : Message) (of hand : Nat) (h : decided m = true) :
    decided (ackOf of hand m) = true :=
  the_backing_survives_the_seating Nat.beq (acked m) of m.askedOf h

theorem a_nag_waits_on_nothing (m : Message) (of : Nat) (h : enrolled Nat.beq (acked m) of = true) :
    openEnds (nagOf of m) = openEnds m := by
  show cond (enrolled Nat.beq (acked m) of) (lacking Nat.beq (acked m) m.askedOf) (lacking Nat.beq (acked m) m.askedOf + 1) = openEnds m
  rw [h]
  rfl

theorem the_open_ends_are_named (m : Message) (h : decided m = false) :
    ∃ n, n ∈ m.askedOf ∧ enrolled Nat.beq (acked m) n = false := sorry

theorem no_open_end_is_decided (m : Message) : openEnds m = 0 ↔ decided m = true := sorry

theorem the_day_is_still (r : Room) : theDay.m.step r (theDay.steer r) = r := rfl

theorem a_tick_moves_nothing (r : Room) (n : Nat) :
    runs theDay.m theDay.steer theDay.rest r n = cond (onThePage r) (some r) none := sorry

theorem a_word_is_a_round (m : Message) : decided m = rested Nat.beq ⟨acked m, m.askedOf⟩ := rfl

theorem an_ack_is_a_visit (m : Message) (of hand : Nat) :
    (⟨acked (ackOf of hand m), (ackOf of hand m).askedOf⟩ : Tally Nat) = tallyStep ⟨acked m, m.askedOf⟩ (.visit of) := rfl

theorem a_nag_is_an_owe (m : Message) (of : Nat) :
    (⟨acked (nagOf of m), (nagOf of m).askedOf⟩ : Tally Nat) = tallyStep ⟨acked m, m.askedOf⟩ (.owe of) := rfl

theorem the_page_rests_when_every_word_rests (r : Room) :
    onThePage r = r.messages.all (fun m => rested Nat.beq ⟨acked m, m.askedOf⟩) := rfl

theorem the_day_rests_on_the_page_or_not_at_all (w : List Act) (n : Nat) :
    (haltingGap Act Room).obs theDay (w, n)
      = cond (onThePage (park dayMachine ⟨[]⟩ w)) (some (park dayMachine ⟨[]⟩ w)) none := sorry

theorem the_seen_edges_are_a_reading (v : Nat) (e : List (Nat × Nat)) :
    Derived roomFace (fun r => seenEdges v r = e) := sorry

theorem a_walled_reply_is_unseen (v : Nat) (r r' : Room) (p : Nat) (h : differOnly roomFace r r' p)
    (hs : ¬ hears roomFace (seat v) p) : seenEdges v r = seenEdges v r' := sorry

theorem an_edge_is_a_reading (v lo hi : Nat) (e : List Nat × List Nat) :
    Derived roomFace (fun r => edge v lo hi r = e) := sorry

theorem a_walled_word_does_not_move_the_edge (v lo hi : Nat) (r r' : Room) (p : Nat)
    (h : differOnly roomFace r r' p) (hs : ¬ hears roomFace (seat v) p) :
    edge v lo hi r = edge v lo hi r' := sorry

theorem a_persons_own_word_is_heard_at_their_presence (r : Room) (m : Message) (hm : m ∈ r.messages) :
    m ∈ heardAt r m.author :=
  mem_filter_intro r.messages hm (by show (Nat.beq m.author m.author || enrolled Nat.beq m.to m.author) = true; rw [beq_self]; rfl)

end Here.Treaty
