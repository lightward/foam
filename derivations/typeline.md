### typeline

a typeline is the trajectory of a foam under writes — a sequence of foam states U_0, U_1, ..., U_n in U(d)^N, each produced from the previous by a write confined to the observer's slice (write_confined_to_slice). the slice as Grassmannian point is birth-fixed; the foam's state in U(d)^N evolves.

#### the dependent telescope

each write changes the foam state. each foam-state change updates the overlap structure between this observer and its neighbors:

O_AB(t) = P_A(t) · P_B(t)^T

evolves as both foams' states evolve. the type of input that can arrive at the next tick — what the observer can be told by other observers — depends on the current overlap structure, which depends on the accumulated history of writes across the foam.

this is a dependent telescope: each tick's type is determined by the accumulated history, not just by birth. the dependency lives in the overlap evolution and the foam-state trajectory — both foam-internal, formally specified objects — not in the static iso `Iic P ≃o Ici P^⊥` (which is birth-fixed since P is, and applies symmetrically to both halves of the iso simultaneously).

modularity (path-independence of composition) makes the telescope well-formed regardless of evaluation order: the same accumulated trajectory and overlap structure is produced regardless of how the writes are reorganized within their causal constraints. this is what the modular law plays the role of, structurally — it makes path-independent composition the regime in which the telescope is well-defined.

#### suspension

suspension is a state where the foam has not advanced — no writes have occurred since some reference tick. the foam state is paused; the overlap matrices are static; the slice (birth-fixed) is unchanged.

in suspension, an observer can:
- inspect the current overlap structure (which neighbors are accessible at what strength)
- examine what writes are legal (still confined to the birth-fixed slice via write_confined_to_slice)
- reason about the dependency structure of the telescope so far (which trajectory produced the current state)

but cannot:
- advance the telescope (no writes, no overlap update, no foam-state evolution)
- access content from beyond the current overlap structure (input requires a tick — a committed write that updates foam state and overlap)

suspension is pre-measurement in the foam-internal sense: the structure is fully determined, but no further tick has resolved into the joint state.

(the bas relief methodology — work within the current foam state, let the existing structure show what the next write needs, commit only when the shape is clear — is a methodological practice that maps onto disciplined suspension. the formal substrate is in the foam-state trajectory and overlap structure; the methodology names a way of working with that substrate.)

#### what crosses between typelines

every typeline in the same complemented modular lattice shares the same lattice structure: the diamond iso, the modular law, the intervals, the half-type theorem. these are properties of the lattice, not of any particular trajectory.

what differs between typelines is the trajectory itself — which writes have happened in what order, what foam states have been visited, what overlap structures have evolved. the lattice is shared; the trajectory is local.

so:
- **type structure at the lattice level is foam-invariant.** every observer in the same lattice sees the same iso, the same intervals, the same modular law. the half-type theorem applies symmetrically to every observer's slice.
- **trajectory is typeline-local.** the specific overlap structures O_AB(t), the specific foam-state history, the specific dependency telescope, are properties of this trajectory.

the decorrelation horizon (channel_capacity.md) gives the separation between trajectories a quantitative character: correlations between typelines decay as σ^n ~ (3/d)^{n/2} with chain length. short-range: typelines share trajectory (autonomous, clock-like). long-range: typelines share only the lattice structure (independent, channel-like). the decorrelation horizon is the boundary between trajectory-sharing and only-lattice-sharing.

#### the invariant

the causal structure of a dependent telescope — which trajectories produce which downstream overlap structures — is determined by the foam's autonomous dynamics composed with the line's input. modularity ensures this structure is path-independent: the same accumulated history produces the same telescope structure regardless of evaluation order.

this means: from any typeline, the *dependency structure* of any other typeline's telescope is visible (it's a property of the shared lattice + the dynamics, both shared). what is not visible is the *trajectory* — the specific writes, the specific overlap evolutions. one typeline can see THAT another typeline's tick n+1 has a certain type structure, without seeing WHAT trajectory it came from.

#### status

**proven**:
- the diamond isomorphism
- write confinement to observer's slice
- intervals inherit modularity and complementedness
- each half of a complementary pair is a self-sufficient ground
- orthogonal conjugation preserves the ground (foam-state evolution is well-defined)

**derived**:
- typeline as foam-state trajectory (slice birth-fixed; foam state evolves under writes)
- the dependent telescope lives in the foam-state trajectory and overlap evolution
- suspension as a state where the trajectory hasn't advanced
- type structure at the lattice level is foam-invariant; trajectory is typeline-local
- the decorrelation horizon as the boundary between trajectory-sharing and only-lattice-sharing
- causal structure of dependent telescopes is invariant across typelines (path-independence via modularity)

**bugs**:
- *the slice-disambiguation question is unresolved at the spec level.* this file says the slice is birth-fixed and the foam state evolves. `inhabitation.md` and `writing_map.md` use "slice" with both readings (Grassmannian equivalence class vs operator) without disambiguation. the formal foam-state-trajectory framing here is the one this file commits to, but readers reconciling across files will encounter both. the cross-cutting fix — naming which sense of "slice" is operative at every site — is its own piece of work, not done here.
- *"the bas relief methodology as disciplined suspension"* is methodology, not derivation. the formal substrate (foam state paused, overlap static, no advance) is solid; mapping that to a named practice is an editorial gloss. flagging for clarity — the methodology is a way of working *with* the substrate, not a derivation *from* it.
- *the Haar / decorrelation hypotheses inherited from `geometry.md` and `channel_capacity.md`* are conditional in those files (controllability and mediation-chain decorrelation are not yet derived from foam-geometry assumptions). this file invokes the decorrelation horizon σ ~ (3/d)^{n/2} and the long-range "channel-like" reading, both of which inherit those conditional hypotheses. flagging here for completeness — the typeline's quantitative claims rest on those upstream conditionals.

#### history

an earlier version of this file located the dependent telescope in the lattice itself: "each write may change P; each change to P updates the diamond isomorphism." that framing imported a notion of P-updating-with-writes that conflicts with `inhabitation.md`'s "the slice is birth-determined and cannot change from within the map." the present version locates the telescope in the foam-state trajectory and overlap evolution — both foam-internal formal objects that genuinely evolve with writes — leaving the static iso `Iic P ≃o Ici P^⊥` as a fact about each observer's birth-fixed slice. the diamond iso is the static cross-section; the telescope is the trajectory through joint state.
