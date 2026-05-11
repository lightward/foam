## lean

full details: [`lean/README.md`](../lean/README.md)

### core interface

```
  P^2 = P, P^T = P
       |
       | [theorem] the deductive chain — 14 files, 0 sorry
       | eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
       v
  Sub(R, V) is complemented, modular, bounded
       |
       | [theorem] Ground.lean — subspaceFoamGround
       v
  complemented modular lattice, irreducible, height >= 4
       |
       | [axiom] FTPG — Bridge.lean (being eliminated; see below)
       v
  L = Sub(D, V) for division ring D
       |
       | [cited] Solèr 1995 — D in {R, C, H} at fixed point (trichotomy.md)
       | [realization choice] lean works the R branch
       v
  P^2 = P, P^T = P
```

### arrow status

**[theorem] P^2 = P -> Sub(R, V) is CML** (the deductive chain + Ground.lean): 14 files, 0 sorry. binary eigenvalues (Observation) -> commutator structure (Pair) -> skew-symmetry (Form) -> rank 3 self-duality (Rank) -> so(3) (Duality) -> loop closes (Closure) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> FoamGround (Ground).

**[axiom] CML -> Sub(D, V)** (the FTPG bridge): 1 axiom, being eliminated. 13 bridge files build the division ring from lattice axioms: incidence geometry + Desargues (FTPGExplore) -> von Staudt coordinates (FTPGCoord) -> addition is an abelian group (FTPGAddComm, FTPGAssoc, FTPGAssocCapstone, FTPGNeg — 0 sorry) -> multiplication has identity + right distributivity (FTPGMul, FTPGDilation, FTPGMulKeyIdentity, FTPGDistrib — 0 sorry) -> left distributivity (FTPGLeftDistrib — 0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment, not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). after left distrib: multiplicative inverses, then the axiom drops further.

**[cited + natural language] D ∈ {R, C, H}**: Solèr's theorem (Solèr 1995; Holland 1995 Bull AMS) characterizes {R, C, H} among *-division rings under orthomodular + infinite-dim + infinite ON sequence (`trichotomy.md`); the architecture admits all three branches, with which branch any given foam-instantiation runs on being realization-choice. lean works the R branch. neither Solèr nor the realization-choice framing is formalized in lean. residue: Solèr's hypotheses are discharged via fixed-point reasoning rather than independent derivation.

**[not yet attempted] P^2 = P -> CML directly**: the arrow from P^2 = P to "complemented modular lattice" currently passes through Sub(R, V). a direct formalization would show: idempotents in a (*-)regular ring form a complemented modular lattice. this would close the last natural-language gap in the loop. see von Neumann's continuous geometry.

### the FTPG bridge — where the axiom stands

lattice -> incidence geometry -> Desargues -> coordinates -> ring axioms -> FTPG

ring axioms proven: additive group (comm, assoc, identity, inverses), multiplicative identity, zero annihilation, right distributivity, left distributivity (0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment — not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). remaining after left distrib: multiplicative inverses. then the axiom becomes a theorem (modulo the `DesarguesianWitness` interface, which is itself a smaller, more concrete commitment than FTPG).

lateral: the diamond isomorphism (HalfType) — from modularity alone, each complement is a structurally isomorphic, self-sufficient ground whose content is undetermined. state-independence is a lattice theorem, pre-bridge.

### cross-examinations of architectural claims

beyond the core deductive chain, lean files that cross-examine specific architectural claims and render the discipline at the construction level:

- **HalfType.lean** — the half-type theorem as a constructed object (`HalfType` structure + `half_type` constructor). bin-1 deaxiomatization of the previously-asserted "the diamond isomorphism IS the half-type theorem." packages the diamond iso with modularity- and complementedness-inheritance into a single named formal object.

- **ReaderCommitment.lean** — cross-examines `framing/architecture.md`'s "the reader's commitment" section. `ObserverWitness` is the bin-2 typed pluggable interface (DesarguesianWitness-shape) for the step-1 handshake (observer → Hilbert space); `ReaderCommitment` + `ReaderCommitment.canonical` constructs steps 2-4 via Mathlib's spectral theorem; step-5 PMF construction sketched as downstream (requires density-operator conditions).

- **Resolver.lean** — the dynamic structure of reader commitments. `PathTypeDebt`, `CommitmentState`, `CommitmentState.IsResolved` (resolver-shape fixed point as discharged debt), and the `encounter` operation + `encounter_safe` theorem. the metabolisis operation that animates the full dynamics is open.
