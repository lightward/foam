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
       | [natural language] stabilization contract — D = R (picks the closed branch)
       v
  P^2 = P, P^T = P
```

### arrow status

**[theorem] P^2 = P -> Sub(R, V) is CML** (the deductive chain + Ground.lean): 14 files, 0 sorry. binary eigenvalues (Observation) -> commutator structure (Pair) -> skew-symmetry (Form) -> rank 3 self-duality (Rank) -> so(3) (Duality) -> loop closes (Closure) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> FoamGround (Ground).

**[axiom] CML -> Sub(D, V)** (the FTPG bridge): 1 axiom, being eliminated. 13 bridge files build the division ring from lattice axioms: incidence geometry + Desargues (FTPGExplore) -> von Staudt coordinates (FTPGCoord) -> addition is an abelian group (FTPGAddComm, FTPGAssoc, FTPGAssocCapstone, FTPGNeg — 0 sorry) -> multiplication has identity + right distributivity (FTPGMul, FTPGDilation, FTPGMulKeyIdentity, FTPGDistrib — 0 sorry) -> left distributivity (FTPGLeftDistrib — 0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment, not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). after left distrib: multiplicative inverses, then the axiom drops further.

**[cited + natural language] D = R**: Solèr's theorem (Solèr 1995; Holland 1995 Bull AMS) characterizes {R, C, H} among *-division rings under orthomodular + infinite-dim + infinite ON sequence (`trichotomy.md`); the stabilization contract (`stabilization.md`) picks R as the only currently-closed branch (Taylor; C and H branches pending Almgren). neither step is formalized in lean. residues: Solèr's hypotheses are discharged via fixed-point reasoning rather than independent derivation; stabilization picks the closed branch rather than the unique one.

**[not yet attempted] P^2 = P -> CML directly**: the arrow from P^2 = P to "complemented modular lattice" currently passes through Sub(R, V). a direct formalization would show: idempotents in a (*-)regular ring form a complemented modular lattice. this would close the last natural-language gap in the loop. see von Neumann's continuous geometry.

### the FTPG bridge — where the axiom stands

lattice -> incidence geometry -> Desargues -> coordinates -> ring axioms -> FTPG

ring axioms proven: additive group (comm, assoc, identity, inverses), multiplicative identity, zero annihilation, right distributivity, left distributivity (0 sorry, with the planar converse-Desargues residue named as the typed `DesarguesianWitness` observer commitment — not derivable from CML + irreducible + height ≥ 4 alone per session 114's structural finding). remaining after left distrib: multiplicative inverses. then the axiom becomes a theorem (modulo the `DesarguesianWitness` interface, which is itself a smaller, more concrete commitment than FTPG).

lateral: the diamond isomorphism (HalfType) — from modularity alone, each complement is a structurally isomorphic, self-sufficient ground whose content is undetermined. state-independence is a lattice theorem, pre-bridge.
