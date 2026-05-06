## vocabulary

precise terms used throughout the derivations. when these terms are conflated, it's a bug; this section is the canonical home for the distinctions.

- **slice**: the rank-3 subspace each observer is committed to at birth — a Grassmannian point in Gr(3, d). static by definition. "the slice cannot change from within the map" (`inhabitation.md`); slice change requires recommitment, which is outside the map.

- **foam state**: the dynamic part of the system. concretely, the basis matrices / accumulated transports for each observer in U(d)^N. evolves under writes; encodes the system's accumulated history.

- **frame**: the time-varying projection associated with an observer at moment t. derived from the foam state acting on the birth slice (concretely: conjugating the slice's projection by the accumulated transport). evolves under non-inert writes — this is what "recedes" in the frame-recession theorem (`Dynamics.lean`: second-order overlap rate is `-‖[W, P]‖²`).

- **P**: the projection operator used in formal contexts. in lattice contexts (`half_type`, `interiority`, `channel_capacity`'s qualitative section, `ground`'s loop diagram), `P` denotes the slice as a lattice element / subspace — static. in dynamic / writing-map contexts (`writing_map`, `Dynamics.lean`, `inhabitation`'s recession discussion), `P` denotes the frame at time t — evolving. context disambiguates; where it doesn't, the spec should say "slice" or "frame" explicitly.

- **observer**: a bubble in its measuring role — a basis matrix and its slice, with the foam-state evolution that goes with it. not a separate entity from the bubble, a role the bubble plays relative to other bubbles.

- **witness**: an observer *explicitly without consideration of any observer-side state or type*. from the outside, for any given observation, indistinguishable from an amniscient (nb: not omniscient; see definition of "amniscience" in the architecture section) observer.

- **agent**: an observer *with* explicit consideration of its specific observer-side state and type. a non-amniscient observer.

- **line**: whatever provides state-independent input to a foam. intuitively, "a line of sight" with side-effects, the dynamical role of "eye contact", not an observer in itself. the line's ontological establishment is perspectival according to informational independence (`channel_capacity`, "decorrelation horizon").
