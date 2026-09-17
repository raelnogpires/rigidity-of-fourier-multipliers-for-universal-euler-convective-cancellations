# Lean formalization status

This directory contains a Lean 4.33.1 / Mathlib 4.33.1 formalization of the
Fourier-multiplier rigidity manuscript. Build it from the repository root
with the repository-local Elan installation:

```sh
ELAN_HOME="$PWD/.lean-toolchain-local" .lean-toolchain-local/bin/lake build
```

Setting `ELAN_HOME` is required, not cosmetic: a bare `lake` resolves the
default toolchain directory instead and will try to re-download Lean.

## What is proved

**Theorem A is proved**, in `FourierMultiplierRigidity/TheoremA.lean`:

```lean
theorem theoremA (R : MultiplierSymbol) :
    UniversalCancellation R ↔ HasGeneratorForm R
```

A reality-compatible multiplier symbol is universally orthogonal to the Euler
convective nonlinearity on real mean-zero divergence-free trigonometric
polynomials if and only if it is the restriction of `A + B curl + curl B` for
constant real symmetric `A`, `B`. Uniqueness of the pair is
`generator_witnesses_unique`.

**Corollary B is proved**, in `FourierMultiplierRigidity/CorollaryB.lean`:

```lean
theorem corollaryB (R : MultiplierSymbol) (hsol : HasSolenoidalOutput R) :
    UniversalCancellation R ↔ HasScalarForm R
```

Adding the range condition collapses the twelve-parameter family to
`R (k) = c I + d curl` for two real constants — energy and helicity are the
only possibilities, and Hermiticity on every nonzero-mode block is forced by
the cubic identity rather than assumed.

The supporting results are formalized as well: Theorem A⁰ includes the
exact real zero block; Corollary C is the normalized integral of an explicit
finite Fourier contraction; Theorem D's three scalar count bounds follow
from rank-nullity and its Hermitian Boolean seed is a typed `26 × 28` matrix
of nullity two; and `LocalSpectra.lean` proves the geometric frame formulas,
Gram spectra, multiplicity-four observation, route bounds, unstable family,
and stability modulo the exact kernel.

The repaired source contains no admitted proofs. A successful build is
required to establish that its new proof scripts elaborate. The development is
not uniformly kernel-checked: the source contains twenty-one `native_decide`
invocations, which the axiom report collapses to eleven distinct axioms. Seven
of them are reached by `theoremA` and `corollaryB` through `SeedCertificate`;
the remaining four are reached only by the Boolean-seed rank and nullity
theorems through `SolenoidalSeedCertificate`, and the two sets are disjoint.
The original classification and the separate Boolean-seed computation
therefore have different dependency graphs; use the axiom report rather than
conflating them.

For the Hermitian Boolean seed, the mandatory exact verifier
`verification/verify_solenoidal_seed_semantics.py` reconstructs all 26
selected rows from explicit signed triads, transverse polarizations, and
phase choices, and checks them against `booleanSeedMatrixZ` up to nonzero row
scaling. This closes the executable physical-to-matrix provenance gap. The
corresponding bridge is not yet an internal kernel-checked Lean theorem, so
the matrix rank/nullity theorem and the external semantic reconstruction must
not be described as one kernel proof.

## Module layout

| Module | Contents |
|---|---|
| `FourierMultiplierRigidity.lean` | generator algebra, triadwise sufficiency, phase polarization, raw-recipient lemmas, lattice propagation, and the rank-144 seed certificate |
| `FourierMultiplierRigidity/SeedCertificate.lean` | the unit-cube constraint matrix, reconstructed in Lean, and its rank over `ZMod 101` |
| `FourierMultiplierRigidity/SeedBridge.lean` | the semantic bridge tying those rows to the actual triad identity |
| `FourierMultiplierRigidity/TheoremA.lean` | necessity, and the final iff |
| `FourierMultiplierRigidity/CorollaryB.lean` | solenoidal rigidity: `R = c I + d curl` |
| `FourierMultiplierRigidity/NonVacuity.lean` | a witness showing the classification is not empty |
| `FourierMultiplierRigidity/AnisotropicCorollary.lean` | Actual second-order operator bridge, longitudinal symbol defect and SV cancellation |
| `FourierMultiplierRigidity/CorollaryC.lean` | Correct finite-Fourier SV functional, inverse curl, pullback bridge, full classification and solenoidal specialization |
| `FourierMultiplierRigidity/SolenoidalPropagation.lean` | Boolean-seed bootstrap and propagation; general arbitrary-length unequal-triad-ordering propagation (`vanishes_of_validOrdering`) and a concrete step beyond the unit cube (`vanishes_at_stepBeyondUnitCube`) |
| `FourierMultiplierRigidity/SolenoidalSeedCertificate.lean` | Typed `26 × 28` Hermitian Boolean-seed matrix, certified rank 26 and nullity 2; external exact row semantics verifier |
| `FourierMultiplierRigidity/FiniteCertificateOptimality.lean` | Matrix-level exact certificates and sharp `8M-2`, `4M-2`, `12M-12` scalar lower bounds |
| `FourierMultiplierRigidity/TheoremD.lean` | Qualitative classification, propagation, and finite scalar optimality theorem |
| `FourierMultiplierRigidity/TheoremAZero.lean` | All-mode classification and the exact arbitrary real zero block |
| `FourierMultiplierRigidity/PhysicalSpaceCorollaryC.lean` | Explicit contraction Fourier series, normalized torus integral, and Corollary C |
| `FourierMultiplierRigidity/LocalSpectra.lean` | Geometric frame bridge, Gram spectra and multiplicities, conditioning, stability modulo kernel |
| `FourierMultiplierRigidity/TorusIntegral.lean` | Normalized torus mean as an iterated interval integral, character orthogonality, term-by-term integration of trigonometric polynomials |
| `FourierMultiplierRigidity/PhysicalSpaceIntegral.lean` | Velocity and vorticity as functions, vorticity by real differentiation, the pointwise strain contraction, its torus integral, and physical-space integration by parts |
| `FourierMultiplierRigidity/SmoothExtension.lean` | Smooth solenoidal fields, absolute convergence of the resonant series, the classification on that class, and a member with infinite spectrum |
| `FourierMultiplierRigidity/CertificateStability.lean` | The Boolean-seed observation map on Euclidean parameter space and its stability constant |
| `FourierMultiplierRigidity/SolenoidalSeedBridge.lean` | Triad, polarization and phase provenance of every Boolean-seed row, recomputed in Lean and checked against the certificate matrix |
| `FourierMultiplierRigidity/SolenoidalSeedPlusOneStepBridge.lean` | Four explicit named test fields at one mode beyond the Boolean seed (`(1,-1,-1)`), proved to have vanishing Euler cubic pairing against every admissible symbol; does not extend the integer-row/rank certificate |

`SeedBridge`, `TheoremA`, `CorollaryB` and `NonVacuity` import the root module, so they are
unreachable from its own import graph and are listed explicitly under `globs`
in `lakefile.toml`.

## Kernel-checked results

These depend only on `propext`, `Classical.choice` and `Quot.sound`:

- the three-dimensional dot and cross-product identities used by the proof;
- Lemma 3.2 (scalarity from lattice directions), in a slightly stronger form
  that does not assume symmetry (`scalarity_from_lattice_directions`);
- the split real form of Proposition 3.1 (`uniqueness_of_split_generator`);
- uniqueness of the two symmetric generator matrices on all nonzero transverse
  complex fibers (`generator_witnesses_unique`);
- finite-support Fourier definitions of real mean-zero divergence-free
  trigonometric fields, multiplier symbols, convolution, and the cubic form;
- reality compatibility of the classified family `A + B C_k + C_k B`;
- the zero-order, first-order, and combined generator cancellations on every
  Fourier triad, and the six-permutation finite-sum argument connecting triad
  cancellation to the convolutional cubic form;
- **sufficiency**: every symmetric generator has universal cancellation for
  every admissible finite Fourier field, including an arbitrary invisible
  zero-mode block (`hasGeneratorForm_universalCancellation`);
- **phase polarization**: universal cancellation on real fields yields the
  local complex active-triad identity (`universal_hasActiveTriadCancellation`);
- the raw-recipient parametrization, the local two-triad determination rule,
  and conjugation/reality transport of fiberwise vanishing;
- the well-founded propagation theorem using the manuscript's `ℓ¹`-shell order,
  with concrete parent-pair certificates for every nonzero lattice mode outside
  the cube (`vanishes_everywhere_of_unitCube`);
- the two-frame decomposition of a transverse fiber vector at each of the
  thirteen seed modes (`seed_frame_decomposition`);
- **non-vacuity** (`sqNormSymbol_not_generator`): `R (k) = ‖k‖² I` is
  reality-compatible but not a generator, because generators are affine in `k`.
  Through `theoremA` this yields `exists_nonvanishing_cubicForm`, so
  `UniversalCancellation` is a proper restriction and `TrigField` really does
  supply witnesses — neither side of the iff is trivially satisfied;
- **the semantic seed bridge** (`seedConstraints_of_triadCancellation`): a
  reality-compatible symbol with active triad cancellation satisfies every
  selected constraint of the unit-cube matrix. This is what makes the rank
  computation mean something about symbols rather than about an arbitrary
  integer matrix. All of `SeedBridge` is kernel-checked, including the finite
  lookup facts about `seed`, `triads` and `polarizationTriples`, which use
  `decide` rather than `native_decide`.
- **general unequal-triad-ordering propagation** (`vanishes_of_validOrdering`
  in `SolenoidalPropagation.lean`): the six hard-coded bootstrap steps
  (`step1_cert`–`step6_cert`) are each one instance of
  `solenoidal_propagation_step`, chained by hand for the specific six modes
  needed to reach the unit cube. `vanishes_of_validOrdering` generalizes this
  to *any* finite sequence of unequal-triad steps of *any* length, proved by
  induction on the sequence: given active triad cancellation, solenoidal
  output, reality compatibility, and vanishing on a starting seed, vanishing
  propagates along every step of a valid ordering (`ValidOrderingFrom`),
  regardless of how long the ordering is or how many modes `M` it reaches.
  This is the qualitative content of Theorem D's admissible unequal-triad
  orderings (Definition 5.1) for general `M`, not just the seven-mode
  bootstrap case. `vanishes_at_stepBeyondUnitCube` instantiates it at one
  concrete new step, `(2,-1,-1) = (1,-1,-1) + (1,0,0)`, reaching a mode
  strictly outside the coordinate unit cube — demonstrating the general
  theorem covers genuinely new geometric observations, not only the six it
  was extracted from. Both theorems are fully kernel-checked, depending only
  on `propext`, `Classical.choice` and `Quot.sound` (verified by
  `#print axioms`); no `native_decide` is introduced.

  **What this does not close:** the general theorem is qualitative — it
  propagates the abstract `VanishesAt D k` predicate (vanishing on the
  transverse fiber, i.e. all of the block's real parameters), not an
  explicit numbered matrix row. It does not construct, for an arbitrary
  admissible ordering, an explicit `TriadDatum`-style list of test fields
  together with a `native_decide`- or `decide`-checked rank/nullity theorem
  for the resulting extended integer matrix, the way `SolenoidalSeedBridge`
  does for the 26 Boolean-seed rows specifically. Building that — an
  arbitrary-`M` generalization of `SolenoidalSeedCertificate.lean` and
  `SolenoidalSeedBridge.lean`'s `Fin 7`/`Fin 28`-indexed bookkeeping to
  `Fin M`/`Fin (4M-2)` — remains open and is the largest remaining piece of
  Theorem D's formalization.
- **explicit test fields at one mode beyond the Boolean seed**
  (`SolenoidalSeedPlusOneStepBridge.lean`): four named `TriadDatum`s at
  `(1,-1,-1)` (two transverse polarizations at the target, `(0,-1,1)` and
  `(-2,-1,-1)`, times two phases), built on the same unequal-length parent
  pair as `step1_cert`. `testPairing_zero_of_datumOK` generalizes the
  semantic-bridge argument behind `SolenoidalSeedBridge.rowPairing_zero`
  (`testPairing_eq_brackets`, `bracket_pos_zero`, `bracket_neg_zero`) from
  "any datum recorded in `booleanProvenance`" to "any datum satisfying the
  same two decidable conditions" — those conditions never referenced the
  Boolean seed's size, so no new mathematics was needed, only dropping the
  membership premise. `stepBeyond_testPairing_zero` instantiates it at the
  four new fields: each has vanishing Euler cubic pairing
  (`testPairing D dat = 0`) against every symbol with active triad
  cancellation, matching the manuscript's Lemma 4.1/5.3 construction
  literally, not just through the abstract `VanishesAt` predicate. Fully
  kernel-checked (`propext`, `Classical.choice`, `Quot.sound` only).

  **What this still does not close:** these are concrete named observations,
  not integer matrix rows. `rowPairing`, `booleanEncoding`, and the Hermitian
  block identities that turn an integer row into a symbol statement are
  hardwired to `colEquiv28 : Fin 7 × Fin 4 ≃ Fin 28` throughout
  `SolenoidalSeedBridge.lean`; extending *that* to an 8-mode
  `Fin 8 × Fin 4 ≃ Fin 32` indexing — so the new fields' coefficients become
  rows of an explicit `30 × 32` matrix with a `native_decide`-checked
  rank/nullity certificate matching `4M-2 = 30` at `M = 8` — is a further,
  separate undertaking, and remains open.

## Compiler-trusted results

Eleven `native_decide` calls discharge the rank-144 claim over `ZMod 101` and
the explicit inverse certificate for the selected `144 × 144` modular minor.
`native_decide` evaluates compiled code rather than reducing in the kernel, so
these trust the Lean compiler, its runtime, and GMP. Each call site introduces
one axiom:

```
SeedCertificate.seed_rank._native.native_decide.ax_1_1
SeedCertificate.seed_rank_integer_reduction._native.native_decide.ax_1_1
SeedCertificate.selected_counts._native.native_decide.ax_1_1
SeedCertificate.selectedColumn_lt._native.native_decide.ax_1_1
SeedCertificate.selectedGenerator_counts._native.native_decide.ax_1_1
SeedCertificate.modular_minor_has_right_inverse._native.native_decide.ax_1_1
SeedCertificate.generator_minor_has_right_inverse._native.native_decide.ax_1_1
SeedCertificate.minorMatrixF_is_integer_reduction._native.native_decide.ax_1_1
SeedCertificate.selected_constraints_annihilate_generators._native.native_decide.ax_1_1
seedGeneratorSelectedRow._native.native_decide.ax_1
seedGeneratorSelectedColumn._native.native_decide.ax_1
```

`theoremA` and `corollaryB` inherit seven of these, through
`seed_parameter_is_generator`. So
the precise status is: **the entire analytic argument is kernel-checked, and
Theorem A holds modulo trusting the Lean compiler for one finite
linear-algebra computation.** No step is unformalized.

This is a deliberate trade-off: the inverse certificate is roughly three
million modular operations, not viable for kernel reduction. Shrinking the
certificate is the route to removing it. By contrast
`seedFrameIVec_eq_explicit`, a `13 × 2` lookup table, *was* moved back across
the boundary — it uses `decide +revert` and takes about three seconds, and had
it stayed on `native_decide` it would have contaminated all of `SeedBridge`.

**Attempted and ruled out:** converting `generator_minor_has_right_inverse`
(the smallest, self-contained `native_decide` call above — a `12 × 12`
matrix product over `Rat`, unrelated to the `704`-row fold behind the other
sites) to plain `decide`. This is not merely slow: the kernel's `Decidable`
reduction for `Rat` equality gets provably *stuck* mid-reduction, because
`Rat`'s arithmetic operations normalize through `Nat.gcd`, which is defined
by well-founded recursion and does not unfold under the kernel's WHNF
reduction — a size-independent obstruction, not a performance one.
`native_decide` sidesteps it by evaluating compiled code instead of
reducing in the kernel, which is exactly why every `Rat`-valued certificate
here (`generator_minor_has_right_inverse`,
`selected_constraints_annihilate_generators`,
`selectedGenerator_counts` indirectly) uses it, independent of size.

A second attempt tried `norm_num` instead of `decide`, since `norm_num`
verifies numeral arithmetic (including `Rat`) through its own certified
procedure rather than raw kernel `Decidable` reduction, and so does not hit
the `Nat.gcd` well-founded-recursion wall directly. It does not work either,
for a different reason: `norm_num`'s simp pass does not fully unfold the
`List.foldl insertQ []` driving `generatorPivotsQ` (the Gauss–Jordan pivot
selection over the `156`-row generator list) down to concrete numerals —
`generatorPivotsQ` stays symbolic, so `norm_num` never reaches an arithmetic
goal it could close. (`decide`, by contrast, *does* fully reduce that fold —
the earlier stuck point was strictly the final `Rat` arithmetic comparison,
not the fold.) So the two candidate replacement tactics fail at opposite
ends of the same pipeline: `decide` reduces the combinatorics but stalls on
`Rat` arithmetic; `norm_num` can do the arithmetic but does not perform the
combinatorial reduction.

A third, independent check ruled out the obvious escape from the `Rat`
obstruction: rewriting the pipeline to use `ZMod p` instead (integers with
cleared denominators, checked in a finite field). A minimal isolated test —
`(3 : ZMod 101)⁻¹ * 3 = 1` and `(37 : ZMod 101) * (37 : ZMod 101)⁻¹ = 1` by
plain `decide` — fails with the *identical* symptom: kernel reduction gets
stuck inside `ZMod.decidableEq`, not merely slow. `ZMod`'s field inverse
routes through the same class of extended-Euclidean, `Nat.gcd`-based
recursion as `Rat`'s normalizer. So the obstruction is not specific to
`Rat` — it is *any* certificate that needs a field inverse (`Rat`, `ZMod`,
or otherwise) evaluated by plain `decide` in current Mathlib. This rules out
"redesign the pipeline to use `ZMod` instead of `Rat`" as a fix: the
resulting certificate would hit the exact same wall, just with different
numerals. The only routes that would actually avoid this are ones that
never call a field inverse at all — e.g. an adjugate/cofactor identity
(`M * adjugate M = det M • I`, using only `+`, `-`, `*`) or fraction-free
(Bareiss) elimination — both combinatorially expensive to construct for a
`12 × 12` or `144 × 144` matrix and neither attempted here. Combined with
the independent scale obstruction on the `ZMod`-based `704`-row sites, no
tactic-level `decide` substitution is available anywhere in this
certificate; removing `native_decide` here remains open, and the viable
remaining routes are substantial reformulations, not tactic swaps.

Reproduce the split with:

```lean
#print axioms FourierMultiplierRigidity.theoremA
#print axioms FourierMultiplierRigidity.corollaryB
-- propext, Classical.choice, Quot.sound, and seven native_decide axioms

#print axioms FourierMultiplierRigidity.seedConstraints_of_triadCancellation
#print axioms FourierMultiplierRigidity.hasGeneratorForm_universalCancellation
-- propext, Classical.choice, Quot.sound
```

`#print axioms` is the authoritative check; prefer it over this list, which can
drift.

## Scope

`theoremA` and `corollaryB` are the main theorem package of the manuscript,
its Theorem A and Corollary B: the mean-zero unrestricted-output
classification, and the solenoidal collapse.

The finite-Fourier statements used by the manuscript are formalized. The
strain-vorticity functional is additionally realized as a genuine integral over
the three-torus, and extended to the smooth solenoidal fields, meaning those
whose Fourier coefficients decay faster than every polynomial.

Two things are deliberately out of scope. A Sobolev completion at finite
regularity is not formalized. Neither is the identification of the extended
functional with the torus integral of the smooth field itself: on that class it
is pinned to physical space only as the limit of the torus integrals of its
truncations.


## Repair build and trust report

The Corollary C/E declarations live in the namespace
`FourierMultiplierRigidity.StrainVorticity`. Their proof scripts are intended
to close the finite Fourier pullback and matrix-symbol bridge. They do not
formalize a physical-space PDE theory or a new regularity criterion.

```sh
lake build
lake env lean lean/CheckAxioms.lean
python3 -B verification/verify_strain_vorticity_pullback.py
python3 -B verification/verify_lean_source_hygiene.py
```

On a fresh machine, install the toolchain pinned in `lean-toolchain` using
Elan, then run `lake exe cache get` before the build. The repository-local
Elan command above applies only if that optional local installation exists.
The observed results of the most recent build and axiom report are recorded in
the verification notes shipped with the manuscript supplement; source
inspection alone is not a build.
