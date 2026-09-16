import FourierMultiplierRigidity.SeedBridge

/-!
# Theorem A

This file completes the classification.  `theoremA` states that a
reality-compatible multiplier symbol is universally orthogonal to the Euler
convective nonlinearity on real mean-zero divergence-free trigonometric
polynomials exactly when it is the restriction of `A + B curl + curl B` for
constant real symmetric `A` and `B`.

Sufficiency is `hasGeneratorForm_universalCancellation`, proved in the root
module.  Necessity is `universalCancellation_hasGeneratorForm`, assembled here
from:

* `universal_hasActiveTriadCancellation` — phase polarization (root module);
* `seedConstraints_of_triadCancellation` — the semantic seed bridge
  (`SeedBridge`);
* `seed_parameter_is_generator` — the rank-144 certificate (root module),
  yielding the twelve generator parameters;
* `vanishes_on_unitCube` together with `vanishes_everywhere_of_unitCube` — the
  difference symbol has zero seed encoding, hence vanishes on the coordinate
  unit cube, and lattice propagation carries that to every nonzero mode.

## Trust

Everything in this file and in `SeedBridge` is kernel-checked.  `theoremA`
nevertheless depends on seven `native_decide` axioms, inherited through
`seed_parameter_is_generator` from the rank and inverse certificates for the
`144 x 144` modular minor.  See `lean/README.md`.
-/

namespace FourierMultiplierRigidity
open SeedCertificate
set_option maxRecDepth 4000000

theorem seed_frame_norm_ne_zero : ∀ m ∈ List.range 13, ∀ i ∈ List.range 2,
    SeedCertificate.dot (seedFrameIVec m i) (seedFrameIVec m i) ≠ 0 := by decide

theorem seedFrameNorm_ne_zero (m i : Nat) (hm : m < 13) (hi : i < 2) :
    seedFrameNorm m i ≠ 0 := by
  unfold seedFrameNorm
  exact_mod_cast seed_frame_norm_ne_zero m (List.mem_range.mpr hm) i (List.mem_range.mpr hi)

/-- Seed encoding is additive in the symbol, so a difference symbol encodes as
the difference of encodings. -/
theorem seedEncoding_difference (R : MultiplierSymbol) (A B : RMatrix) :
    seedEncoding (differenceSymbol R A B).map =
      seedEncoding R.map - seedEncoding (generatorMap A B) := by
  funext col
  simp only [seedEncoding, differenceSymbol, Pi.sub_apply, LinearMap.sub_apply]
  split <;> simp [Complex.sub_re, Complex.sub_im, sub_div]

/-- A zero encoding kills both frame blocks at every seed mode. -/
theorem blockValue_eq_zero (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (henc : seedEncoding D = 0) (m : Fin 13) (i : Fin 2) :
    blockValue D m.val i.val = 0 := by
  funext o
  have h0 := congrFun henc (colEquiv (m, wEquiv (o, i, 0)))
  have h1 := congrFun henc (colEquiv (m, wEquiv (o, i, 1)))
  rw [seedEncoding_col' D m o i 0] at h0
  rw [seedEncoding_col' D m o i 1] at h1
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, if_true] at h0 h1
  have hn := seedFrameNorm_ne_zero m.val i.val m.isLt i.isLt
  have hre : (blockValue D m.val i.val o).re = 0 := by
    field_simp at h0
    simpa using h0
  have him : (blockValue D m.val i.val o).im = 0 := by
    field_simp at h1
    simpa using h1
  exact Complex.ext hre him

/-- Hence the symbol vanishes on the whole transverse fiber of a seed mode. -/
theorem vanishesAt_seedMode (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (henc : seedEncoding D = 0) (m : Fin 13) : VanishesAt D (seedMode m.val) := by
  intro v hv
  rw [seed_frame_decomposition m v hv, map_add, map_smul, map_smul]
  have e0 : D (seedMode m.val) (seedFrameComplex m.val 0) = 0 := by
    simpa [seedFrameComplex, blockValue] using blockValue_eq_zero D henc m 0
  have e1 : D (seedMode m.val) (seedFrameComplex m.val 1) = 0 := by
    simpa [seedFrameComplex, blockValue] using blockValue_eq_zero D henc m 1
  rw [e0, e1]
  simp

/-- Every nonzero mode of the coordinate unit cube is a seed mode. -/
theorem exists_seed_of_unitCube (k : LatticeVec) (hk : k ≠ 0) (hc : InUnitCube k) :
    ∃ y ∈ seed, latticeOfIVec y = k := by
  refine ⟨(k 0, k 1, k 2), ?_, ?_⟩
  · have h0 : k 0 = -1 ∨ k 0 = 0 ∨ k 0 = 1 := by have := hc 0; omega
    have h1 : k 1 = -1 ∨ k 1 = 0 ∨ k 1 = 1 := by have := hc 1; omega
    have h2 : k 2 = -1 ∨ k 2 = 0 ∨ k 2 = 1 := by have := hc 2; omega
    have hne : ¬(k 0 = 0 ∧ k 1 = 0 ∧ k 2 = 0) := by
      rintro ⟨a, b, c⟩
      apply hk
      funext i
      fin_cases i <;> simpa
    rcases h0 with h0 | h0 | h0 <;> rcases h1 with h1 | h1 | h1 <;>
      rcases h2 with h2 | h2 | h2 <;> rw [h0, h1, h2] <;>
      first
        | decide
        | exact absurd ⟨h0, h1, h2⟩ hne
  · funext i
    fin_cases i <;> simp [latticeOfIVec, latticeVec]

theorem vanishes_on_unitCube (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (hreal : RealityCompatibleMap D) (henc : seedEncoding D = 0) :
    ∀ k, k ≠ 0 → InUnitCube k → VanishesAt D k := by
  intro k hk hc
  obtain ⟨y, hy, hyk⟩ := exists_seed_of_unitCube k hk hc
  have hm := seed_modeIndex_lt y hy
  have hmode := seedMode_modeIndex y hy
  rcases seed_rep_dichotomy y hy with h | ⟨_, h⟩
  · have hpos : latticeOfIVec y = seedMode (modeIndex y) := by
      rw [hmode]; conv_lhs => rw [h]
    rw [← hyk, hpos]
    exact vanishesAt_seedMode D henc ⟨modeIndex y, hm⟩
  · have hneg : latticeOfIVec y = -(seedMode (modeIndex y)) := by
      rw [hmode]; conv_lhs => rw [h, latticeOfIVec_neg]
    rw [← hyk, hneg]
    exact vanishesAt_neg_of_reality D hreal _
      (vanishesAt_seedMode D henc ⟨modeIndex y, hm⟩)

/-! ## Theorem A -/

/-- **Necessity.**  Universal cancellation forces the classified generator
form on every nonzero transverse Fourier fiber. -/
theorem universalCancellation_hasGeneratorForm (R : MultiplierSymbol)
    (hR : UniversalCancellation R) : HasGeneratorForm R := by
  have htriad : HasActiveTriadCancellation R.map :=
    universal_hasActiveTriadCancellation R hR
  have hreal : RealityCompatibleMap R.map := R.realityCompatible
  obtain ⟨g, hg⟩ :=
    seed_parameter_is_generator (seedEncoding R.map)
      (seedConstraints_of_triadCancellation R.map hreal htriad)
  have hAsym : (generatorAOf g).transpose = generatorAOf g := generatorAOf_symmetric g
  have hBsym : (generatorBOf g).transpose = generatorBOf g := generatorBOf_symmetric g
  have hD : seedEncoding (differenceSymbol R (generatorAOf g) (generatorBOf g)).map = 0 := by
    rw [seedEncoding_difference, seedEncoding_generator g, hg, sub_self]
  have hDreal : RealityCompatibleMap
      (differenceSymbol R (generatorAOf g) (generatorBOf g)).map :=
    (differenceSymbol R (generatorAOf g) (generatorBOf g)).realityCompatible
  have hDtriad : HasActiveTriadCancellation
      (differenceSymbol R (generatorAOf g) (generatorBOf g)).map :=
    universal_hasActiveTriadCancellation _
      (difference_universalCancellation R _ _ hR hAsym hBsym)
  have hall := vanishes_everywhere_of_unitCube _ hDtriad hDreal
    (vanishes_on_unitCube _ hDreal hD)
  refine ⟨generatorAOf g, generatorBOf g, hAsym, hBsym, ?_⟩
  intro k hk v hv
  have hz : R.map k v - generatorMap (generatorAOf g) (generatorBOf g) k v = 0 :=
    hall k hk v hv
  exact sub_eq_zero.mp hz

/-- **Theorem A.**  A reality-compatible multiplier symbol is universally
orthogonal to the Euler convective nonlinearity on real mean-zero
divergence-free trigonometric polynomials if and only if it is the restriction
of `A + B curl + curl B` for constant real symmetric `A`, `B`. -/
theorem theoremA (R : MultiplierSymbol) :
    UniversalCancellation R ↔ HasGeneratorForm R :=
  ⟨universalCancellation_hasGeneratorForm R, hasGeneratorForm_universalCancellation R⟩

end FourierMultiplierRigidity
