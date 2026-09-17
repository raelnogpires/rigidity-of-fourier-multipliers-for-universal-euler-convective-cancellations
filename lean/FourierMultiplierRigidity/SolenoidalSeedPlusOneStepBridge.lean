import FourierMultiplierRigidity.SolenoidalSeedBridge

/-!
# Explicit geometric observations at one mode beyond the Boolean seed

`SolenoidalSeedBridge.lean` records the 26 rows of the Hermitian Boolean-seed
matrix as explicit named test fields (`TriadDatum`s: a triad, three transverse
polarizations, three phases in `{1, i}`), recomputes their coefficients inside
Lean, and proves (`rowPairing_zero`) that each row's constraint vanishes for
every solenoidal, Hermitian, reality-compatible symbol with active triad
cancellation. This is the concrete content behind Theorem D's "geometric
observation family" for the seven-mode Boolean seed.

`SolenoidalPropagation.lean`'s `vanishes_of_validOrdering` proves the
*qualitative* counterpart for arbitrary further modes: if `D` vanishes on a
known set, it vanishes at any target reached by a valid unequal-triad step.
But that argument goes through the abstract `target_image_line_of_vanishing_parents`
lemma, not through a named, explicit test field.

This file gives the *explicit* counterpart at one concrete mode beyond the
Boolean seed: `(1,-1,-1)`, reached from the Boolean-seed parents `(1,0,0)` and
`(0,-1,-1)` (the same pair used by `step1_cert` in `SolenoidalPropagation.lean`).
Four named test fields — two transverse polarizations at the new mode times
two phases — are recorded exactly as `SolenoidalSeedBridge.lean` records the
existing 26, and each is proved to annihilate every admissible symbol.

## What this proves, precisely

For each of the four new `TriadDatum`s `newDat`, `testPairing D newDat = 0`
for every `D` with active triad cancellation: the *explicit* Euler cubic form
of this *named, concrete* divergence-free test field vanishes. This is proved
via `testPairing_zero_of_datumOK`, a direct generalization of the argument
behind `SolenoidalSeedBridge.rowPairing_zero`'s final steps
(`testPairing_eq_brackets`, `bracket_pos_zero`, `bracket_neg_zero`) from "any
recorded datum in `booleanProvenance`" to "any datum satisfying the same two
decidable hypotheses" — those hypotheses do not depend on the Boolean seed's
size, so the generalization needs no new mathematics, only dropping the
`booleanProvenance`-membership premise in favour of the same two `decide`
facts checked directly at the new data.

## What this does not prove

This does **not** produce an integer *row* comparable to
`booleanSeedMatrixZ`'s 26 rows, nor a rank/nullity certificate for a `30 × 32`
extended matrix. That direction — `rowPairing`, `booleanEncoding`, and the
Hermitian block identities that connect an integer row to a symbol pairing —
is hardwired to the Boolean seed's `Fin 7` block indexing
(`colEquiv28 : Fin 7 × Fin 4 ≃ Fin 28`) throughout `SolenoidalSeedBridge.lean`,
and extending it to `Fin 8` blocks would require re-deriving that indexing and
every theorem built on it. What is proved here is the same content one level
down: the named, concrete test fields exist and their Euler-cubic pairings
vanish, matching the manuscript's Lemma 4.1 (test field structure) and Lemma
5.3 (one-triad solenoidal determination) applied literally at this new mode,
rather than only through the abstract propagation predicate `VanishesAt`. The
integer-row/rank-certificate generalization remains open; see
`lean/README.md`.
-/

namespace FourierMultiplierRigidity.SolenoidalSeedBridge

open FourierMultiplierRigidity.SeedCertificate

/-! ## The generic semantic bridge, freed from `booleanProvenance` membership

`bracket_pos_zero`, `bracket_neg_zero` and `testPairing_eq_brackets` each take
a hypothesis `dat ∈ booleanProvenance` only to extract two decidable facts:
`datumOK dat = true` and `resonantTriples (modesOf dat) = expectedTriples dat`.
Neither fact, nor any step of their proofs, mentions the Boolean seed's size
or membership in the recorded list — they hold for any datum satisfying the
same two conditions, checked directly by `decide`. -/

private theorem bracket_pos_zero_of (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) {dat : TriadDatum}
    (hok : datumOK dat = true) :
    triadBracket D (latticeOfIVec dat.p) (latticeOfIVec dat.q) (latticeOfIVec dat.r)
      (cOfGVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a)))
      (cOfGVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u)))
      (cOfGVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v))) = 0 := by
  simp only [datumOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hres, hp⟩, hq⟩, hr⟩, hcross⟩, ha⟩, hu⟩, hv⟩ := hok
  refine htriad _ _ _ _ _ _ ?_ (latticeOfIVec_ne_zero hp) (latticeOfIVec_ne_zero hq)
    (latticeOfIVec_ne_zero hr) ?_ (transverse_amp ha _) (transverse_amp hu _)
    (transverse_amp hv _)
  · rw [← latticeOfIVec_add, ← latticeOfIVec_add, hres, latticeOfIVec_zero]
  · show Vec3.cross (latticeToReal (latticeOfIVec dat.q))
      (latticeToReal (latticeOfIVec dat.r)) ≠ 0
    rw [latticeToReal_latticeOfIVec, latticeToReal_latticeOfIVec, cross_realOfIVec]
    exact realOfIVec_ne_zero hcross

private theorem bracket_neg_zero_of (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) {dat : TriadDatum}
    (hok : datumOK dat = true) :
    triadBracket D (latticeOfIVec (neg dat.p)) (latticeOfIVec (neg dat.q))
      (latticeOfIVec (neg dat.r))
      (cOfGVec (gconjVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a))))
      (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u))))
      (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v)))) = 0 := by
  simp only [datumOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hres, hp⟩, hq⟩, hr⟩, hcross⟩, ha⟩, hu⟩, hv⟩ := hok
  refine htriad _ _ _ _ _ _ ?_ (latticeOfIVec_ne_zero (neg_ne_zero_IVec hp))
    (latticeOfIVec_ne_zero (neg_ne_zero_IVec hq))
    (latticeOfIVec_ne_zero (neg_ne_zero_IVec hr)) ?_ (transverse_amp_conj ha _)
    (transverse_amp_conj hu _) (transverse_amp_conj hv _)
  · rw [← latticeOfIVec_add, ← latticeOfIVec_add, neg_resonance hres,
      latticeOfIVec_zero]
  · show Vec3.cross (latticeToReal (latticeOfIVec (neg dat.q)))
      (latticeToReal (latticeOfIVec (neg dat.r))) ≠ 0
    rw [latticeToReal_latticeOfIVec, latticeToReal_latticeOfIVec, cross_realOfIVec]
    refine realOfIVec_ne_zero ?_
    rw [cross_neg_neg]
    exact hcross

private theorem testPairing_eq_brackets_of (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    {dat : TriadDatum} (hexp : resonantTriples (modesOf dat) = expectedTriples dat) :
    testPairing D dat =
      Complex.I * triadBracket D (latticeOfIVec dat.p) (latticeOfIVec dat.q)
          (latticeOfIVec dat.r)
          (cOfGVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a)))
          (cOfGVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u)))
          (cOfGVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v))) +
        Complex.I * triadBracket D (latticeOfIVec (neg dat.p))
          (latticeOfIVec (neg dat.q)) (latticeOfIVec (neg dat.r))
          (cOfGVec (gconjVec (gsmulVec (phaseOf dat.php) (gOfIVec dat.a))))
          (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phq) (gOfIVec dat.u))))
          (cOfGVec (gconjVec (gsmulVec (phaseOf dat.phr) (gOfIVec dat.v)))) := by
  unfold testPairing
  rw [hexp]
  rw [← six_perm_sum D dat.p dat.q dat.r, ← six_perm_sum D (neg dat.p) (neg dat.q)
    (neg dat.r)]
  simp only [expectedTriples, modesOf, List.map, List.sum_cons, List.sum_nil,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  ring

/-- **Generic semantic bridge.**  Any triad datum satisfying the same two
decidable conditions the recorded Boolean-seed rows satisfy — valid triad
data (`datumOK`) and the expected resonant-triple enumeration
(`resonantTriples_eq_expected`-style) — has vanishing test-field pairing
against every symbol with active triad cancellation. This generalizes the
argument behind `rowPairing_zero` one level below the integer row: it applies
to *any* named test field, not only the 26 recorded in `booleanProvenance`. -/
theorem testPairing_zero_of_datumOK (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) {dat : TriadDatum}
    (hok : datumOK dat = true)
    (hexp : resonantTriples (modesOf dat) = expectedTriples dat) :
    testPairing D dat = 0 := by
  rw [testPairing_eq_brackets_of D hexp, bracket_pos_zero_of D htriad hok,
    bracket_neg_zero_of D htriad hok]
  ring

/-! ## Four explicit test fields at the mode `(1,-1,-1)`

The target `(1,-1,-1) = (1,0,0) + (0,-1,-1)` is reached from the Boolean seed
by the same unequal-length, non-collinear parent pair as
`SolenoidalPropagation.step1_cert` (`|(1,0,0)|² = 1 ≠ 2 = |(0,-1,-1)|²`).
`frame (1,-1,-1) = [(0,-1,1), (-2,-1,-1)]` supplies the two transverse
polarizations at the target; `(0,0,1)` is transverse to `(1,0,0)` and
`(0,-1,1)` is transverse to `(0,-1,-1)`, fixed as the parents' polarizations
throughout. Two target polarizations times two phases (`1`, `i`) give four
named test fields. -/

def stepBeyondTarget : IVec := (1, -1, -1)

/-- The `TriadDatum.p` field must satisfy `p + q + r = 0` (the resonance
convention used throughout this file), so it is the *negative* of the target
mode reached by the parents below: `-(1,-1,-1) + (1,0,0) + (0,-1,-1) = 0`.
Transversality of a polarization to `p` is sign-invariant, so the target's own
frame vectors (computed at `(1,-1,-1)`, since `representative (-1,1,1) =
(1,-1,-1)`) still serve as the polarizations at `p`. -/
def stepBeyondTargetSigned : IVec := neg stepBeyondTarget
def stepBeyondParentQ : IVec := (1, 0, 0)
def stepBeyondParentR : IVec := (0, -1, -1)
def stepBeyondFrame0 : IVec := (0, -1, 1)
def stepBeyondFrame1 : IVec := (-2, -1, -1)
def stepBeyondPolQ : IVec := (0, 0, 1)
def stepBeyondPolR : IVec := (0, -1, 1)

def stepBeyondData : List TriadDatum :=
  [ ⟨stepBeyondTargetSigned, stepBeyondParentQ, stepBeyondParentR,
      stepBeyondFrame0, stepBeyondPolQ, stepBeyondPolR, false, false, false⟩,
    ⟨stepBeyondTargetSigned, stepBeyondParentQ, stepBeyondParentR,
      stepBeyondFrame0, stepBeyondPolQ, stepBeyondPolR, true, false, false⟩,
    ⟨stepBeyondTargetSigned, stepBeyondParentQ, stepBeyondParentR,
      stepBeyondFrame1, stepBeyondPolQ, stepBeyondPolR, false, false, false⟩,
    ⟨stepBeyondTargetSigned, stepBeyondParentQ, stepBeyondParentR,
      stepBeyondFrame1, stepBeyondPolQ, stepBeyondPolR, true, false, false⟩ ]

theorem stepBeyondData_datumOK :
    stepBeyondData.all datumOK = true := by decide

theorem stepBeyondData_resonance :
    stepBeyondData.all
        (fun dat => resonantTriples (modesOf dat) == expectedTriples dat) = true := by
  decide

/-- **Four explicit geometric observations beyond the Boolean seed.**  Each of
the four named test fields at `(1,-1,-1)` has vanishing Euler cubic pairing
against every solenoidal-output symbol with active triad cancellation. These
are concrete instances of the manuscript's Lemma 4.1/5.3 test-field
construction at a mode outside the original 26-row Boolean seed. -/
theorem stepBeyond_testPairing_zero (D : LatticeVec → CVec →ₗ[ℂ] CVec)
    (htriad : HasActiveTriadCancellation D) {dat : TriadDatum}
    (h : dat ∈ stepBeyondData) :
    testPairing D dat = 0 := by
  have hok := List.all_eq_true.mp stepBeyondData_datumOK dat h
  have hexp := eq_of_beq (List.all_eq_true.mp stepBeyondData_resonance dat h)
  exact testPairing_zero_of_datumOK D htriad hok hexp

end FourierMultiplierRigidity.SolenoidalSeedBridge
