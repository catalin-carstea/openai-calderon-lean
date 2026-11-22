module

public import Proof.CalderonN.LinearLaplacian

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

/-! LinearGreen from the checked 3D Theorem 3.1 release 55d37bfe, with arbitrary ambient dimension. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal

namespace CalderonN

variable {n : ℕ} [NeZero n]

@[expose] def linearPullbackGreen (G : (X n) × (X n) → ℝ) (A : (X n) ≃L[ℝ] (X n)) (q : (X n) × (X n)) : ℝ :=
  G (A q.1, A q.2)

private theorem map_volume_linearChart (A : (X n) ≃L[ℝ] (X n)) :
    (volume : Measure (X n)).map A.toHomeomorph.toMeasurableEquiv =
      ENNReal.ofReal (|(coordinateMatrix A.toContinuousLinearMap).det|⁻¹) • volume := by
  change (volume : Measure (X n)).map A.toContinuousLinearMap.toLinearMap = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    (by rw [← coordinateMatrix_det_eq]; exact coordinateMatrix_det_ne_zero A),
    ← coordinateMatrix_det_eq A.toContinuousLinearMap, abs_inv]

private theorem locallyIntegrableOn_linearPullback {Ω : Set (X n)} (hΩ : IsOpen Ω)
    {f : (X n) → ℝ} (hf : LocallyIntegrableOn f Ω) (A : (X n) ≃L[ℝ] (X n)) :
    LocallyIntegrableOn (f ∘ A) (A ⁻¹' Ω) := by
  let E := A.toHomeomorph.toMeasurableEquiv
  apply (locallyIntegrableOn_iff (hΩ.preimage A.continuous).isLocallyClosed).mpr
  intro K hKΩ hK
  have hI : IntegrableOn f (E '' K) volume :=
    hf.integrableOn_compact_subset (by rintro _ ⟨z, hz, rfl⟩; exact hKΩ hz) (hK.image A.continuous)
  have hM : IntegrableOn f (E '' K) ((volume : Measure (X n)).map E) := by
    rw [map_volume_linearChart]
    unfold IntegrableOn at *
    rw [Measure.restrict_smul]
    exact hI.smul_measure ENNReal.ofReal_ne_top
  have h := (integrableOn_map_equiv E).mp hM
  rwa [E.injective.preimage_image] at h

/-- The actual Green kernel transforms by composition in both coordinates.
The volume determinant cancels the Jacobian in the same weak law. -/
theorem GreenGerm.linearPullback {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : (MetricField n)}
    (hg : SmoothMetric Ω g) {G : (X n) × (X n) → ℝ} (hG : GreenGerm Ω g G) (A : (X n) ≃L[ℝ] (X n)) :
    GreenGerm (A ⁻¹' Ω) (linearPullbackMetric g A) (linearPullbackGreen G A) := by
  let T : Set (X n) := A ⁻¹' Ω
  let E := A.toHomeomorph.toMeasurableEquiv
  let J := |(coordinateMatrix A.toContinuousLinearMap).det|
  have hJ : 0 < J := abs_pos.mpr (coordinateMatrix_det_ne_zero A)
  have hT : IsOpen T := hΩ.preimage A.continuous
  have hmap : MapsTo (fun q : (X n) × (X n) => (A q.1, A q.2)) (OffDiagonal T) (OffDiagonal Ω) :=
    fun q hq => ⟨hq.1, hq.2.1, fun h => hq.2.2 (A.injective h)⟩
  have hdiff : ContDiff ℝ ∞ (fun q : (X n) × (X n) => (A q.1, A q.2)) :=
    (A.toContinuousLinearMap.contDiff.comp contDiff_fst).prodMk
      (A.toContinuousLinearMap.contDiff.comp contDiff_snd)
  refine ⟨hG.1.comp hdiff.contDiffOn hmap, fun q hq => hG.2.1 _ (hmap hq), ?_⟩
  intro y hy
  refine ⟨locallyIntegrableOn_linearPullback hΩ (hG.2.2 (A y) hy).1 A, ?_⟩
  intro φ hφ hφc hφT
  let Φ : (X n) → ℝ := φ ∘ A.symm
  have hΦ : ContDiff ℝ ∞ Φ := hφ.comp A.symm.toContinuousLinearMap.contDiff
  have hΦc : HasCompactSupport Φ := hφc.comp_homeomorph A.symm.toHomeomorph
  have hΦΩ : tsupport Φ ⊆ Ω := by
    rw [show Φ = φ ∘ A.symm.toHomeomorph from rfl, tsupport_comp_eq_preimage φ A.symm.toHomeomorph]
    intro z hz
    have hz' : A (A.symm z) ∈ Ω := hφT hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz'
  let H (z : (X n)) := G (z, A y) * (-laplace g Φ z) * chartVolume g z
  have hH : (∫ z in Ω, H z) = Φ (A y) :=
    (hG.2.2 (A y) hy).2 Φ hΦ hΦc hΦΩ
  have hcomp : Φ ∘ A = φ := funext fun z => congrArg φ (A.symm_apply_apply z)
  have hchange : (∫ x in T, H (A x)) = J⁻¹ * ∫ z in Ω, H z := by
    have h := (setIntegral_map_equiv (μ := (volume : Measure (X n))) E H Ω).symm
    rw [map_volume_linearChart, Measure.restrict_smul, integral_smul_measure,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hJ.le), smul_eq_mul] at h
    exact h
  calc
    _ = ∫ x in T, J * H (A x) := by
      apply setIntegral_congr_fun hT.measurableSet
      intro x hx
      have hLaplace := laplace_linearPullback hΩ hg A hΦ.contDiffOn (show A x ∈ Ω from hx)
      rw [hcomp] at hLaplace
      change linearPullbackGreen G A (x,y) * (-laplace (linearPullbackMetric g A) φ x) *
        chartVolume (linearPullbackMetric g A) x = _
      rw [linearPullbackGreen, hLaplace, linearPullbackMetric_volume]
      dsimp [J, H]
      ring
    _ = Φ (A y) := by rw [integral_const_mul, hchange, ← mul_assoc, mul_inv_cancel₀ hJ.ne', one_mul, hH]
    _ = φ y := congrArg φ (A.symm_apply_apply y)

end CalderonN
