module

public import Proof.CalderonN.DilationHarmonic

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Pointwise

/- Port of the chart Green dilation law from the 3D Theorem 3.1 release (55d37bfe). -/

namespace CalderonN

variable {n : ℕ}

/-- Under spatial dilation a volume-normalized Green kernel acquires the factor λ^(n−2). -/
def dilatedGreen (G : X n × X n → ℝ) (lam : ℝ) (p : X n × X n) : ℝ :=
  lam ^ (n - 2) * G (lam • p.1, lam • p.2)

private theorem scale_inverse_smul (lam : ℝ) (hlam : lam ≠ 0) (x : X n) :
    lam⁻¹ • (lam • x) = x := by rw [smul_smul, inv_mul_cancel₀ hlam, one_smul]

private theorem locIntegrable_dilation {Ω : Set (X n)} (hΩ : IsOpen Ω) {f : X n → ℝ}
    (hf : LocallyIntegrableOn f Ω) (c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    LocallyIntegrableOn (fun x => c * f (lam • x)) {x | lam • x ∈ Ω} := by
  let L := Homeomorph.smulOfNeZero lam hlam.ne' (α := X n)
  let T : Set (X n) := {x | lam • x ∈ Ω}
  have hT : IsOpen T := hΩ.preimage L.continuous
  apply (locallyIntegrableOn_iff hT.isLocallyClosed).mpr
  intro K hKT hK
  have hKΩ : L '' K ⊆ Ω := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKT hx
  have hI : IntegrableOn f (L '' K) volume :=
    hf.integrableOn_compact_subset hKΩ (hK.image L.continuous)
  have hM : IntegrableOn f (L '' K) ((volume : Measure (X n)).map L.toMeasurableEquiv) := by
    change IntegrableOn f (L '' K) ((volume : Measure (X n)).map (fun x : X n => lam • x))
    rw [Measure.map_addHaar_smul _ hlam.ne']
    unfold IntegrableOn at *
    rw [Measure.restrict_smul]
    exact hI.smul_measure ENNReal.ofReal_ne_top
  have h := (integrableOn_map_equiv L.toMeasurableEquiv).mp hM
  have he : L.toMeasurableEquiv ⁻¹' (L '' K) = K := L.injective.preimage_image K
  rw [he] at h
  exact h.const_mul c

theorem GreenGerm.dilated (hn : 2 ≤ n) {Ω : Set (X n)} (hΩ : IsOpen Ω) {g : MetricField n}
    (hg : SmoothMetric Ω g) {G : X n × X n → ℝ} (hG : GreenGerm Ω g G) {lam : ℝ} (hlam : 0 < lam) :
    GreenGerm {x | lam • x ∈ Ω} (dilatedMetric g lam) (dilatedGreen G lam) := by
  let T : Set (X n) := {x | lam • x ∈ Ω}
  let L : X n →L[ℝ] X n := lam • ContinuousLinearMap.id ℝ (X n)
  let E := Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne') (α := X n)
  have hT : IsOpen T := hΩ.preimage L.continuous
  have hSmul (x x' : X n) (hx : x ≠ x') : lam • x ≠ lam • x' := fun h =>
    hx (by simpa only [scale_inverse_smul lam hlam.ne'] using congrArg (fun z : X n => lam⁻¹ • z) h)
  have hmap : MapsTo (fun p : X n × X n => (lam • p.1, lam • p.2)) (OffDiagonal T) (OffDiagonal Ω) :=
    fun p hp => ⟨hp.1, hp.2.1, hSmul p.1 p.2 hp.2.2⟩
  have hsm : ContDiff ℝ ∞ (fun p : X n × X n => (lam • p.1, lam • p.2)) :=
    (L.contDiff.comp contDiff_fst).prodMk (L.contDiff.comp contDiff_snd)
  refine ⟨contDiffOn_const.mul (hG.1.comp hsm.contDiffOn hmap), ?_, ?_⟩
  · intro q hq
    exact congrArg (fun v : ℝ => lam ^ (n - 2) * v) (hG.2.1 _ (hmap hq))
  · intro y hy
    refine ⟨locIntegrable_dilation hΩ (hG.2.2 (lam • y) hy).1 (lam ^ (n - 2)) hlam, ?_⟩
    intro φ hφ hφc hφT
    let Φ : X n → ℝ := φ ∘ E
    have hΦ : ContDiff ℝ ∞ Φ :=
      hφ.comp (lam⁻¹ • ContinuousLinearMap.id ℝ (X n)).contDiff
    have hΦc : HasCompactSupport Φ := hφc.comp_homeomorph E
    have hΦΩ : tsupport Φ ⊆ Ω := by
      rw [tsupport_comp_eq_preimage φ E]
      intro z hz
      have hz' : lam • (lam⁻¹ • z) ∈ Ω := hφT hz
      simpa only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] using hz'
    have hback : dilatedMetric (dilatedMetric g lam) lam⁻¹ = g := by
      funext z
      simp only [dilatedMetric, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
    let H (z : X n) := G (z, lam • y) * (-laplace g Φ z) * Real.sqrt (g z).det
    have hH : (∫ z in Ω, H z) = Φ (lam • y) :=
      (hG.2.2 (lam • y) hy).2 Φ hΦ hΦc hΦΩ
    have hEqT : lam • T = Ω := by
      ext z
      rw [mem_smul_set_iff_inv_smul_mem₀ hlam.ne']
      change lam • (lam⁻¹ • z) ∈ Ω ↔ z ∈ Ω
      rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
    have hdim : Module.finrank ℝ (X n) = n := finrank_euclideanSpace_fin
    have hscale : lam ^ n = lam ^ (n - 2) * lam ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hn]
    calc
      _ = ∫ x in T, lam^n * H (lam • x) := by
        apply setIntegral_congr_fun hT.measurableSet
        intro x hx
        have hΦlap : laplace g Φ (lam • x) = lam⁻¹ ^ 2 * laplace (dilatedMetric g lam) φ x := by
          have hmem : lam⁻¹ • (lam • x) ∈ T := by simpa only [scale_inverse_smul lam hlam.ne'] using hx
          have h := laplace_dilated hT (smoothMetric_dilated hg lam) hφ.contDiffOn hmem
          change laplace g (fun z => φ (lam⁻¹ • z)) (lam • x) = _
          simpa only [hback, scale_inverse_smul lam hlam.ne'] using h
        simp only [dilatedGreen, dilatedMetric, H, hΦlap, hscale]
        field_simp [hlam.ne']
      _ = lam^n * ((lam^n)⁻¹ * ∫ z in Ω, H z) := by
        rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume H T hlam, hdim, hEqT, smul_eq_mul]
      _ = Φ (lam • y) := by rw [hH, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hlam.ne'), one_mul]
      _ = φ y := congrArg φ (scale_inverse_smul lam hlam.ne' y)

end CalderonN
