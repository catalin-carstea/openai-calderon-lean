module

public import Proof.Manuscript.MovingTraceSymbols

import Proof.Manuscript.CompactAngularFourier
import Proof.CalderonN.Moments
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic


public section

noncomputable section

open Set Filter Metric MeasureTheory CalderonN
open scoped ContDiff Topology ENNReal

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]


omit [NeZero dim] in
private theorem sphereProbability_isOpenPosMeasure :
    (sphereProbability dim).IsOpenPosMeasure := by
  let μ := (volume : Measure (X dim)).toSphere
  change Measure.IsOpenPosMeasure ((μ univ)⁻¹ • μ)
  exact Measure.isOpenPosMeasure_smul μ (ENNReal.inv_ne_zero.mpr (measure_ne_top μ univ))

/-- Real smooth ambient cutoffs separate continuous complex fields on the
sphere under its normalized surface measure. -/
theorem eq_zero_of_sphere_smooth_test_pairings
    {g : ↥(standardSphere dim) → ℂ} (hg : Continuous g)
    (hTest : ∀ t : X dim → ℝ, ContDiff ℝ ∞ t →
      (∫ w : ↥(standardSphere dim), g w * (t w : ℂ) ∂sphereProbability dim) = 0) :
    ∀ w, g w = 0 := by
  let μ := sphereProbability dim
  let : μ.IsOpenPosMeasure := sphereProbability_isOpenPosMeasure
  let : CompactSpace (↥(standardSphere dim)) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  intro w
  by_contra hw
  let a (z : ↥(standardSphere dim)) := (star (g w) * g z).re
  have ha : Continuous a := Complex.continuous_re.comp (continuous_const.mul hg)
  have hAw : 0 < a w := by
    have he : a w = Complex.normSq (g w) := by
      simp [a,Complex.mul_re,Complex.normSq_apply]
    rw [he]
    exact Complex.normSq_pos.mpr hw
  obtain ⟨δ,hδ,hInside⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const ha).mem_nhds hAw)
  let t : ContDiffBump (w : X dim) := ⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  let H (z : ↥(standardSphere dim)) := a z * t z
  have hH : Continuous H := ha.mul (t.continuous.comp continuous_subtype_val)
  have hIntH : Integrable H μ := hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHpos : 0 ≤ H := by
    intro z
    by_cases hz : z ∈ ball w δ
    · exact mul_nonneg (le_of_lt (hInside hz)) t.nonneg
    · have ht : t z = 0 := t.zero_of_le_dist (not_lt.mp (fun h => hz h))
      simp [H,ht]
  have htW : t w = 1 := t.one_of_mem_closedBall (mem_closedBall_self t.rIn_pos.le)
  have hHw : H w ≠ 0 := by simpa only [H,htW,mul_one] using hAw.ne'
  have hPos : 0 < ∫ z, H z ∂μ := integral_pos_of_integrable_nonneg_nonzero hH hIntH hHpos hHw
  let P (z : ↥(standardSphere dim)) := star (g w) * (g z * (t z : ℂ))
  have hP : Continuous P := continuous_const.mul
    (hg.mul (Complex.continuous_ofReal.comp (t.continuous.comp continuous_subtype_val)))
  have hIntP : Integrable P μ := hP.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPart (z : ↥(standardSphere dim)) : H z = (P z).re := by
    dsimp [H,a,P]
    rw [← mul_assoc]
    exact (by simp [Complex.mul_re] :
      (star (g w) * g z).re * t z = ((star (g w) * g z) * (t z : ℂ)).re)
  have hZero : (∫ z, P z ∂μ) = 0 := by
    dsimp only [P]
    rw [integral_const_mul,hTest t t.contDiff,mul_zero]
  have hHzero : (∫ z, H z ∂μ) = 0 := by
    simp only [hPart]
    change (∫ z, Complex.reCLM (P z) ∂μ) = 0
    rw [Complex.reCLM.integral_comp_comm hIntP,hZero,map_zero]
  exact hPos.ne' hHzero

private theorem integral_kernel_swap {S E : Type*}
    [MeasurableSpace S] [MeasurableSpace E] {μ : Measure S} [IsFiniteMeasure μ]
    {ν : Measure E} [SigmaFinite ν] {K : S × E → ℂ} (hK : Measurable K)
    {a : E → ℂ} (ha : Measurable a) {b : E → ℝ} (hb : Integrable b ν)
    (hBound : ∀ w ξ, ‖K (w,ξ)*a ξ‖ ≤ b ξ) :
    (∫ w, ∫ ξ, K (w,ξ)*a ξ ∂ν ∂μ) =
      ∫ ξ, (∫ w, K (w,ξ) ∂μ)*a ξ ∂ν := by
  let f (p : S × E) := K p * a p.2
  have hfM : Measurable f := hK.mul (ha.comp measurable_snd)
  have hG : Integrable (fun p : S × E => b p.2) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (μ := μ) (1:ℝ)).mul_prod hb
  have hf : Integrable f (μ.prod ν) :=
    hG.mono' hfM.aestronglyMeasurable (.of_forall fun p => hBound p.1 p.2)
  calc
    _ = ∫ p, f p ∂μ.prod ν := (integral_prod f hf).symm
    _ = ∫ ξ, ∫ w, f (w,ξ) ∂μ ∂ν := integral_prod_symm f hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ξ
      exact integral_mul_const (μ := μ) (a ξ) (fun w => K (w,ξ))

set_option maxHeartbeats 4500000 in
/-- Recover a continuous operator output from its responses on the
localized plane waves, using duality on the actual sphere measure. -/
theorem angularFourier_reconstruct_from_sphere_pairings
    {f : AngularCoordinates dim → ℂ} (hf : ContDiff ℝ ∞ f) (hSupp : HasCompactSupport f)
    {K : ↥(standardSphere dim) × AngularCoordinates dim → ℂ} (hK : Continuous K)
    {C : ℝ} (hC : 0 ≤ C) (hGrowth : ∀ w ξ, ‖K (w,ξ)‖ ≤ C*(1+‖ξ‖))
    {G ζ : ↥(standardSphere dim) → ℂ} (hG : Continuous G) (hζ : Continuous ζ)
    {read : ↥(standardSphere dim) → AngularCoordinates dim} (hRead : Measurable read)
    (hPair : ∀ t : X dim → ℝ, ContDiff ℝ ∞ t →
      ∃ v : ↥(standardSphere dim) → ℂ, Continuous v ∧
        (∀ ξ, (∫ w : ↥(standardSphere dim), K (w,ξ)*(t w : ℂ) ∂sphereProbability dim) =
          ∫ w : ↥(standardSphere dim), ζ w*angularFourierPhase (read w) ξ*v w ∂sphereProbability dim) ∧
        (∫ w : ↥(standardSphere dim), G w*(t w : ℂ) ∂sphereProbability dim) =
          ∫ w : ↥(standardSphere dim), ζ w*f (read w)*v w ∂sphereProbability dim) :
    ∀ w, G w = ∫ ξ, K (w,ξ)*angularFourierTransform f ξ := by
  let μ := sphereProbability dim
  let : CompactSpace (↥(standardSphere dim)) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X dim) 1)
  let F := angularFourierTransform f
  let R (w : ↥(standardSphere dim)) := ∫ ξ, K (w,ξ)*F ξ
  have hF : Continuous F := angularFourierTransform_continuous f hf hSupp
  have hF0 : Integrable (fun ξ => ‖F ξ‖) := by
    simpa only [pow_zero,one_mul] using angularFourierTransform_integrable_norm_weight f hf hSupp 0
  have hF1 : Integrable (fun ξ => ‖ξ‖ * ‖F ξ‖) := by
    simpa only [pow_one] using angularFourierTransform_integrable_norm_weight f hf hSupp 1
  let b (ξ : AngularCoordinates dim) := (1+‖ξ‖)*‖F ξ‖
  have hb : Integrable b := by
    have h : b = (fun ξ => ‖F ξ‖) + (fun ξ => ‖ξ‖ * ‖F ξ‖) := by
      funext ξ
      simp only [b,Pi.add_apply,add_mul,one_mul]
    rw [h]
    exact hF0.add hF1
  have hKR (w : ↥(standardSphere dim)) (ξ : AngularCoordinates dim) :
      ‖K (w,ξ)*F ξ‖ ≤ C*b ξ := by
    rw [norm_mul,show C*b ξ = (C*(1+‖ξ‖))*‖F ξ‖ from (mul_assoc _ _ _).symm]
    exact mul_le_mul_of_nonneg_right (hGrowth w ξ) (norm_nonneg _)
  have hR : Continuous R := continuous_of_dominated
    (fun w => ((hK.comp (continuous_const.prodMk continuous_id)).mul hF).aestronglyMeasurable)
    (fun w => .of_forall (hKR w)) (hb.const_mul C)
    (.of_forall fun ξ => (hK.comp (continuous_id.prodMk continuous_const)).mul continuous_const)
  have hDiff : ∀ w, G w - R w = 0 := by
    apply eq_zero_of_sphere_smooth_test_pairings (hG.sub hR)
    intro t ht
    obtain ⟨v,hv,hPlane,hData⟩ := hPair t ht
    have htₛ : Continuous (fun w : ↥(standardSphere dim) => t w) := ht.continuous.comp continuous_subtype_val
    obtain ⟨T,hT⟩ := isCompact_univ.exists_bound_of_continuousOn htₛ.continuousOn
    obtain ⟨V,hV⟩ := isCompact_univ.exists_bound_of_continuousOn (hζ.mul hv).continuousOn
    let A := max T 0 * C
    have hMajor₁ (w : ↥(standardSphere dim)) (ξ : AngularCoordinates dim) :
        ‖(K (w,ξ)*(t w : ℂ))*F ξ‖ ≤ A*b ξ := by
      rw [mul_right_comm,norm_mul,Complex.norm_real]
      calc
        _ ≤ C*b ξ * max T 0 := mul_le_mul (hKR w ξ)
          ((hT w (mem_univ _)).trans (le_max_left _ _)) (norm_nonneg _) (by
            dsimp only [b]; positivity)
        _ = _ := by dsimp only [A]; ring
    have hP := integral_kernel_swap
      (ν := volume) (μ := μ) (K := fun q => K q * (t q.1 : ℂ))
      (hK.mul (Complex.continuous_ofReal.comp (htₛ.comp continuous_fst))).measurable
      hF.measurable (hb.const_mul A) hMajor₁
    have hPhase : Continuous (fun q : AngularCoordinates dim × AngularCoordinates dim =>
        angularFourierPhase q.1 q.2) := by unfold angularFourierPhase; fun_prop
    let Q (p : ↥(standardSphere dim) × AngularCoordinates dim) :=
      ζ p.1 * angularFourierPhase (read p.1) p.2 * v p.1
    have hQ : Measurable Q :=
      (hζ.measurable.comp measurable_fst |>.mul
        (hPhase.measurable.comp ((hRead.comp measurable_fst).prodMk measurable_snd))).mul
        (hv.measurable.comp measurable_fst)
    have hMajor₂ (w : ↥(standardSphere dim)) (ξ : AngularCoordinates dim) :
        ‖Q (w,ξ)*F ξ‖ ≤ max V 0 * ‖F ξ‖ := by
      change ‖(ζ w * angularFourierPhase (read w) ξ * v w) * F ξ‖ ≤ _
      rw [mul_right_comm (ζ w),norm_mul,norm_mul,angularFourierPhase_norm,mul_one]
      exact mul_le_mul_of_nonneg_right ((hV w (mem_univ _)).trans (le_max_left _ _)) (norm_nonneg _)
    have hQSwap := integral_kernel_swap (ν := volume) (μ := μ) hQ hF.measurable
      (hF0.const_mul (max V 0)) hMajor₂
    have hRec : (∫ w : ↥(standardSphere dim), R w * (t w : ℂ) ∂μ) =
        ∫ w : ↥(standardSphere dim), ζ w * f (read w) * v w ∂μ := by
      calc
        _ = ∫ w, ∫ ξ, (K (w,ξ)*(t w : ℂ))*F ξ ∂volume ∂μ := by
          apply integral_congr_ae
          filter_upwards with w
          simp only [R,← integral_mul_const,mul_right_comm]
        _ = ∫ ξ, (∫ w, K (w,ξ)*(t w : ℂ) ∂μ)*F ξ := hP
        _ = ∫ ξ, (∫ w, Q (w,ξ) ∂μ)*F ξ := by
          apply integral_congr_ae
          filter_upwards with ξ
          rw [hPlane ξ]
        _ = ∫ w, ∫ ξ, Q (w,ξ)*F ξ ∂volume ∂μ := hQSwap.symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards with w
          calc
            _ = (ζ w * v w) * ∫ ξ, angularFourierPhase (read w) ξ * F ξ := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with ξ
              dsimp only [Q]
              ring
            _ = _ := by
              rw [(angularFourier_inversion f hf hSupp (read w)).2.2]
              ring
    have hGt : Integrable (fun w : ↥(standardSphere dim) => G w * (t w : ℂ)) μ :=
      (hG.mul (Complex.continuous_ofReal.comp htₛ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hRt : Integrable (fun w : ↥(standardSphere dim) => R w * (t w : ℂ)) μ :=
      (hR.mul (Complex.continuous_ofReal.comp htₛ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change (∫ w : ↥(standardSphere dim), (G w-R w)*(t w : ℂ) ∂μ) = 0
    simp only [sub_mul]
    rw [integral_sub hGt hRt,hRec,hData,sub_self]
  exact fun w => sub_eq_zero.mp (hDiff w)

end CalderonPaper
