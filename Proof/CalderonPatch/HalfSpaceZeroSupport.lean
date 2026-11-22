module

public import Proof.CalderonPatch.HalfSpaceTangentialExtension
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.CompactSupport

import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Density
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Translation
import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.Lp.Translation
import Mathlib.Tactic

public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace TauCeti
open scoped ContDiff Distributions ENNReal Gradient Topology

namespace CalderonPatch

open CalderonN (X I axis)

variable {n : ℕ} [NeZero n]
local notation "E" => X n
local notation "H" => positiveHalfSpaceOpens n
local notation "μ" => (volume : Measure E)

omit [NeZero n] in
private theorem restrictL_contDiffSMul_ofTestFunction_eq
    {U : Opens E} {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ (U : Set E)) {B : ℝ} (hB : 0 ≤ B)
    (hbχ : ∀ x, |χ x| ≤ B) (hbg : ∀ x, ‖∇ χ x‖ ≤ B)
    (φ : 𝓓(⊤,ℝ)) :
    W1p.restrictL (U := U) le_top
      (W1p.contDiffSMul χ hχ hB (fun x _ => hbχ x) (fun x _ => hbg x)
        (W1p.ofTestFunctionₗ μ ⊤ 2 φ)) =
      W1p.ofTestFunctionₗ μ U 2
        ⟨χ * φ,hχ.mul φ.contDiff,φ.hasCompactSupport.mul_left,tsupport_mul_subset_left.trans hs⟩ := by
  let ψ : 𝓓(U,ℝ) :=
    ⟨χ * φ,hχ.mul φ.contDiff,φ.hasCompactSupport.mul_left,tsupport_mul_subset_left.trans hs⟩
  let u := W1p.ofTestFunctionₗ μ ⊤ 2 φ
  let v := W1p.contDiffSMul χ hχ hB (fun x _ => hbχ x) (fun x _ => hbg x) u
  change W1p.restrictL (U := U) le_top v = W1p.ofTestFunctionₗ μ U 2 ψ
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.value_restrictL_ae (U := U) le_top v,
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) (W1p.value_contDiffSMul_ae hχ hB
      (fun x _ => hbχ x) (fun x _ => hbg x) u),
    ae_restrict_of_ae_restrict_of_subset (subset_univ _) (testFunctionLp_apply_ae (mu := μ) 2 φ),
    testFunctionLp_apply_ae (mu := μ) 2 ψ] with x h₁ h₂ h₃ h₄
  rw [h₁,h₂,W1p.value_ofTestFunctionₗ,smul_eq_mul,h₃,
    W1p.value_ofTestFunctionₗ,h₄]
  rfl

omit [NeZero n] in
private theorem map_mem_w1p0_of_test
    {U : Opens E} (L : W1p μ ⊤ 2 →L[ℝ] W1p μ U 2)
    (hL : ∀ φ : 𝓓(⊤, ℝ), L (W1p.ofTestFunctionₗ μ ⊤ 2 φ) ∈ w1p0Submodule μ U 2)
    (w : W1p μ ⊤ 2) : L w ∈ w1p0Submodule μ U 2 := by
  exact (W1p.denseRange_ofTestFunctionₗ_top (mu := μ) (p := 2) (by norm_num)).induction_on w
    ((w1p0Submodule μ U 2).isClosed.preimage L.continuous) hL

set_option maxHeartbeats 3500000 in
omit [NeZero n] in
theorem restrictL_contDiffSMul_mem_w1p0
    {U : Opens E} {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ (U : Set E)) {B : ℝ} (hB : 0 ≤ B)
    (hbχ : ∀ x, |χ x| ≤ B) (hbg : ∀ x, ‖∇ χ x‖ ≤ B)
    (w : W1p μ ⊤ 2) :
    W1p.restrictL (U := U) le_top
      (W1p.contDiffSMul χ hχ hB (fun x _ => hbχ x) (fun x _ => hbg x) w) ∈
        w1p0Submodule μ U 2 := by
  let P := W1p.contDiffSMulL (Omega := ⊤) (mu := μ) (p := 2) χ hχ hB
    (fun x _ => hbχ x) (fun x _ => hbg x)
  let Q := W1p.restrictL (U := U) (mu := μ) (p := 2) le_top
  let L : W1p μ ⊤ 2 →L[ℝ] W1p μ U 2 := Q.comp P
  have hTest (φ : 𝓓(⊤, ℝ)) : L (W1p.ofTestFunctionₗ μ ⊤ 2 φ) ∈ w1p0Submodule μ U 2 := by
    simp only [L,P,Q,ContinuousLinearMap.comp_apply,W1p.contDiffSMulL_apply]
    rw [restrictL_contDiffSMul_ofTestFunction_eq hχ hs hB hbχ hbg]
    exact W1p.ofTestFunctionₗ_mem_w1p0Submodule _
  have hm := map_mem_w1p0_of_test L hTest w
  simpa only [L,P,Q,ContinuousLinearMap.comp_apply,W1p.contDiffSMulL_apply] using hm

private theorem exists_halfSpaceCutoff_gradient_bound {c : ℝ} (hc : 0 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x : E, |halfSpaceCutoff c x| ≤ B) ∧
      ∀ x : E, ‖∇ (halfSpaceCutoff c) x‖ ≤ B := by
  have hcomp : HasCompactSupport (deriv Real.smoothTransition) := by
    apply (isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    by_cases hLower : x < 0
    · have hEq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => 0) :=
        Filter.Eventually.mono (isOpen_Iio.mem_nhds (show x ∈ Iio (0 : ℝ) from hLower))
          (fun y hy => Real.smoothTransition.zero_of_nonpos (mem_Iio.mp hy).le)
      exact hx (hEq.deriv_eq.trans (by simp))
    · have hUpper : 1 < x := lt_of_not_ge (fun hle => h ⟨le_of_not_gt hLower,hle⟩)
      have hEq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => 1) :=
        Filter.Eventually.mono (isOpen_Ioi.mem_nhds (show x ∈ Ioi (1 : ℝ) from hUpper))
          (fun y hy => Real.smoothTransition.one_of_one_le (mem_Ioi.mp hy).le)
      exact hx (hEq.deriv_eq.trans (by simp))
  obtain ⟨B,hB⟩ := ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).norm
    |>.bddAbove_range_of_hasCompactSupport hcomp.norm
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB ⟨0,rfl⟩)
  let L := EuclideanSpace.proj (𝕜 := ℝ) (0 : I n)
  refine ⟨max 1 (B * c * ‖L‖),zero_le_one.trans (le_max_left _ _),fun x => ?_,fun x => ?_⟩
  · rw [halfSpaceCutoff,abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact (Real.smoothTransition.le_one _).trans (le_max_left _ _)
  · have hl : HasFDerivAt (fun y : E => c * L y - 1) (c • L) x :=
        (L.hasFDerivAt.const_mul c).sub_const 1
    have hd := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero (c * L x - 1)).hasDerivAt
    have hdχ : HasFDerivAt (halfSpaceCutoff c) ((deriv Real.smoothTransition (c * L x - 1) * c) • L) x :=
      (hd.comp_hasFDerivAt x hl).congr_fderiv (by rw [smul_smul])
    rw [norm_gradient_eq_norm_fderiv,hdχ.fderiv,norm_smul,norm_mul,Real.norm_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB ⟨_,rfl⟩) hc)
      (norm_nonneg _)).trans (le_max_right _ _)

private def shiftNormal (s : ℝ) (w : W1p μ ⊤ 2) : W1p μ ⊤ 2 :=
  W1p.translate (Omega := ⊤) (V := ⊤) (h := (-s) • axis 0) (fun _ _ => by simp) w

private theorem shiftNormal_tendsto (w : W1p μ ⊤ 2) :
    Tendsto (fun s : ℝ => shiftNormal s w) (𝓝 0) (𝓝 w) := by
  have hl : Tendsto (fun s : ℝ => (-s) • (axis (0 : I n))) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun s : ℝ => (-s) • (axis (0 : I n))) :=
      (show Continuous (fun s : ℝ => -s) from continuous_neg).smul continuous_const
    simpa only [neg_zero,zero_smul] using hc.tendsto (0 : ℝ)
  let ν := (μ).restrict (⊤ : Opens E)
  have hν : ν = μ := Measure.restrict_univ
  let : ν.IsAddRightInvariant := hν.symm ▸ (inferInstance : (μ).IsAddRightInvariant)
  let : ν.InnerRegularCompactLTTop := hν.symm ▸ (inferInstance : (μ).InnerRegularCompactLTTop)
  let : IsLocallyFiniteMeasure ν := hν.symm ▸ (inferInstance : IsLocallyFiniteMeasure μ)
  have ht (A : Type) [NormedAddCommGroup A] [NormedSpace ℝ A] (f : Lp A 2 ν) :
      Tendsto (fun s : ℝ => Measure.translateLp ν 2 ((-s) • axis 0) f) (𝓝 0) (𝓝 f) := by
    have h := (Measure.continuous_translateLp (mu := ν) (p := 2) (by norm_num) f).tendsto
      (0 : E)
    rw [Measure.translateLp_zero] at h
    exact h.comp hl
  refine W1p.tendsto_iff_value_gradient.mpr ⟨(ht ℝ (W1p.value w)).congr (fun s => ?_),
    (ht E (W1p.gradient w)).congr (fun s => ?_)⟩
  · apply Lp.ext
    exact (Measure.coeFn_translateLp ((-s) • axis 0) (W1p.value w)).trans
      (W1p.value_translate_ae (V := ⊤) (h := (-s) • axis 0) (fun _ _ => by simp) w).symm
  · apply Lp.ext
    exact (Measure.coeFn_translateLp ((-s) • axis 0) (W1p.gradient w)).trans
      (W1p.gradient_translate_ae (V := ⊤) (h := (-s) • axis 0) (fun _ _ => by simp) w).symm

/-- A whole-space Sobolev function vanishing almost everywhere below
the flat face restricts to a zero-trace function on the half-space. -/
theorem restrictL_mem_w1p0_of_zero_off_positiveHalfSpace (w : W1p μ ⊤ 2)
    (hw : ∀ᵐ x ∂μ, x ∉ positiveHalfSpace n → W1p.value w x = 0) :
    W1p.restrictL (U := H) le_top w ∈ w1p0Submodule μ H 2 := by
  have ht := ((W1p.restrictL (U := H) (mu := μ) (p := 2) le_top).continuous.tendsto w).comp
    (shiftNormal_tendsto w)
  apply (w1p0Submodule μ H 2).isClosed.mem_of_tendsto
    (ht.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ))))
  apply eventually_nhdsWithin_of_forall
  intro s hs
  have hs' : 0 < s := hs
  let c : ℝ := 2 / s
  have hc : 0 < c := div_pos (by norm_num) hs'
  obtain ⟨B,hB,hbχ,hbg⟩ := exists_halfSpaceCutoff_gradient_bound (n := n) hc.le
  have hsupp : tsupport (halfSpaceCutoff c : E → ℝ) ⊆ (H : Set E) :=
    (tsupport_halfSpaceCutoff_subset hc).trans fun x hx =>
      mem_positiveHalfSpace.mpr ((div_pos one_pos hc).trans_le hx)
  have hcut := restrictL_contDiffSMul_mem_w1p0
    (contDiff_halfSpaceCutoff c) hsupp hB hbχ hbg (shiftNormal s w)
  have hEq : W1p.contDiffSMul (halfSpaceCutoff c) (contDiff_halfSpaceCutoff c) hB
      (fun x _ => hbχ x) (fun x _ => hbg x) (shiftNormal s w) = shiftNormal s w := by
    apply W1p.ext_value
    apply Lp.ext
    have htr := W1p.value_translate_ae (V := ⊤) (h := (-s) • axis 0) (fun _ _ => by simp) w
    have hshift := (measurePreserving_add_right μ ((-s) • axis (0 : I n))).quasiMeasurePreserving.ae hw
    filter_upwards [W1p.value_contDiffSMul_ae (contDiff_halfSpaceCutoff c) hB (fun x _ => hbχ x)
      (fun x _ => hbg x) (shiftNormal s w),htr,ae_restrict_of_ae hshift] with x h₁ h₂ h₃
    rw [h₁,smul_eq_mul]
    by_cases hx : s ≤ x 0
    · have hχ : halfSpaceCutoff c x = 1 := by
        apply Real.smoothTransition.one_of_one_le
        change 1 ≤ 2 / s * x 0 - 1
        rw [div_mul_eq_mul_div]
        have hh := (le_div_iff₀ hs').2 (by linarith [hx] : (2 : ℝ) * s ≤ 2 * x 0)
        linarith
      rw [hχ,one_mul]
    · have hx0 : x + (-s) • axis (0 : I n) ∉ positiveHalfSpace n := by
        rw [mem_positiveHalfSpace]
        simpa [axis,not_lt,sub_eq_add_neg] using le_of_not_ge hx
      change W1p.value (shiftNormal s w) x = _ at h₂
      rw [h₂,h₃ hx0,mul_zero]
  rwa [hEq] at hcut

end CalderonPatch
