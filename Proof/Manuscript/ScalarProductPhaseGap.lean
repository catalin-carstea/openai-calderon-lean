module

public import Proof.Manuscript.SingleAxisProductPhase
public import Proof.CalderonN.ProductMetricHessian
public import Proof.CalderonN.PrescribedChartPhase
public import Proof.CalderonN.PositiveHessianGap

import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

@[expose] public section

/-! The derivative computation for the product gap adapts
`StrictWeightPrescribedMetricJets` at anisotropic-calderon-lean revision
`d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The product Hessian test gives two strict phases whose sum lies under
the same defining function, after the source quadratic modification. -/
theorem exists_local_productPhase_gap_all
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {U : Set ((X dim) × (X dim))} (hU : IsOpen U) (z0 : (X dim) × (X dim)) (h0U : z0 ∈ U)
    {rho : (X dim) × (X dim) → ℝ} (hrho : ContDiffOn ℝ ∞ rho U) (hrho0 : rho z0 = 0)
    (hstrict : ProductStrictHessianAt g₁ g₂ rho z0) :
    ∃ (theta1 theta2 : (X dim) → ℝ) (K c r : ℝ),
      ContDiff ℝ ∞ theta1 ∧ ContDiff ℝ ∞ theta2 ∧ theta1 z0.1 = 0 ∧ theta2 z0.2 = 0 ∧
      fderiv ℝ theta1 z0.1 = (fderiv ℝ rho z0).comp (ContinuousLinearMap.inl ℝ (X dim) (X dim)) ∧
      fderiv ℝ theta2 z0.2 = (fderiv ℝ rho z0).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim)) ∧
      StrictMetricWeightAt g₁ theta1 z0.1 ∧ StrictMetricWeightAt g₂ theta2 z0.2 ∧
      0 < K ∧ 0 < c ∧ 0 < r ∧ closedBall z0 r ⊆ U ∧
      (∀ z ∈ closedBall z0 r, theta1 z.1 + theta2 z.2 + c * (‖z.1-z0.1‖^2 + ‖z.2-z0.2‖^2) ≤
        rho z + K*(rho z)^2/2) ∧
      ∀ z ∈ closedBall z0 r, 0 < rho z + K*(rho z)^2/2 ↔ 0 < rho z := by
  let x0 := z0.1
  let y0 := z0.2
  let ell := fderiv ℝ rho z0
  let ell1 := ell.comp (ContinuousLinearMap.inl ℝ (X dim) (X dim))
  let ell2 := ell.comp (ContinuousLinearMap.inr ℝ (X dim) (X dim))
  have hρ := hrho.contDiffAt (hU.mem_nhds h0U)
  have hSplit :
      let f₁ : X dim → ℝ := fun x => rho (x,z0.2)
      let f₂ : X dim → ℝ := fun y => rho (z0.1,y)
      let a₁ := (covectorSq g₁ f₁ z0.1)⁻¹ • chartMetricGradient g₁ f₁ z0.1
      let a₂ := (covectorSq g₂ f₂ z0.2)⁻¹ • chartMetricGradient g₂ f₂ z0.2
      ∃ (P₁ P₂ : selfAdjoint (Mat dim)) (K : ℝ), 0 < K ∧
        P₁ ∈ ProductHessianSeparation.strictSphereCone (g₁ z0.1)
          (fun i => coordDeriv i f₁ z0.1) (fun i => a₁ i) ∧
        P₂ ∈ ProductHessianSeparation.strictSphereCone (g₂ z0.2)
          (fun i => coordDeriv i f₂ z0.2) (fun i => a₂ i) ∧
        ∀ v : X dim × X dim, v ≠ 0 → 0 <
          productMetricHessian g₁ g₂ rho z0 v v + K*(fderiv ℝ rho z0 v)^2 -
            chartBilinear (P₁ : Mat dim) v.1 v.1 - chartBilinear (P₂ : Mat dim) v.2 v.2 := by
    by_cases h : dim = 1
    · subst dim
      exact CalderonPaper.ScalarElliptic.exists_single_axis_blockHessians hg₁ hg₂ hstrict
    · have hn : 2 ≤ dim := by
        have h0 := NeZero.ne dim
        omega
      let : Nontrivial (Fin dim) := Fin.nontrivial_iff_two_le.mpr hn
      exact exists_blockHessians_of_productStrictHessian hg₁ hg₂ (hρ.of_le (by simp)) hstrict
  obtain ⟨P₁,P₂,K,hK,hcone₁,hcone₂,hGap⟩ := hSplit
  obtain ⟨theta1,hSmooth1,hZero1,hFirst1,hSecond1,hHess1⟩ :=
    exists_phase_of_jets hg₁ x0 ell1 P₁
  obtain ⟨theta2,hSmooth2,hZero2,hFirst2,hSecond2,hHess2⟩ :=
    exists_phase_of_jets hg₂ y0 ell2 P₂
  have hgrad₁ (i : (I dim)) : coordDeriv i theta1 x0 = coordDeriv i (fun x => rho (x,y0)) x0 := by
    rw [coordDeriv, hFirst1]
    exact (slice_coordDeriv rho z0 (hρ.differentiableAt (by simp)) i).1.symm
  have hgrad₂ (i : (I dim)) : coordDeriv i theta2 y0 = coordDeriv i (fun y => rho (x0,y)) y0 := by
    rw [coordDeriv, hFirst2]
    exact (slice_coordDeriv rho z0 (hρ.differentiableAt (by simp)) i).2.symm
  change _ ∧ _ ∧ _ at hstrict
  have hs₁ := strictMetricWeightAt_of_matrix_cone
    (hg₁.2 x0 (mem_univ x0)) (f := theta1) (by simpa only [hgrad₁] using hstrict.1)
    P₁ hHess1 (by simpa only [chartMetricGradient, covectorSq, hgrad₁] using hcone₁)
  have hs₂ := strictMetricWeightAt_of_matrix_cone
    (hg₂.2 y0 (mem_univ y0)) (f := theta2) (by simpa only [hgrad₂] using hstrict.2.1)
    P₂ hHess2 (by simpa only [chartMetricGradient, covectorSq, hgrad₂] using hcone₂)
  let E := (X dim) × (X dim)
  let pr1 : E →L[ℝ] (X dim) := ContinuousLinearMap.fst ℝ (X dim) (X dim)
  let pr2 : E →L[ℝ] (X dim) := ContinuousLinearMap.snd ℝ (X dim) (X dim)
  let C1 : ((X dim) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E (X dim) ℝ).flip pr1
  let C2 : ((X dim) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E (X dim) ℝ).flip pr2
  let RhoD : E → E →L[ℝ] ℝ := fderiv ℝ rho
  let D1 : E → E →L[ℝ] ℝ := fun z => C1 (fderiv ℝ theta1 z.1)
  let D2 : E → E →L[ℝ] ℝ := fun z => C2 (fderiv ℝ theta2 z.2)
  let F : E → ℝ := fun z => rho z + (K/2) * (rho z * rho z) - theta1 z.1 - theta2 z.2
  let Aderiv : E → E →L[ℝ] ℝ := fun z =>
    RhoD z + (K/2) • (rho z • RhoD z + rho z • RhoD z) - D1 z - D2 z
  have hRhoAt : ContDiffAt ℝ ∞ rho z0 := hrho.contDiffAt (hU.mem_nhds h0U)
  have hRhoDiff (z : E) (hz : z ∈ U) : DifferentiableAt ℝ rho z :=
    (hrho.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hF : ContDiffOn ℝ ∞ F U :=
    ((hrho.add (contDiffOn_const.mul (hrho.mul hrho))).sub
      (hSmooth1.comp contDiff_fst).contDiffOn).sub
        (hSmooth2.comp contDiff_snd).contDiffOn
  have hDFat (z : E) (hz : z ∈ U) : fderiv ℝ F z = Aderiv z := by
    have hR : HasFDerivAt rho (RhoD z) z := (hRhoDiff z hz).hasFDerivAt
    have hT1 : HasFDerivAt (fun w : E => theta1 w.1) (D1 z) z := by
      have hOuter : HasFDerivAt theta1 (fderiv ℝ theta1 z.1) z.1 :=
        (hSmooth1.differentiable (by simp) z.1).hasFDerivAt
      have hInner : HasFDerivAt (fun w : E => w.1) pr1 z :=
        ContinuousLinearMap.hasFDerivAt pr1
      exact HasFDerivAt.comp (f := fun w : E => w.1) (f' := pr1)
        (g := theta1) (g' := fderiv ℝ theta1 z.1) z hOuter hInner
    have hT2 : HasFDerivAt (fun w : E => theta2 w.2) (D2 z) z := by
      have hOuter : HasFDerivAt theta2 (fderiv ℝ theta2 z.2) z.2 :=
        (hSmooth2.differentiable (by simp) z.2).hasFDerivAt
      have hInner : HasFDerivAt (fun w : E => w.2) pr2 z :=
        ContinuousLinearMap.hasFDerivAt pr2
      exact HasFDerivAt.comp (f := fun w : E => w.2) (f' := pr2)
        (g := theta2) (g' := fderiv ℝ theta2 z.2) z hOuter hInner
    have h := ((hR.add ((hR.mul hR).const_smul (K/2))).sub hT1).sub hT2
    have hFunction : ((rho + (K/2) • (rho*rho) - (fun w : E => theta1 w.1)) -
        (fun w : E => theta2 w.2)) = F := by
      funext w
      rfl
    rw [hFunction] at h
    simpa only [Aderiv,RhoD] using h.fderiv
  have hDFgerm : fderiv ℝ F =ᶠ[𝓝 z0] Aderiv := by
    filter_upwards [hU.mem_nhds h0U] with z hz
    exact hDFat z hz
  have hEllPair (u v : (X dim)) : ell (u,v) = ell1 u + ell2 v :=
    fderiv_product_split ell (u,v)
  have hFzero : F z0 = 0 := by
    change rho z0 + (K/2) * (rho z0 * rho z0) - theta1 x0 - theta2 y0 = 0
    simp [hrho0, hZero1, hZero2]
  have hDFzero : fderiv ℝ F z0 = 0 := by
    rw [hDFat z0 h0U]
    apply ContinuousLinearMap.ext
    intro W
    change ell W + (K/2) * (rho z0 * ell W + rho z0 * ell W) -
      (fderiv ℝ theta1 x0) W.1 - (fderiv ℝ theta2 y0) W.2 = 0
    rw [hrho0,hFirst1,hFirst2]
    have h := hEllPair W.1 W.2
    change ell W = ell1 W.1 + ell2 W.2 at h
    linarith only [h]
  have hRD : HasFDerivAt RhoD (fderiv ℝ (fderiv ℝ rho) z0) z0 :=
    ((hRhoAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hR : HasFDerivAt rho ell z0 := (hRhoDiff z0 h0U).hasFDerivAt
  have hD1 : HasFDerivAt D1
      (C1.comp ((fderiv ℝ (fderiv ℝ theta1) x0).comp pr1)) z0 := by
    have hTheta : HasFDerivAt (fderiv ℝ theta1)
        (fderiv ℝ (fderiv ℝ theta1) x0) x0 :=
      (((hSmooth1.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x0).hasFDerivAt
    have hP : HasFDerivAt (fun z : E => z.1) pr1 z0 :=
      ContinuousLinearMap.hasFDerivAt pr1
    have hFirst := HasFDerivAt.comp (f := fun z : E => z.1) (f' := pr1)
      (g := fderiv ℝ theta1) (g' := fderiv ℝ (fderiv ℝ theta1) x0) z0 hTheta hP
    have hOuter : HasFDerivAt (fun v : (X dim) →L[ℝ] ℝ => C1 v) C1 (fderiv ℝ theta1 x0) :=
      ContinuousLinearMap.hasFDerivAt C1
    exact HasFDerivAt.comp (f := fun z : E => fderiv ℝ theta1 z.1)
      (f' := (fderiv ℝ (fderiv ℝ theta1) x0).comp pr1)
      (g := fun v : (X dim) →L[ℝ] ℝ => C1 v) (g' := C1) z0 hOuter hFirst
  have hD2 : HasFDerivAt D2
      (C2.comp ((fderiv ℝ (fderiv ℝ theta2) y0).comp pr2)) z0 := by
    have hTheta : HasFDerivAt (fderiv ℝ theta2)
        (fderiv ℝ (fderiv ℝ theta2) y0) y0 :=
      (((hSmooth2.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) y0).hasFDerivAt
    have hP : HasFDerivAt (fun z : E => z.2) pr2 z0 :=
      ContinuousLinearMap.hasFDerivAt pr2
    have hFirst := HasFDerivAt.comp (f := fun z : E => z.2) (f' := pr2)
      (g := fderiv ℝ theta2) (g' := fderiv ℝ (fderiv ℝ theta2) y0) z0 hTheta hP
    have hOuter : HasFDerivAt (fun v : (X dim) →L[ℝ] ℝ => C2 v) C2 (fderiv ℝ theta2 y0) :=
      ContinuousLinearMap.hasFDerivAt C2
    exact HasFDerivAt.comp (f := fun z : E => fderiv ℝ theta2 z.2)
      (f' := (fderiv ℝ (fderiv ℝ theta2) y0).comp pr2)
      (g := fun v : (X dim) →L[ℝ] ℝ => C2 v) (g' := C2) z0 hOuter hFirst
  have hScale := hR.smul hRD
  have hA := ((hRD.add ((hScale.add hScale).const_smul (K/2))).sub hD1).sub hD2
  have hAFunction : (RhoD + (K/2) • (rho • RhoD + rho • RhoD) - D1 - D2) = Aderiv := by
    funext z
    rfl
  rw [hAFunction] at hA
  let Q : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ F) z0
  have hQformula (W : E) : Q W W =
      productMetricHessian g₁ g₂ rho z0 W W + K*(ell W)^2 -
        chartBilinear (P₁ : (Mat dim)) W.1 W.1 - chartBilinear (P₂ : (Mat dim)) W.2 W.2 := by
    have hQderiv : Q = fderiv ℝ Aderiv z0 := hDFgerm.fderiv_eq
    rw [hQderiv,hA.fderiv]
    change fderiv ℝ (fderiv ℝ rho) z0 W W +
      (K/2) * ((rho z0 * fderiv ℝ (fderiv ℝ rho) z0 W W + ell W * ell W) +
        (rho z0 * fderiv ℝ (fderiv ℝ rho) z0 W W + ell W * ell W)) -
      fderiv ℝ (fderiv ℝ theta1) x0 W.1 W.1 - fderiv ℝ (fderiv ℝ theta2) y0 W.2 W.2 = _
    rw [hrho0,hSecond1,hSecond2,productMetricHessian,
      hEllPair (connection g₁ x0 W.1 W.1) (connection g₂ y0 W.2 W.2)]
    ring
  have hQpositive (W : E) (hW : W ≠ 0) : 0 < Q W W := by
    rw [hQformula]
    exact hGap W hW
  obtain ⟨b,r,hb,hr,hrU,hlower⟩ :=
    exists_quadratic_lower_of_hessian_positive hU hF h0U hFzero hDFzero hQpositive
  have hFactorContinuous : ContinuousAt (fun z : E => 1+K*rho z/2) z0 :=
    continuousAt_const.add ((continuousAt_const.mul hρ.continuousAt).div_const 2)
  have hFactorAt0 : 0 < 1+K*rho z0/2 := by simp [hrho0]
  have hp : {z : E | 0 < 1+K*rho z/2} ∈ 𝓝 z0 :=
    hFactorContinuous (Ioi_mem_nhds hFactorAt0)
  obtain ⟨d,hd,hp'⟩ := Metric.mem_nhds_iff.mp hp
  let r' := min r (d/2)
  have hr' : 0 < r' := lt_min hr (half_pos hd)
  have hsub : closedBall z0 r' ⊆ closedBall z0 r := closedBall_subset_closedBall (min_le_left _ _)
  refine ⟨theta1,theta2,K,b/2,r',hSmooth1,hSmooth2,hZero1,hZero2,hFirst1,hFirst2,hs₁,hs₂,
    hK,half_pos hb,hr',hsub.trans hrU,?_,?_⟩
  · intro z hz
    have h := hlower z (hsub hz)
    have h1 := norm_fst_le (z-z0)
    have h2 := norm_snd_le (z-z0)
    change ‖z.1-z0.1‖ ≤ ‖z-z0‖ at h1
    change ‖z.2-z0.2‖ ≤ ‖z-z0‖ at h2
    have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hsum : ‖z.1-z0.1‖^2 + ‖z.2-z0.2‖^2 ≤ 2 * ‖z-z0‖^2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hsum (half_pos hb).le
    dsimp only [F] at h
    nlinarith only [h,hm]
  · intro z hz
    have hzin : z ∈ ball z0 d := mem_ball.mpr
      ((mem_closedBall.mp hz).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hd)))
    have hpos : 0 < 1+K*rho z/2 := hp' hzin
    rw [show rho z + K*(rho z)^2/2 = rho z*(1+K*rho z/2) by ring]
    exact mul_pos_iff_of_pos_right hpos

end CalderonN
