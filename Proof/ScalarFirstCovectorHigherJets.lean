import Proof.NormalFrameRelativeNativeCoefficientJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The scalar first covector is the spatial differential of one diagonal
    coefficient entry at zero. Thus its parameter jets use the same local
    mixed coefficient jets, with no basis or frame-derivative loss. -/
theorem norm_iteratedFDeriv_covector_of_scalar_coefficients_le
    (a : P × X → Mat) (ell : P → X →L[ℝ] ℝ) (p0 : P)
    (V : Set P) (hV : IsOpen V) (hp0 : p0 ∈ V)
    (hModel : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,a (p,z) = ell p z • (1:Mat))
    (n : ℕ) (C : ℝ)
    (hMixed : ‖iteratedFDeriv ℝ n (fun p => iteratedFDeriv ℝ 1 (fun z => a (p,z) 0 0) 0) p0‖ ≤ C) :
    ‖iteratedFDeriv ℝ n ell p0‖ ≤ C := by
  let J := fun p => iteratedFDeriv ℝ 1 (fun z => a (p,z) 0 0) 0
  have hEll : ell =ᶠ[𝓝 p0] (fun p => fderiv ℝ (fun z => a (p,z) 0 0) 0) := by
    filter_upwards [hV.mem_nhds hp0] with p hp
    have hSpatial : (fun z => a (p,z) 0 0) =ᶠ[𝓝 (0:X)] (fun z => ell p z) := by
      filter_upwards [Metric.ball_mem_nhds (0:X) (by norm_num : (0:ℝ)<2)] with z hz
      have hh := congrArg (fun A : Mat => A 0 0) (hModel p hp z (Metric.ball_subset_closedBall hz))
      simpa only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply_eq,mul_one] using hh
    rw [hSpatial.fderiv_eq,ContinuousLinearMap.fderiv]
  have hEq : (fun p => fderiv ℝ (fun z => a (p,z) 0 0) 0) =
      (continuousMultilinearCurryFin1 ℝ X ℝ) ∘ J := by
    funext p
    apply ContinuousLinearMap.ext
    intro x
    simp only [Function.comp_apply,continuousMultilinearCurryFin1_apply,J,iteratedFDeriv_one_apply]
    rfl
  rw [(hEll.iteratedFDeriv ℝ n).eq_of_nhds,hEq,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  exact hMixed

theorem NormalFrameRelativeCoefficientJetFamily.firstCovectorJets
    {Y Ω : Set X} {g g₁ : MetricField} {E : X × X → X} {y : X} {L : X →L[ℝ] X}
    {r Z C : ℝ} {N : ℕ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω g g₁ E y L r (N+1) Z C)
    (hZ : 2 ≤ Z) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (normalFrameRelativeFirstCovector g g₁) ((y,L),0)‖ ≤ C := by
  apply norm_iteratedFDeriv_covector_of_scalar_coefficients_le q.a1
    (normalFrameRelativeFirstCovector g g₁) ((y,L),0) q.domain q.domainOpen q.pointMem
    (fun p hp z hz => q.firstScalar p hp z (Metric.closedBall_subset_closedBall hZ hz)) n C
  exact q.firstMixedJets 0 (by simpa only [norm_zero] using (zero_le_two.trans hZ)) n 1 (by omega) 0 0

end ShrinkingSpheres
