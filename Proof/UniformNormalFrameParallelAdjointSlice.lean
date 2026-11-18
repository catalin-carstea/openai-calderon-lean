import Proof.UniformParallelOneBoundaryTaylorData
import Proof.UniformNormalizedAdjointPointControl
import Proof.CommonSupportRadialAdjointTaylorDerivative
import Proof.UniformNormalFrameTaylorSlices
import Proof.ParallelCoefficientPointGerms
import Proof.NormalFrameRadialAdjointLift
import Proof.FirstRadialSliceDerivative
import Proof.RadialAdjointCurveCongruence
import Proof.NormalFrameAdjointTaylorSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

/-- The actual adjoint of any chosen genuine master response has a uniformly
quadratic parallel-center remainder derivative, with no frame derivative bound. -/
theorem uniform_normalFrame_parallel_adjoint_taylor_slice {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CJ : ℝ) (hCJ : 0 ≤ CJ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∀ (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
        (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
        (V : Set NormalFrameParameter) (hV : IsOpen V)
        (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
        (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
        (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (hR : ContDiffOn ℝ ∞ R V)
        (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)))
        (hPoint : ‖normalFrameRadialTaylorFamily d R (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ CJ*(d.radius y)^2),
      ‖fderiv ℝ (fun t => normalFrameRadialAdjointTaylorFamily d
        (commonSupportRadialAdjointFamily A hA S hS hz R)
          (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖ ≤ C*(d.radius y)^2*‖a‖ := by
  obtain ⟨ηB,C1,CQ,hηB,hC1,hCQ,hDataB⟩ := uniform_parallel_one_boundary_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CF,hηF,hCF,hDataF⟩ := uniform_normalFrame_parallel_taylor_slice hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CP,F0,hηP,hCP,hF0,hDataP⟩ := uniform_normalized_adjoint_point_control (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ CJ hCJ
  let CB := 6*parallelFirstModelDerivativeBudget (by omega : 2 ≤ m) K M
  let Q := radialAdjointDerivativeBudget (C1+CQ) CQ CF CB
  let C := radialAdjointJetBudget CP*Q
  have hCB : 0 ≤ CB := by dsimp [CB,parallelFirstModelDerivativeBudget];positivity
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  have hQ : 0 ≤ Q := by dsimp [Q,radialAdjointDerivativeBudget];positivity
  have hC : 0 ≤ C := by dsimp [C,radialAdjointJetBudget];positivity
  refine ⟨min (min ηB ηF) (min ηP 1),C,lt_min (lt_min hηB hηF) (lt_min hηP zero_lt_one),hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy a A hA S hS hz V hV hp0 hRep R hR hRestrict hPoint
  have hSmallB := hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hSmallF := hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hSmallP := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hyΩ := hd.2.1.center_mem hy
  obtain ⟨B,B1,BD,hB,hB1,hBD,SB,hSB,hzB,hzB1,hzBD,W,hW,h0W,hWY,hRepB,hRepB1,hField,hFirstB,hResidualB,hPrincipalB,hTaylorB⟩ :=
    hDataB floor hf ε hε hSmallB d hd y hy a
  let c := normalFrameParallelCurve d.γ d.frame d.radius y a
  let ell := parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y)
  let D := fun t => R (c t)+sphereSobolevDegreeL
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcD := (hasDerivAt_normalFrameParallelCurve d.γ d.frame d.radius y a).differentiableAt
  have hc : ContinuousAt c 0 := (hasDerivAt_normalFrameParallelCurve d.γ d.frame d.radius y a).continuousAt
  have h0V : c 0 ∈ V := by simpa only [c,normalFrameParallelCurve_zero] using hp0
  have hD : DifferentiableAt ℝ D 0 :=
    (((hR.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp)).comp 0 hcD).add (differentiableAt_const _)
  have hEll : DifferentiableAt ℝ ell 0 :=
    (hasDerivAt_parallelFirstCoefficientCovector d.γ d.g₁ y a (frameVectorLinear d.frame y)
      ((hd.1.firstDensityLogDifferential_smooth hKpos hΩ).contDiffAt (hΩ.mem_nhds hyΩ))).differentiableAt
  have hEll0 : ell 0 = firstDensityLogCovector d y :=
    hd.1.parallelFirstCoefficientCovector_zero hΩ hKpos hyΩ a
  have hModel (t : ℝ) (ht : t ∈ W) (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) :
      B1 (t,z) = ell t z • (1:Mat) := (hRepB1 t ht z hzBall).eq_of_nhds
  obtain ⟨hRepP,hRepP1⟩ := hd.1.parallel_coefficient_pair_point_germs hΩ hKpos hyΩ a B B1 hB hB1 SB SB hSB hSB hzB hzB1
    (fun z hz => hRepB 0 h0W z hz) (fun z hz => hRepB1 0 h0W z hz)
  have hPointD : ‖D 0-sphereSobolevDegreeL-r • (radialCorrectionCovectorL (firstDensityLogCovector d y)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*r^2 := by
    have hEq : D 0-sphereSobolevDegreeL-r • (radialCorrectionCovectorL (firstDensityLogCovector d y)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) =
        normalFrameRadialTaylorFamily d R (y,(d.radius y,frameVectorLinear d.frame y)) := by
      dsimp [D,c]
      rw [normalFrameParallelCurve_zero]
      unfold normalFrameRadialTaylorFamily
      rw [hd.1.normalFrameFirstCovector_actual hΩ hKpos hyΩ]
      module
    rw [hEq]
    exact hPoint
  obtain ⟨hInv0,hPC⟩ := hDataP floor hf ε hε hSmallP d hd y hy _ _ hRepP hRepP1 (D 0) hPointD
  have hPC' : RadialAdjointTaylorPointControl (commonSupportMatrixFamily 2 B hB SB hSB hzB 0)
      (commonSupportMatrixFamily 2 B1 hB1 SB hSB hzB1 0) (D 0) (ell 0) r CP := by
    rw [hEll0];exact hPC
  obtain ⟨hFdiff,hFnorm⟩ := hDataF floor hf ε hε hSmallF d hd y hy a A hA S hS hz V hV hp0 hRep R hRestrict
  have hFEq : (fun t => D t-sphereSobolevDegreeL-r •
      (radialCorrectionCovectorL (ell t)).comp (sphereSobolevInclusionL 1 0 (by norm_num))) =
      (fun t => normalFrameRadialTaylorFamily d R (c t)) := by
    funext t
    rw [normalFrameRadialTaylorFamily_parallel]
    dsimp [D,c,ell,r]
    rw [radialCorrectionCovectorL_apply]
    module
  have hForward : ‖fderiv ℝ (fun t => D t-sphereSobolevDegreeL-r •
      (radialCorrectionCovectorL (ell t)).comp (sphereSobolevInclusionL 1 0 (by norm_num))) 0‖ ≤ (CF*‖a‖)*r^2 := by
    rw [hFEq]
    exact hFnorm.trans_eq (by ring)
  have hFirst : ‖fderiv ℝ (fun t => radialCorrectionCovectorL (ell t)) 0‖ ≤ CB*‖a‖ :=
    hd.1.parallel_first_correction_derivative_bound hΩ hK (by omega) hyΩ a
  have hPrincipal : CommonSupportOneBoundaryDerivativeBounds B hB SB hSB hzB (((C1+CQ)*‖a‖)*r) := by
    convert hPrincipalB using 1 <;> ring
  have hResidual : CommonSupportOneBoundaryTaylorDerivativeBounds B B1 hB hB1 SB SB hSB hSB hzB hzB1 r ((CQ*‖a‖)*r^2) := by
    convert hTaylorB using 1 <;> ring
  have hBound := commonSupport_radial_adjoint_taylor_derivative_le B B1 hB hB1 SB SB hSB hSB hzB hzB1
    D ell hD hEll W hW h0W hModel F0 hF0 hInv0 r CP ((C1+CQ)*‖a‖) (CQ*‖a‖) (CF*‖a‖) (CB*‖a‖)
    hr.le hr1 hCP (by positivity) (by positivity) (by positivity) (by positivity)
    hPC' hPrincipal hResidual hForward hFirst
  have hValue (t : ℝ) (ht : t ∈ W) (hcV : c t ∈ V) (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) :
      A (c t,z) = B (t,z) :=
    ((hRep (c t) hcV z hzBall).eq_of_nhds).trans
      ((normalFrameNormalizedCoefficient_parallel d.γ d.g₁ d.expMap d.frame d.radius y a z t).trans
        (hRepB t ht z hzBall).eq_of_nhds.symm)
  have hGerm := commonSupport_radial_adjoint_curve_germ_congr A hA S hS hz B hB SB hSB hzB
    c hc V hV h0V W hW h0W hValue (fun p => R p+sphereSobolevDegreeL)
  have hTaylor : (fun t => normalFrameRadialAdjointTaylorFamily d (commonSupportRadialAdjointFamily A hA S hS hz R) (c t)) =ᶠ[𝓝 (0:ℝ)]
      fun t => radialAdjointFromResponseL (commonSupportMatrixFamily 2 B hB SB hSB hzB t) (D t)-sphereSobolevDegreeL-r •
        (radialCorrectionCovectorL (ell t)).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    filter_upwards [hGerm] with t ht
    have hEq := congrArg₂ (fun (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (U : SphereSobolev 0 →L[ℝ] SphereSobolev 0) => T-sphereSobolevDegreeL-r •
          U.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) ht
      (radialCorrectionCovectorL_apply (ell t)).symm
    exact (normalFrameRadialAdjointTaylorFamily_parallel d (commonSupportRadialAdjointFamily A hA S hS hz R) y a t).trans hEq
  rw [hTaylor.fderiv_eq]
  exact hBound.trans_eq (by dsimp [C,Q,radialAdjointDerivativeBudget];ring)

end ShrinkingSpheres
