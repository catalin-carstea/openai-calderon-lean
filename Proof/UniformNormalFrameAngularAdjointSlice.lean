import Proof.UniformRotatedOneBoundaryTaylorData
import Proof.UniformNormalFrameAngularTaylorJet
import Proof.CommonSupportCoefficientPointGerms
import Proof.UniformNormalizedAdjointPointControl
import Proof.CommonSupportRadialAdjointTaylorDerivative
import Proof.UniformNormalFrameTaylorSlices
import Proof.ParallelCoefficientPointGerms
import Proof.NormalFrameRadialAdjointLift
import Proof.RotationFirstCorrectionDerivative
import Proof.RadialAdjointCurveCongruence
import Proof.NormalFrameAdjointRotationModel

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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevDegreeL

/-- The actual adjoint of any chosen genuine master response has a uniformly
quadratic coordinate-rotation remainder derivative, with no frame derivative bound. -/
theorem uniform_normalFrame_angular_adjoint_taylor_slice {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CJ : ℝ) (hCJ : 0 ≤ CJ) :
    ∃ η C : ℝ,0 < η ∧ 0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ i j : I,
      ∀ (A : NormalFrameParameter × X → Mat) (hA : ContDiff ℝ ∞ A)
        (S : Set X) (hS : IsCompact S) (hz : ∀ p z,z ∉ S → A (p,z) = 0)
        (V : Set NormalFrameParameter) (hV : IsOpen V)
        (hp0 : (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V)
        (hRep : ∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap)
        (R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (hR : ContDiffOn ℝ ∞ R V)
        (hCoercive : ∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p)))
        (hStrong : ∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible)
        (hRestrict : ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)))
        (hPoint : ‖normalFrameRadialTaylorFamily d R (y,(d.radius y,frameVectorLinear d.frame y))‖ ≤ CJ*(d.radius y)^2),
      ‖fderiv ℝ (fun t => normalFrameRadialAdjointTaylorFamily d
        (commonSupportRadialAdjointFamily A hA S hS hz R)
          (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨ηB,C1,CQ,hηB,hC1,hCQ,hDataB⟩ := uniform_rotated_one_boundary_taylor_data hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CP0,CF,hηF,hCP0,hCF,hDataF⟩ := uniform_normalFrame_angular_radial_taylor_jet hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,CP,F0,hηP,hCP,hF0,hDataP⟩ := uniform_normalized_adjoint_point_control (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ CJ hCJ
  let PG := K^2*|M ⟨1,by omega⟩|
  let CB := 12*PG
  let Q := radialAdjointDerivativeBudget (C1+CQ) CQ CF CB
  let C := radialAdjointJetBudget CP*Q
  have hCB : 0 ≤ CB := by dsimp [CB,PG];positivity
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  have hQ : 0 ≤ Q := by dsimp [Q,radialAdjointDerivativeBudget];positivity
  have hC : 0 ≤ C := by dsimp [C,radialAdjointJetBudget];positivity
  refine ⟨min (min ηB ηF) (min ηP 1),C,lt_min (lt_min hηB hηF) (lt_min hηP zero_lt_one),hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy i j A hA S hS hz V hV hp0 hRep R hR hCoercive hStrong hRestrict hPoint
  have hSmallB := hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hSmallF := hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hSmallP := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hyΩ := hd.2.1.center_mem hy
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let B0 : X → Mat := fun z => A (p0,z)
  have hB0 : ContDiff ℝ ∞ B0 := hA.comp (contDiff_const.prodMk contDiff_id)
  have hCompact0 : HasCompactSupport B0 := HasCompactSupport.of_support_subset_isCompact hS (by
    intro z hzB
    by_contra hzS
    exact hzB (hz p0 z hzS))
  have hRep0 (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) : B0 =ᶠ[𝓝 z] normalizedFirstNormalCoefficient d y := by
    have hNear := (hRep p0 hp0 z hzBall).comp_tendsto
      (show Tendsto (fun w : X => (p0,w)) (𝓝 z) (𝓝 (p0,z)) from
        (continuousAt_const.prodMk continuousAt_id).tendsto)
    filter_upwards [hNear] with w hw
    exact hw.trans (normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame y w (d.radius y))
  obtain ⟨B,B1,BD,hB,hB1,hBD,SB,hSB,hzB,hzB1,hzBD,hRepB,hRepB1,hField,hFirstB,hResidualB,hPrincipalB,hTaylorB⟩ :=
    hDataB floor hf ε hε hSmallB d hd y hy i j B0 hB0 hCompact0 hRep0
  let c := normalFrameRotationCurve d.frame d.radius y i j
  let ell := fun t : ℝ => (firstDensityLogCovector d y).comp
    (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap
  let D := fun t => R (c t)+sphereSobolevDegreeL
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcD := (hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j).differentiableAt
  have hc : ContinuousAt c 0 := (hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j).continuousAt
  have h0V : c 0 ∈ V := by simpa only [c,normalFrameRotationCurve_zero] using hp0
  have hD : DifferentiableAt ℝ D 0 :=
    (((hR.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp)).comp 0 hcD).add (differentiableAt_const _)
  have hEllCurve := hasDerivAt_rotated_covector_zero (firstDensityLogCovector d y) i j
  have hEll : DifferentiableAt ℝ ell 0 := hEllCurve.differentiableAt
  have hEll0 : ell 0 = firstDensityLogCovector d y := by
    ext z
    change firstDensityLogCovector d y (coordinateRotation i j 0 z) = firstDensityLogCovector d y z
    rw [coordinateRotation_zero]
  have hModel (t : ℝ) (_ht : t ∈ (Set.univ:Set ℝ)) (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) :
      B1 (t,z) = ell t z • (1:Mat) := (hRepB1 t z hzBall).eq_of_nhds
  have hRepP := commonSupport_coefficient_point_germs B
    (fun p : ℝ × X => coordinateRotationPrincipalFamily i j
      (fun v : ℝ × X => normalizedFirstNormalCoefficient d y v.2) ((p.1,0),p.2)) hB SB hSB hzB 0
    (normalizedFirstNormalCoefficient d y) (fun z hz => hRepB 0 z hz)
    (fun w => coordinateRotationPrincipalFamily_zero_angle i j _ (0:ℝ) w)
  have hRepP1Raw := commonSupport_coefficient_point_germs B1
    (fun p : ℝ × X => firstDensityLogCovector d y (coordinateRotation i j p.1 p.2) • (1:Mat)) hB1 SB hSB hzB1 0
    (fun w => firstDensityLogCovector d y w • (1:Mat)) (fun z hz => hRepB1 0 z hz)
    (fun w => by rw [coordinateRotation_zero])
  have hRepP1 : ∀ z ∈ Metric.closedBall (0:X) 2,∀ k l,
      coefficientValue 2 (commonSupportMatrixFamily 2 B1 hB1 SB hSB hzB1 0 k l) =ᶠ[𝓝 z]
        (fun w => firstDensityLogCovector d y w*(1:Mat) k l) := by
    simpa only [Matrix.smul_apply,smul_eq_mul] using hRepP1Raw
  have hPointD : ‖D 0-sphereSobolevDegreeL-r • (radialCorrectionCovectorL (firstDensityLogCovector d y)).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*r^2 := by
    have hEq : D 0-sphereSobolevDegreeL-r • (radialCorrectionCovectorL (firstDensityLogCovector d y)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) =
        normalFrameRadialTaylorFamily d R (y,(d.radius y,frameVectorLinear d.frame y)) := by
      dsimp [D,c]
      rw [normalFrameRotationCurve_zero]
      unfold normalFrameRadialTaylorFamily
      rw [hd.1.normalFrameFirstCovector_actual hΩ hKpos hyΩ]
      module
    rw [hEq]
    exact hPoint
  obtain ⟨hInv0,hPC⟩ := hDataP floor hf ε hε hSmallP d hd y hy _ _ hRepP hRepP1 (D 0) hPointD
  have hPC' : RadialAdjointTaylorPointControl (commonSupportMatrixFamily 2 B hB SB hSB hzB 0)
      (commonSupportMatrixFamily 2 B1 hB1 SB hSB hzB1 0) (D 0) (ell 0) r CP := by
    rw [hEll0];exact hPC
  have hForwardData := hDataF floor hf ε hε hSmallF d hd y hy A hA S hS hz V hV hp0 hRep R hR hCoercive hStrong hRestrict
  have hFnorm := (hForwardData.2 i j).1
  have hFEq : (fun t => D t-sphereSobolevDegreeL-r •
      (radialCorrectionCovectorL (ell t)).comp (sphereSobolevInclusionL 1 0 (by norm_num))) =
      (fun t => normalFrameRadialTaylorFamily d R (c t)) := by
    funext t
    rw [hd.1.normalFrameRadialTaylorFamily_rotation hΩ hKpos hyΩ]
    dsimp [D,c,ell,r]
    rw [radialCorrectionCovectorL_apply]
    module
  have hForward : ‖fderiv ℝ (fun t => D t-sphereSobolevDegreeL-r •
      (radialCorrectionCovectorL (ell t)).comp (sphereSobolevInclusionL 1 0 (by norm_num))) 0‖ ≤ CF*r^2 := by
    rw [hFEq]
    exact norm_deriv_eq_norm_fderiv.symm.le.trans hFnorm
  have hFirst : ‖fderiv ℝ (fun t => radialCorrectionCovectorL (ell t)) 0‖ ≤ CB :=
    rotation_first_correction_derivative_bound (firstDensityLogCovector d y) i j PG (by dsimp [PG];positivity)
      (hd.1.norm_firstDensityLogCovector_le hΩ hK (by omega) hyΩ)
  have hPrincipal : CommonSupportOneBoundaryDerivativeBounds B hB SB hSB hzB ((C1+CQ)*r) := by
    convert hPrincipalB using 1 <;> ring
  have hResidual : CommonSupportOneBoundaryTaylorDerivativeBounds B B1 hB hB1 SB SB hSB hSB hzB hzB1 r (CQ*r^2) := by
    convert hTaylorB using 1 <;> ring
  have hBound := commonSupport_radial_adjoint_taylor_derivative_le B B1 hB hB1 SB SB hSB hSB hzB hzB1
    D ell hD hEll Set.univ isOpen_univ (mem_univ _) hModel F0 hF0 hInv0 r CP ((C1+CQ)) (CQ) (CF) CB
    hr.le hr1 hCP (by positivity) (by positivity) (by positivity) (by positivity)
    hPC' hPrincipal hResidual hForward hFirst
  have hValue (t : ℝ) (_ht : t ∈ (Set.univ:Set ℝ)) (hcV : c t ∈ V) (z : X) (hzBall : z ∈ Metric.closedBall (0:X) 2) :
      A (c t,z) = B (t,z) := by
    have hRot := normalFrameNormalizedCoefficient_coordinate_rotation d.γ d.g₁ d.expMap
      y (d.radius y) (frameVectorLinear d.frame y) i j t z
    have hTrue : normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap (c t,z) =
        coordinateRotationPrincipalFamily i j (fun v : ℝ × X => normalizedFirstNormalCoefficient d y v.2) ((t,0),z) := by
      apply hRot.trans
      change (coordinateRotationMatrix i j t).transpose*
        normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap (p0,coordinateRotation i j t z)*coordinateRotationMatrix i j t = _
      rw [normalFrameNormalizedCoefficient_framed]
      rfl
    exact ((hRep (c t) hcV z hzBall).eq_of_nhds).trans (hTrue.trans (hRepB t z hzBall).eq_of_nhds.symm)
  have hGerm := commonSupport_radial_adjoint_curve_germ_congr A hA S hS hz B hB SB hSB hzB
    c hc V hV h0V Set.univ isOpen_univ (mem_univ _) hValue (fun p => R p+sphereSobolevDegreeL)
  have hTaylor : (fun t => normalFrameRadialAdjointTaylorFamily d (commonSupportRadialAdjointFamily A hA S hS hz R) (c t)) =ᶠ[𝓝 (0:ℝ)]
      fun t => radialAdjointFromResponseL (commonSupportMatrixFamily 2 B hB SB hSB hzB t) (D t)-sphereSobolevDegreeL-r •
        (radialCorrectionCovectorL (ell t)).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    filter_upwards [hGerm] with t ht
    have hEq := congrArg₂ (fun (T : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
        (U : SphereSobolev 0 →L[ℝ] SphereSobolev 0) => T-sphereSobolevDegreeL-r •
          U.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))) ht
      (radialCorrectionCovectorL_apply (ell t)).symm
    exact (hd.1.normalFrameRadialAdjointTaylorFamily_rotation hΩ hKpos hyΩ (commonSupportRadialAdjointFamily A hA S hS hz R) i j t).trans hEq
  rw [hTaylor.fderiv_eq]
  exact hBound

end ShrinkingSpheres
