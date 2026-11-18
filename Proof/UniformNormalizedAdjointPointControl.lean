import Proof.RadialAdjointTaylorPointControl
import Proof.NormalizedStrongTaylorPointData
import Proof.NormalizedCoefficientBoundaryData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevDegreeL

/-- Uniform point controls for every genuine normalized coefficient and
    first-model representative, keeping any chosen forward radial response. -/
theorem uniform_normalized_adjoint_point_control {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CJ : ℝ) (hCJ : 0 ≤ CJ) :
    ∃ η C : ℝ,∃ F0 : SmoothCoefficientMatrix 2,0 < η ∧ 0 ≤ C ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ F F1 : SmoothCoefficientMatrix 2,
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 z]
        (fun w => normalizedFirstNormalCoefficient d y w i j)) →
      (∀ z ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 z]
        (fun w => firstDensityLogCovector d y w*(1:Mat) i j)) →
      ∀ D : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ‖D-sphereSobolevDegreeL-d.radius y • (radialCorrectionCovectorL (firstDensityLogCovector d y)).comp
        (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 →
      (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible ∧
        RadialAdjointTaylorPointControl F F1 D (firstDensityLogCovector d y) (d.radius y) C := by
  obtain ⟨ηS,CS,P,Q,F0,hηS,hCS,hP,hQ,hF0,hPoint⟩ :=
    uniform_normalized_strong_taylor_point_data (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  let PG := K^2*|M ⟨1,by omega⟩|
  let PB := P+PG
  let L := (73*36)*PB+(73*36)*Q
  let δ := (2*(L+1))⁻¹
  let C := radialAdjointPointBudget PB Q CJ
  have hPG : 0 ≤ PG := by dsimp [PG];positivity
  have hPB : 0 ≤ PB := add_nonneg hP hPG
  have hL : 0 ≤ L := by dsimp [L];positivity
  have hδ : 0 < δ := by dsimp [δ];positivity
  have hCG := boundaryTangentialCoarseBudget_nonneg
  have hCA := boundaryTangentialAdjointBudget_nonneg
  have hC : 0 ≤ C := by dsimp [C,radialAdjointPointBudget];positivity
  refine ⟨min (min ηS ηE) (min 1 δ),C,F0,lt_min (lt_min hηS hηE) (lt_min zero_lt_one hδ),hC,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy F F1 hRep hRep1 D hJ
  obtain ⟨hInv,hNI,hInv0,hNI0,hV1,hD1,hVR,hDR⟩ :=
    hPoint floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy F F1 hRep hRep1
  let r := d.radius y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrδ : r ≤ δ := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hEq : (2*(L+1))*δ = 1 := mul_inv_cancel₀ (by positivity)
  have hSmallL : L*r ≤ (1/2:ℝ) :=
    (mul_le_mul_of_nonneg_left hrδ hL).trans (by nlinarith only [hEq,hδ.le])
  have hEll := hElliptic floor hf ε hε (hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith [sq_nonneg (K-1)]
  have hField (z : X) (hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F z = normalizedFirstNormalCoefficient d y z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hUE := normalized_coefficient_uniformlyElliptic d y F (4*K^2) hKP hEll hField
  have hFirst (w : UnitSphere) : coefficientMatrixField 2 F1 w.val = firstDensityLogCovector d y w.val • (1:Mat) := by
    ext i j
    exact (hRep1 w.val (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)) i j).eq_of_nhds
  have hPP : P ≤ PB := le_add_of_nonneg_right hPG
  have hEllNorm : ‖firstDensityLogCovector d y‖ ≤ PB :=
    (hd.1.norm_firstDensityLogCovector_le hΩ hK (by omega) (hd.2.1.center_mem hy)).trans (le_add_of_nonneg_left hP)
  refine ⟨hInv0,radial_adjoint_taylor_point_control_of_local_C1 F F0 F1 D
    (firstDensityLogCovector d y) r PB Q CJ _ _ hr.le hr1 hPB hQ hCJ hF0 hFirst hUE
    (fun i j z hz => (hV1 i j z hz).trans hPP) (fun i j z hz => (hD1 i j z hz).trans hPP)
    ?_ ?_ hEllNorm hJ hSmallL⟩
  · simpa only [one_smul] using hVR
  · simpa only [one_smul] using hDR

end ShrinkingSpheres
