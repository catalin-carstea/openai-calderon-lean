import Proof.UniformCenterVectorCoefficients
import Proof.PhysicalRadialAdjointTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem norm_radial_adjoint_of_quadratic_taylor
    (Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (B : SphereSobolev 0 →L[ℝ] SphereSobolev 0) (r CB CJ : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hCB : 0 ≤ CB) (hCJ : 0 ≤ CJ) (hB : ‖B‖ ≤ CB)
    (hR : ‖Da-sphereSobolevDegreeL-r • B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*r^2) :
    ‖Da‖ ≤ 2+CB+CJ := by
  let T := B.adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))
  have hT : ‖T‖ ≤ CB :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul ((ContinuousLinearMap.adjoint.norm_map B).le.trans hB)
        (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (norm_nonneg _) hCB).trans_eq (mul_one _))
  have hScale : ‖r • T‖ ≤ CB := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hT hr).trans
      ((mul_le_mul_of_nonneg_right hr1 hCB).trans_eq (one_mul _))
  have hSq : r^2 ≤ 1 := by nlinarith
  have hRem : ‖Da-sphereSobolevDegreeL-r • T‖ ≤ CJ :=
    hR.trans ((mul_le_mul_of_nonneg_left hSq hCJ).trans_eq (mul_one _))
  have hEq : Da = (sphereSobolevDegreeL+r • T)+(Da-sphereSobolevDegreeL-r • T) := by abel
  calc
    _ = ‖(sphereSobolevDegreeL+r • T)+(Da-sphereSobolevDegreeL-r • T)‖ := congrArg norm hEq
    _ ≤ (‖sphereSobolevDegreeL‖+‖r • T‖)+‖Da-sphereSobolevDegreeL-r • T‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add norm_sphereSobolevDegreeL_le_two hScale) hRem

/-- A uniformly small adjoint for the actual Jacobi center coefficient, using
    the same genuine physical radial response and its L2 adjoint. -/
theorem uniform_center_boundary_error_adjoint {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CE : ℝ,0 < η ∧ 0 ≤ CD ∧ 0 ≤ CE ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,
      ∃ D Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,∃ F : I → SmoothCoefficientJets 2,
        ‖Da‖ ≤ CD ∧
        (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (F j) =ᶠ[𝓝 z]
          (fun w => metricPair d.γ y
            ((normalizedParallelCenterJacobian d.γ d.expMap y
              (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
        ‖(d.radius y)⁻¹ • boundaryGradientAdjointL F Da‖ ≤ CE*‖a‖*d.radius y ∧
        (∀ u v,⟪((d.radius y)⁻¹ • boundaryGradientL F D) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,((d.radius y)⁻¹ • boundaryGradientAdjointL F Da) v⟫_ℝ) ∧
        ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
        ∀ f : SphereSobolev (3/2:ℝ),
        (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
          u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
        (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
          (D (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f)) =ᵐ[sphereProbability]
            fun w : UnitSphere => radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u := by
  obtain ⟨ηP,CB,CJ,hηP,hCB,hCJ,hPhysical⟩ := uniform_physical_radial_adjoint_taylor hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηF,CG,hηF,hCG,hCoefficients⟩ := uniform_center_error_vector_coefficients hY hΩ hm K ρ c₀ M Cj hK hρ
  let CD := 2+CB+CJ
  let CE := (73*boundaryTangentialAdjointBudget+438*CD)*CG
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCE : 0 ≤ CE := by
    have := boundaryTangentialAdjointBudget_nonneg
    dsimp only [CE];positivity
  refine ⟨min ηP (min ηF 1),CD,CE,lt_min hηP (lt_min hηF zero_lt_one),hCD,hCE,?_⟩
  intro floor hf ε hε hSmall d hd y hy a
  have hPHere := hPhysical floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨D,Da,B,hB,hTaylor,hPair,hReal⟩ := hPHere
  have hFHere := hCoefficients floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a
  obtain ⟨F,hRep,hBound,hReconstruct⟩ := hFHere
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hDa : ‖Da‖ ≤ CD := norm_radial_adjoint_of_quadratic_taylor Da B (d.radius y) CB CJ hr.le hr1 hCB hCJ hB hTaylor
  have hAdjoint := norm_boundaryGradientAdjointL_local_C1 F Da (CG*‖a‖*(d.radius y)^2) (by positivity) hBound
  have hSmallAdjoint : ‖(d.radius y)⁻¹ • boundaryGradientAdjointL F Da‖ ≤ CE*‖a‖*d.radius y := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ (d.radius y)⁻¹*((73*boundaryTangentialAdjointBudget+438*CD)*(CG*‖a‖*(d.radius y)^2)) := by
        gcongr
        exact hAdjoint.trans (by gcongr)
      _ = _ := by dsimp only [CE];field_simp <;> ring
  refine ⟨D,Da,F,hDa,hRep,hSmallAdjoint,?_,hReal⟩
  intro u v
  have h := congrArg (fun t : ℝ => (d.radius y)⁻¹*t) (boundaryGradientL_adjoint F D Da hPair u v)
  simpa only [_root_.smul_apply,real_inner_smul_left,inner_smul_right] using h

end ShrinkingSpheres
