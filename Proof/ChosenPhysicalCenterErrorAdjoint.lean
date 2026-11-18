import Proof.PhysicalCenterErrorAdjoint
import Proof.RadialConormalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The physical center-error witnesses and their uniform bounds apply to
    ANY already chosen genuine radial response and its true sphere adjoint.
    Dense uniqueness preserves higher-jet families chosen by other callers. -/
theorem uniform_physical_center_error_of_chosen_radial {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD CE : ℝ,0 < η ∧ 0 ≤ CD ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ R Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      RealizesActualMidpointRadialError d y R →
      (∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) →
      ∃ Fp : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (Fp i j) =ᶠ[𝓝 x]
          (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 Fp).IsInvertible ∧ ‖Da‖ ≤ CD ∧
        (∀ f : SphereSobolev (3/2:ℝ),(R+sphereSobolevDegreeL) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f) =
          sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
            (outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (strongPoissonL Fp f))) ∧
        ∀ a : X,∃ C : I → SmoothCoefficientJets 2,
          (∀ j,∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 (C j) =ᶠ[𝓝 z]
            (fun w => metricPair d.γ y
              ((normalizedParallelCenterJacobian d.γ d.expMap y
                (d.radius y • frameVector d.frame y w)-ContinuousLinearMap.id ℝ X) a) (d.frame y j))) ∧
          ‖(d.radius y)⁻¹ • boundaryGradientAdjointL C Da‖ ≤ CE*‖a‖*d.radius y ∧
          ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
          ∀ f : SphereSobolev (3/2:ℝ),
          (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
            u (normalChart d.expMap d.frame y (d.radius y) w.val)) →
          (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (boundaryGradientL C (R+sphereSobolevDegreeL) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) f))
              =ᵐ[sphereProbability] fun w : UnitSphere =>
                fderiv ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val)
                  ((normalizedParallelCenterJacobian d.γ d.expMap y
                    (d.radius y • frameVector d.frame y w.val)-ContinuousLinearMap.id ℝ X) a) := by
  obtain ⟨η,CD,CB,CJ,CE,hη,hCD,_hCB,_hCJ,hCE,hOld⟩ :=
    uniform_physical_center_error_gradient_adjoint_canonical hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CD,CE,hη,hCD,hCE,?_⟩
  intro floor hf ε hε hSmall d hd y hy R Da hR hPair
  obtain ⟨Fp,D0,Da0,B,hRep,hInv,hDa0,_hB,_hBNorm,_hTaylor,hPair0,hHigh,hCenter⟩ :=
    hOld floor hf ε hε hSmall d hd y hy
  have hField (z : X) (hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 Fp z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hD : R+sphereSobolevDegreeL = D0 :=
    continuousLinearMap_eq_of_high_restriction _ _ (fun f =>
      (hR.full_high d y R Fp hField f).trans (hHigh f).symm)
  have hPair0' : ∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da0 v⟫_ℝ := by rw [hD];exact hPair0
  have hDa : Da = Da0 := radial_physical_adjoint_unique _ Da Da0 hPair hPair0'
  refine ⟨Fp,hRep,hInv,by rw [hDa];exact hDa0,?_,?_⟩
  · rw [hD]
    exact hHigh
  · rw [hD,hDa]
    exact hCenter

end ShrinkingSpheres
