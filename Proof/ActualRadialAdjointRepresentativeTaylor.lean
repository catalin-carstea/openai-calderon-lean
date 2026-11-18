import Proof.UniformActualRadialAdjoint
import Proof.RadialConormalReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The existing canonical adjoint Taylor estimate applies to ANY actual
    radial representative and its true physical adjoint, by dense uniqueness.
    In particular this retains a previously chosen smooth master family. -/
theorem uniform_actual_radial_adjoint_representative_taylor {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CB CJ : ℝ,0 < η ∧ 0 ≤ CB ∧ 0 ≤ CJ ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ R Da : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      RealizesActualMidpointRadialError d y R →
      (∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da v⟫_ℝ) →
      ‖firstRadialCorrectionL d y‖ ≤ CB ∧
      ‖Da-sphereSobolevDegreeL-d.radius y •
        (firstRadialCorrectionL d y).adjoint.comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤ CJ*(d.radius y)^2 := by
  obtain ⟨η,CB,CJ,hη,hCB,hCJ,hPoint⟩ :=
    uniform_actual_midpoint_radial_adjoint_canonical (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CB,CJ,hη,hCB,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy R Da hR hDa
  obtain ⟨F,D0,Da0,hRep,hInv,hB,hTaylor,hPair,hHigh⟩ := hPoint floor hf ε hε hSmall d hd y hy
  have hField (z : X) (hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 F z =
      principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z := by
    ext i j
    exact (hRep z (unitBall_subset_closedBall_two hz) i j).eq_of_nhds
  have hD : R+sphereSobolevDegreeL = D0 := by
    apply continuousLinearMap_eq_of_high_restriction
    intro f
    exact (hR.full_high d y R F hField f).trans (hHigh f).symm
  have hDa0 : ∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Da0 v⟫_ℝ := by
    rw [hD]
    exact hPair
  have hEq := radial_physical_adjoint_unique (R+sphereSobolevDegreeL) Da Da0 hDa hDa0
  refine ⟨hB,?_⟩
  rw [hEq]
  exact hTaylor

end ShrinkingSpheres
