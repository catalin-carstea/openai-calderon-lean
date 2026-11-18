import Proof.CompletedNormalCoefficientFamily
import Proof.RadialConormalConjugation
import Proof.UniformActualRadialBoundaryCoefficient
import Proof.NativeRelativePhysicalRadialIdentification
import Proof.NativeRelativeFullAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_native_normal_scalar_flux {Y Ω : Set X}
    (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (F0 : SmoothCoefficientMatrix 2) (CQ CI CW CF CA CM C : ℝ),
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ R : RelativeNormalScalarRemainderFamily d y C,∀ Q : SmoothCoefficientJets 2,
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) →
      let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      (s.response.fullAdjoint p).comp (closedOneBoundaryScalarMultiplierL (R.normalCoefficient Q p))=
        (closedThreeJetCoarseScalarMultiplierL (R.normalCoefficient Q p)).comp (s.response.response p+sphereSobolevDegreeL) ∧
      (closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).IsInvertible := by
  obtain ⟨η,hη,hProduce⟩ := uniform_actual_radial_boundary_coefficient (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM C s R Q hQ p
  let F := commonSupportMatrixFamily 2 s.coefficients.a s.coefficients.smooth
    s.coefficients.support s.coefficients.compact s.coefficients.supported p
  have hKpos := zero_lt_one.trans_le hK
  have hyΩ := hd.2.1.center_mem hy
  obtain ⟨hRep,_⟩ := s.coefficients.actual_point_germs hΩ hd.1 hKpos hyΩ (by norm_num)
  have hF (w : UnitSphere) : coefficientMatrixField 2 F w.val=normalizedFirstNormalCoefficient d y w.val := by
    ext i j
    exact (hRep w.val (Metric.closedBall_subset_closedBall (by norm_num)
      (Metric.sphere_subset_closedBall w.property)) i j).eq_of_nhds
  obtain ⟨hNormal,hT,hTa,hPos⟩ := hProduce floor hf ε hε hSmall d hd y hy F hF
  have hNormalPos (w : UnitSphere) : 0 < coefficientValue 2 (normalCoefficientJet F) w.val := by
    rw [coefficientValue_normalCoefficientJet,hNormal w]
    exact hPos w
  have hOne := R.normalCoefficient_point_one_multiplier Q hQ hΩ hd.1 hKpos hyΩ F hF
  have hCoarse := R.normalCoefficient_point_coarse_multiplier Q hQ hΩ hd.1 hKpos hyΩ F hF
  have hNeg := R.normalCoefficient_point_negative_multiplier Q hQ hΩ hd.1 hKpos hyΩ F hF
  constructor
  · have hFlux := radialAdjointFromResponse_tangent_zero_flux F hT hTa
      (oneBoundaryCoefficientMulL_isInvertible_of_pos _ hNormalPos) (s.response.response p+sphereSobolevDegreeL)
    rw [← hOne,← hCoarse] at hFlux
    exact hFlux
  · rw [hNeg]
    rw [← commonSupport_negative_normal_multiplier_eq]
    exact s.point.normal
end ShrinkingSpheres
