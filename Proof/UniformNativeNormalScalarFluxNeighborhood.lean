import Proof.UniformRelativeRadialGaussDomain
import Proof.RelativeNormalScalarMultiplierIdentification
import Proof.RadialConormalConjugation
import Proof.NativeRelativeTrueAdjointDomain
import Proof.NativeRelativeFullAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

theorem uniform_native_normal_scalar_flux_neighborhood {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ (F0 : SmoothCoefficientMatrix 2) (CQ CI CW CF CA CM CR : ℝ),
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ R : RelativeNormalScalarRemainderFamily d y CR,∀ Q : SmoothCoefficientJets 2,
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) →
      ∀ V : s.response.SymmetricAdjointDomain,
      ∃ W : Set NormalFrameRelativeParameter,IsOpen W ∧ ((y,frameVectorLinear d.frame y),0) ∈ W ∧ W ⊆ V.domain ∧
        ∀ p ∈ W,
          (s.response.fullAdjoint p).comp (closedOneBoundaryScalarMultiplierL (R.normalCoefficient Q p))=
            (closedThreeJetCoarseScalarMultiplierL (R.normalCoefficient Q p)).comp (s.response.response p+sphereSobolevDegreeL) ∧
          (closedThreeJetNegativeScalarMultiplierL (R.normalCoefficient Q p)).IsInvertible := by
  classical
  obtain ⟨η,hη,hGeom⟩ := uniform_relative_radial_gauss_domain hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy F0 CQ CI CW CF CA CM CR s R Q hQ V
  obtain ⟨U,hU,hpU,hUD,hRowU⟩ := hGeom floor hf ε hε hSmall d hd y hy
  let W := U ∩ (V.domain ∩ R.domain)
  refine ⟨W,hU.inter (V.domainOpen.inter R.isOpen),⟨hpU,V.pointMem,R.point⟩,(fun p hp => hp.2.1),?_⟩
  intro p hp
  let F := commonSupportMatrixFamily 2 s.coefficients.a s.coefficients.smooth s.coefficients.support
    s.coefficients.compact s.coefficients.supported p
  have hF (w : UnitSphere) : coefficientMatrixField 2 F w.val=
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) (p,w.val) := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact (s.coefficients.coefficientGerm p (s.response.sub (V.sub hp.2.1)) w.val
      (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property))).eq_of_nhds
  let chi : UnitSphere → ℝ := fun w => Classical.choose (hRowU p hp.1 w.val
    (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)))
  have hChi (w : UnitSphere) : 0 < chi w ∧ ∀ j : I,
      ∑ i : I,w.val i*coefficientMatrixField 2 F w.val i j=chi w*w.val j := by
    have hh := Classical.choose_spec (hRowU p hp.1 w.val
      (Metric.closedBall_subset_closedBall (by norm_num) (Metric.sphere_subset_closedBall w.property)))
    refine ⟨hh.1,?_⟩
    intro j
    exact (congrArg (fun A : Mat => ∑ i : I,w.val i*A i j) (hF w)).trans (hh.2 j)
  have hRow (w : UnitSphere) (j : I) : ∑ i : I,w.val i*coefficientValue 2 (F i j) w.val=chi w*w.val j := (hChi w).2 j
  have hNormal := boundaryNormalCoefficient_of_radial_row F chi hRow
  obtain ⟨hT,hTa⟩ := radial_row_tangential_operators_zero F chi hRow
  have hPos (w : UnitSphere) : 0 < coefficientValue 2 (normalCoefficientJet F) w.val := by
    rw [coefficientValue_normalCoefficientJet,hNormal w]
    exact (hChi w).1
  have hOne := R.normalCoefficient_one_multiplier_at_parameter Q hQ p hp.2.2 F hF
  have hCoarse := R.normalCoefficient_coarse_multiplier_at_parameter Q hQ p hp.2.2 F hF
  have hNeg := R.normalCoefficient_negative_multiplier_at_parameter Q hQ p hp.2.2 F hF
  constructor
  · have hFlux := radialAdjointFromResponse_tangent_zero_flux F hT hTa
      (oneBoundaryCoefficientMulL_isInvertible_of_pos _ hPos) (s.response.response p+sphereSobolevDegreeL)
    exact (congrArg (fun MM : SphereSobolev 1 →L[ℝ] SphereSobolev 1 => (s.response.fullAdjoint p).comp MM) hOne).trans
      (hFlux.trans (congrArg (fun MM : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
        MM.comp (s.response.response p+sphereSobolevDegreeL)) hCoarse.symm))
  · have hActual := V.normal p hp.2.1
    exact hNeg.symm ▸ hActual
end ShrinkingSpheres
