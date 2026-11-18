import Proof.NormalFrameCoefficientFamily
import Proof.CommonSupportMidpointNeighborhood
import Proof.NormalizedMidpointRadialRealization
import Proof.NormalizedCoefficientBoundaryData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- A genuine smooth midpoint radial family with independent center, radius
    and frame parameters, realizing the unchanged actual response at every
    actual profile parameter in its neighborhood. -/
theorem uniform_normalFrame_local_radial_family {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ A : NormalFrameParameter × X → Mat,∃ hA : ContDiff ℝ ∞ A,
      ∃ S : Set X,∃ hS : IsCompact S,∃ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∃ V : Set NormalFrameParameter,IsOpen V ∧ (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V ∧
        (∀ p ∈ V,p.1 ∈ Y) ∧
        (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
          A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) ∧
      ∃ R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,ContDiffOn ℝ ∞ R V ∧
        (∀ x : X,(x,(d.radius x,frameVectorLinear d.frame x)) ∈ V →
          RealizesActualMidpointRadialError d x (R (x,(d.radius x,frameVectorLinear d.frame x)))) ∧
        (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
          (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) ∧
        (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) ∧
        (∀ p ∈ V,(negativeBoundaryCoefficientMulL
          (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) ∧
        ∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
            (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p)) := by
  obtain ⟨ηF,hηF,hFamily⟩ := uniform_normalFrame_coefficient_family hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨min ηF ηE,lt_min hηF hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,hA,S,hS,hz,V0,hV0,hpV0,hCenter,hRep⟩ := hFamily floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  have hPoint (z : X) (hzBall : z ∈ (ballOpens:Set X)) : A (p0,z) = normalizedFirstNormalCoefficient d y z :=
    ((hRep p0 hpV0 z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds).trans
      (normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame y z (d.radius y))
  let KP := 4*K^2
  let lam := (metricDensityBudget KP)⁻¹*KP⁻¹
  let Lam := metricDensityBudget KP*KP
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy d.g₁ (by simp)
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (fun z => A (p0,z))
      ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*lam) ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*Lam) := by
    have hField (z : X) (hzBall : z ∈ (ballOpens:Set X)) :
        coefficientMatrixField 2 (F p0) z = normalizedFirstNormalCoefficient d y z := by
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact hPoint z hzBall
    have hHere := normalized_coefficient_uniformlyElliptic d y (F p0) KP hKP hEll hField
    simpa only [F,coefficientMatrixField_commonSupportMatrixFamily] using hHere
  have hCoercive0 : IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p0)) :=
    isCoercive_unitBall_zeroDrift hUE
      (hA.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (commonSupportEnergyMemLp A hA p0)
  have hStrong0 : (strongDirichletOperator fixedSobolevCalculus 0 (F p0)).IsInvertible := by
    apply strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 (F p0)
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hUE
  have hNormal0 : (negativeBoundaryCoefficientMulL (normalCoefficientJet (F p0))).IsInvertible := by
    apply negativeNormalCoefficient_isInvertible (F p0) (normalCoefficientJet (F p0))
      (coefficientSmoothData_normalCoefficientJet (F p0))
      ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*lam) ((firstMetricDensityFactor d.γ d.g₁ y)⁻¹*Lam)
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hUE
  obtain ⟨V,hV,hpV,hSub,hCoercive,hStrong,hNormal,R,hR,hRestrict⟩ :=
    exists_commonSupport_midpoint_neighborhood A hA S hS hz p0 V0 hV0 hpV0 hCoercive0 hStrong0 hNormal0
  have hActual (x : X) (hx : (x,(d.radius x,frameVectorLinear d.frame x)) ∈ V) :
      RealizesActualMidpointRadialError d x (R (x,(d.radius x,frameVectorLinear d.frame x))) := by
    let px : NormalFrameParameter := (x,(d.radius x,frameVectorLinear d.frame x))
    have hFieldX (z : X) (hzBall : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F px) z = normalizedFirstNormalCoefficient d x z := by
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact ((hRep px (hSub hx) z (unitBall_subset_closedBall_two hzBall)).eq_of_nhds).trans
        (normalFrameNormalizedCoefficient_framed d.γ d.g₁ d.expMap d.frame x z (d.radius x))
    exact realizesActualMidpointRadialError_of_normalized_restriction d x (R px) (F px) hFieldX (hStrong px hx) (hRestrict px hx)
  exact ⟨A,hA,S,hS,hz,V,hV,hpV,(fun p hp => hCenter p (hSub hp)),
    (fun p hp => hRep p (hSub hp)),R,hR,hActual,hStrong,hCoercive,hNormal,hRestrict⟩

end ShrinkingSpheres
