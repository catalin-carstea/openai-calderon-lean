import Proof.OrthogonalCoefficientEllipticity
import Proof.NormalFrameRadialRotationCovariance
import Proof.NormalFrameRadialAdjointLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local irreducible] sphereSobolevDegreeL
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The actual native adjoint pairing holds along every rotated frame that
remains in the master neighborhood, with the unchanged chosen response. -/
theorem uniform_normalFrame_rotated_radial_adjoint_pairing {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ A : NormalFrameParameter × X → Mat,∀ hA : ContDiff ℝ ∞ A,
      ∀ S : Set X,∀ hS : IsCompact S,∀ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∀ V : Set NormalFrameParameter,(y,(d.radius y,frameVectorLinear d.frame y)) ∈ V →
      (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,
        A =ᶠ[𝓝 (p,z)] normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap) →
      ∀ R : NormalFrameParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ p ∈ V,IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp A hA p))) →
      (∀ p ∈ V,(strongDirichletOperator fixedSobolevCalculus 0
        (commonSupportMatrixFamily 2 A hA S hS hz p)).IsInvertible) →
      (∀ p ∈ V,(negativeBoundaryCoefficientMulL
        (normalCoefficientJet (commonSupportMatrixFamily 2 A hA S hS hz p))).IsInvertible) →
      (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
          (actualHighRadialErrorL (commonSupportMatrixFamily 2 A hA S hS hz p))) →
      ∀ i j : I,∀ θ : ℝ,normalFrameRotationCurve d.frame d.radius y i j θ ∈ V →
      ∀ u v,
        let p := normalFrameRotationCurve d.frame d.radius y i j θ
        ⟪(R p+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,commonSupportRadialAdjointFamily A hA S hS hz R p v⟫_ℝ := by
  obtain ⟨η,hη,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hp0 hRep R hCoercive hStrong hNormal hRestrict i j θ hθ
  let p := normalFrameRotationCurve d.frame d.radius y i j θ
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let e := coordinateRotationIsometry i j θ
  let F := commonSupportMatrixFamily 2 A hA S hS hz
  let a := normalizedFirstNormalCoefficient d y
  let KP := 4*K^2
  let c := (firstMetricDensityFactor d.γ d.g₁ y)⁻¹
  let lam := c*((metricDensityBudget KP)⁻¹*KP⁻¹)
  let Lam := c*(metricDensityBudget KP*KP)
  have hKP : 1 ≤ KP := by dsimp [KP];nlinarith [sq_nonneg (K-1)]
  have hEll := hElliptic floor hf ε hε hSmall d hd y hy d.g₁ (by simp)
  have hUE0 : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) a lam Lam :=
    uniformlyEllipticOn_positive_const_smul ((hEll.principalCoefficient_tau hKP).mono_set unitBall_subset_closedBall_two)
      c (inv_pos.mpr (firstMetricDensityFactor_pos _ _ _))
  have hBaseSymm (z : X) (hzB : z ∈ (ballOpens:Set X)) : (a z).IsSymm := by
    change (c • (OAI.AnisotropicCalderon.vol _ z •
      ((framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z)⁻¹)).IsSymm
    have hSym : ((framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z).IsSymm :=
      (hEll.2 z (unitBall_subset_closedBall_two hzB)).1
    exact (hSym.inv.smul _).smul _
  have hRotField (z : X) (hzB : z ∈ (ballOpens:Set X)) :
      coefficientMatrixField 2 (F p) z = orthogonalPrincipalCoefficient e a z := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    apply ((hRep p hθ z (unitBall_subset_closedBall_two hzB)).eq_of_nhds).trans
    have hRot := normalFrameNormalizedCoefficient_coordinate_rotation d.γ d.g₁ d.expMap
      y (d.radius y) (frameVectorLinear d.frame y) i j θ z
    apply hRot.trans
    rw [← coordinateRotationPrincipalFamily_eq_orthogonal i j (fun v : ℝ × X => a v.2) θ (0:ℝ) z]
    change (coordinateRotationMatrix i j θ).transpose*
      normalFrameNormalizedCoefficient d.γ d.g₁ d.expMap (p0,coordinateRotation i j θ z)*coordinateRotationMatrix i j θ = _
    rw [normalFrameNormalizedCoefficient_framed]
    rfl
  have hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (coefficientMatrixField 2 (F p)) lam Lam :=
    (uniformlyEllipticOn_orthogonal_unitBall e a lam Lam hUE0).congr hRotField
  have hPos (w : UnitSphere) : 0 < coefficientValue 2 (normalCoefficientJet (F p)) w.val := by
    rw [coefficientValue_normalCoefficientJet]
    exact boundaryNormalCoefficientData_pos (F p) lam Lam hUE w
  have hSym : ∀ᵐ z ∂((volume:Measure X).restrict ballOpens),(A (p,z)).IsSymm := by
    filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with z hzB
    have hez : e z ∈ (ballOpens:Set X) := by
      change e z ∈ Metric.ball (0:X) 1
      have hzBall : z ∈ Metric.ball (0:X) 1 := hzB
      simpa only [Metric.mem_ball,dist_zero_right,e.norm_map] using hzBall
    have hAField : A (p,z) = orthogonalPrincipalCoefficient e a z :=
      (congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 A hA S hS hz p) z).symm.trans (hRotField z hzB)
    rw [hAField]
    exact orthogonalPrincipalCoefficient_isSymm e a z (hBaseSymm _ hez)
  exact midpoint_radialAdjointFromResponse_pairing (commonSupportEnergyMemLp A hA p) (hCoercive p hθ) hSym
    (F p) (fun z _ => congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 A hA S hS hz p) z)
    (hStrong p hθ) (hNormal p hθ) hPos (R p) (hRestrict p hθ)

end ShrinkingSpheres
