import Proof.NormalFrameRotatedAdjointPairing
import Proof.BoundaryAdjointOrthogonalCovariance

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

/-- True physical adjunction and the native forward covariance give the
rotation covariance of the SAME actual adjoint on the master neighborhood. -/
theorem uniform_normalFrame_radial_adjoint_rotation_covariance {Y Ω : Set X} (hΩ : IsOpen Ω)
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
      (commonSupportRadialAdjointFamily A hA S hS hz R (normalFrameRotationCurve d.frame d.radius y i j θ)).comp
        (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ)) =
      (sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)).comp
        (commonSupportRadialAdjointFamily A hA S hS hz R (y,(d.radius y,frameVectorLinear d.frame y))) := by
  obtain ⟨η,hη,hPair⟩ := uniform_normalFrame_rotated_radial_adjoint_pairing (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hp0 hRep R hCoercive hStrong hNormal hRestrict i j θ hθ
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let pθ := normalFrameRotationCurve d.frame d.radius y i j θ
  let e := coordinateRotationIsometry i j θ
  let P0 := sphereSobolevOrthogonalPullbackL 0 e
  let P1 := sphereSobolevOrthogonalPullbackL 1 e
  have hAdjθ := hPair floor hf ε hε hSmall d hd y hy A hA S hS hz V hp0 hRep R hCoercive hStrong hNormal hRestrict i j θ hθ
  have hZero : normalFrameRotationCurve d.frame d.radius y i j 0 ∈ V := by simpa only [normalFrameRotationCurve_zero] using hp0
  have hAdj0Raw := hPair floor hf ε hε hSmall d hd y hy A hA S hS hz V hp0 hRep R hCoercive hStrong hNormal hRestrict i j 0 hZero
  have hAdj0 : ∀ u v,⟪(R p0+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,commonSupportRadialAdjointFamily A hA S hS hz R p0 v⟫_ℝ := by
    simpa only [normalFrameRotationCurve_zero] using hAdj0Raw
  have hRCov := normalFrame_radial_rotation_covariance d y A hA S hS hz V hp0 hRep R hCoercive hStrong hRestrict i j θ hθ
  have hDCov (u : SphereSobolev 1) : (R pθ+sphereSobolevDegreeL) (P1 u) = P0 ((R p0+sphereSobolevDegreeL) u) := by
    have hRValue := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) hRCov
    have hDegree := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) (sphereSobolevDegreeL_orthogonal_covariance e)
    exact (congrArg₂ (fun x y : SphereSobolev 0 => x+y) hRValue hDegree).trans (P0.map_add _ _).symm
  exact boundary_adjoint_orthogonal_covariance e _ _ _ _ hAdj0 hAdjθ hDCov

end ShrinkingSpheres
