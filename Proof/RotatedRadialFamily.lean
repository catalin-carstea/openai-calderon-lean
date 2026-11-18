import Proof.CommonSupportMidpointRadialRegularity
import Proof.MidpointRadialOrthogonalCovariance
import Proof.OrthogonalEllipticity
import Proof.Archive.CoordinateRotationCoefficientFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.SmoothSphereRotation
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def rotatedCommonSupportMatrixFamily (i j : I) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (L : ℝ) (hz : ∀ p z,z ∉ Metric.closedBall (0:X) L → a (p,z) = 0) (t : ℝ × P) :
    SmoothCoefficientMatrix 2 :=
  commonSupportMatrixFamily 2 (coordinateRotationPrincipalFamily i j a)
    (contDiff_coordinateRotationPrincipalFamily i j a ha) (Metric.closedBall (0:X) L)
      (isCompact_closedBall _ _) (coordinateRotationPrincipalFamily_zero_outside i j a L hz) t

lemma coefficientMatrixField_rotatedCommonSupportMatrixFamily
    (i j : I) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a)
    (L : ℝ) (hz : ∀ p z,z ∉ Metric.closedBall (0:X) L → a (p,z) = 0) (t : ℝ × P) :
    coefficientMatrixField 2 (rotatedCommonSupportMatrixFamily i j a ha L hz t) =
      (fun z => coordinateRotationPrincipalFamily i j a (t,z)) :=
  coefficientMatrixField_commonSupportMatrixFamily 2 _ _ _ _ _ t

/-- A true smooth radial family on the whole angle line, with exact
    orthogonal covariance. Ellipticity supplies every inverse internally. -/
theorem exists_smooth_rotated_midpoint_radial_family
    (i j : I) (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (L : ℝ)
    (hz : ∀ p z,z ∉ Metric.closedBall (0:X) L → a (p,z) = 0)
    (U : Set P) (hU : IsOpen U) (lam Lam : ℝ)
    (hUE : ∀ p ∈ U,TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (fun z => a (p,z)) lam Lam) :
    ∃ R : (ℝ × P) → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ R (Set.univ ×ˢ U) ∧
      (∀ t ∈ Set.univ ×ˢ U,(R t).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
          (actualHighRadialErrorL (rotatedCommonSupportMatrixFamily i j a ha L hz t))) ∧
      ∀ θ : ℝ,∀ p ∈ U,(R (θ,p)).comp (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ)) =
        (sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ)).comp (R (0,p)) := by
  let ra := coordinateRotationPrincipalFamily i j a
  have hra : ContDiff ℝ ∞ ra := contDiff_coordinateRotationPrincipalFamily i j a ha
  let V : Set (ℝ × P) := Set.univ ×ˢ U
  let F := rotatedCommonSupportMatrixFamily i j a ha L hz
  have hV : IsOpen V := isOpen_univ.prod hU
  have hRotUE (t : ℝ × P) (ht : t ∈ V) :
      TauCeti.PDE.UniformlyEllipticOn (ballOpens:Set X) (fun z => ra (t,z)) lam Lam := by
    rcases t with ⟨θ,p⟩
    have h := uniformlyEllipticOn_unitBall_orthogonal (coordinateRotationIsometry i j θ)
      (fun z => a (p,z)) lam Lam (hUE p ht.2)
    simpa only [ra,coordinateRotationPrincipalFamily_eq_orthogonal] using h
  have hCoercive (t : ℝ × P) (ht : t ∈ V) :
      IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp ra hra t)) :=
    isCoercive_unitBall_zeroDrift (hRotUE t ht)
      (hra.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (commonSupportEnergyMemLp ra hra t)
  have hStrong (t : ℝ × P) (ht : t ∈ V) :
      (strongDirichletOperator fixedSobolevCalculus 0 (F t)).IsInvertible := by
    apply strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0
    rw [coefficientMatrixField_rotatedCommonSupportMatrixFamily]
    exact hRotUE t ht
  have hNormal (t : ℝ × P) (ht : t ∈ V) :
      (negativeBoundaryCoefficientMulL (normalCoefficientJet (F t))).IsInvertible := by
    apply negativeNormalCoefficient_isInvertible (F t) (normalCoefficientJet (F t))
      (coefficientSmoothData_normalCoefficientJet (F t)) lam Lam
    rw [coefficientMatrixField_rotatedCommonSupportMatrixFamily]
    exact hRotUE t ht
  have hFam := exists_commonSupport_smooth_midpoint_radial_family ra hra (Metric.closedBall (0:X) L)
    (isCompact_closedBall _ _) (coordinateRotationPrincipalFamily_zero_outside i j a L hz) V hV
      hCoercive hStrong hNormal
  obtain ⟨R,hSmooth,hRestrict⟩ := hFam
  refine ⟨R,hSmooth,hRestrict,?_⟩
  intro θ p hp
  have h0 : (0,p) ∈ V := ⟨mem_univ _,hp⟩
  have hθ : (θ,p) ∈ V := ⟨mem_univ _,hp⟩
  let e := coordinateRotationIsometry i j θ
  have hBaseC : IsCoercive (TauCeti.PDE.energyFormH1L0 (commonSupportEnergyMemLp a ha p)) :=
    isCoercive_unitBall_zeroDrift (hUE p hp)
      (ha.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        (commonSupportEnergyMemLp a ha p)
  have hRotMem : MemLp (fun z => TauCeti.PDE.energyIntegrand
      (orthogonalPrincipalCoefficient e (fun q => a (p,q)) z) (0:X) (0:ℝ)) ⊤
        ((volume:Measure X).restrict ballOpens) := by
    simpa only [ra,e,coordinateRotationPrincipalFamily_eq_orthogonal] using commonSupportEnergyMemLp ra hra (θ,p)
  have hRotC : IsCoercive (TauCeti.PDE.energyFormH1L0 hRotMem) := by
    simpa only [ra,e,coordinateRotationPrincipalFamily_eq_orthogonal] using hCoercive (θ,p) hθ
  have hF0 (z : X) (_hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F (0,p)) z = a (p,z) := by
    simp only [F,coefficientMatrixField_rotatedCommonSupportMatrixFamily,coordinateRotationPrincipalFamily_zero_angle]
  have hFθ (z : X) (_hz : z ∈ (ballOpens:Set X)) : coefficientMatrixField 2 (F (θ,p)) z =
      orthogonalPrincipalCoefficient e (fun q => a (p,q)) z := by
    simp only [F,coefficientMatrixField_rotatedCommonSupportMatrixFamily,coordinateRotationPrincipalFamily_eq_orthogonal,e]
  have hPoisson := strongPoissonL_orthogonal_covariance e (fun z => a (p,z))
    (ha.continuous.comp (continuous_const.prodMk continuous_id)) (commonSupportEnergyMemLp a ha p)
      hRotMem hBaseC hRotC (F (0,p)) (F (θ,p)) hF0 hFθ (hStrong (0,p) h0) (hStrong (θ,p) hθ)
  exact midpointRadial_orthogonal_covariance e (F (0,p)) (F (θ,p)) (R (0,p)) (R (θ,p))
    (hRestrict (0,p) h0) (hRestrict (θ,p) hθ)
      (actualHighRadialErrorL_orthogonal_covariance e (F (0,p)) (F (θ,p)) hPoisson)

end ShrinkingSpheres
