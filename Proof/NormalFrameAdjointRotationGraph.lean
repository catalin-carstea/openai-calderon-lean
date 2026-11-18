import Proof.NormalFrameAdjointRotationCovariance
import Proof.NormalFrameAdjointRotationModel
import Proof.LocalRadialTaylorRotationDistribution

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

/-- The actual adjoint Taylor derivative is exactly its angular commutator
as an H2-to-distributions graph, using native physical adjunction. -/
theorem uniform_normalFrame_adjoint_taylor_rotation_distribution {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ A : NormalFrameParameter × X → Mat,∀ hA : ContDiff ℝ ∞ A,
      ∀ S : Set X,∀ hS : IsCompact S,∀ hz : ∀ p z,z ∉ S → A (p,z) = 0,
      ∀ V : Set NormalFrameParameter,IsOpen V → (y,(d.radius y,frameVectorLinear d.frame y)) ∈ V →
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
      ContDiffOn ℝ ∞ (commonSupportRadialAdjointFamily A hA S hS hz R) V →
      ∀ i j : I,∀ f : SphereSobolev 2,
        let H := normalFrameRadialAdjointTaylorFamily d (commonSupportRadialAdjointFamily A hA S hS hz R)
        let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
        let C := deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0
        sphereSobolevRotationL 0 i j (H p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
          sphereSobolevInclusionL 0 (-1) (by norm_num)
            (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+H p0 (sphereSobolevRotationL 2 i j f)) := by
  obtain ⟨η,hη,hCovariant⟩ := uniform_normalFrame_radial_adjoint_rotation_covariance (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy A hA S hS hz V hV hp0 hRep R hCoercive hStrong hNormal hRestrict hDaS i j f
  let Da := commonSupportRadialAdjointFamily A hA S hS hz R
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let c := normalFrameRotationCurve d.frame d.radius y i j
  let Q := fun t => Da (c t)-sphereSobolevDegreeL
  let H := normalFrameRadialAdjointTaylorFamily d Da
  let q := firstDensityLogCovector d y
  let r := d.radius y
  let B0 := (radialCorrectionCovectorL q).adjoint
  let B1 := radialCorrectionAdjointSobolevL 1 q
  let D := (radialCorrectionCovectorL (rotationCovector q i j)).adjoint
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hyΩ := hd.2.1.center_mem hy
  have hCurve := hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j
  have hZero : c 0 = p0 := normalFrameRotationCurve_zero d.frame d.radius y i j
  have hDaDiff : DifferentiableAt ℝ Da (c 0) := by
    rw [hZero]
    exact (hDaS.contDiffAt (hV.mem_nhds hp0)).differentiableAt (by simp)
  have hQDiff : DifferentiableAt ℝ Q 0 := (hDaDiff.comp 0 hCurve.differentiableAt).sub (differentiableAt_const _)
  have h0V : c 0 ∈ V := by rw [hZero];exact hp0
  have hEvent : ∀ᶠ t in 𝓝 (0:ℝ),c t ∈ V := hCurve.continuousAt.eventually (hV.mem_nhds h0V)
  have hCov : ∀ᶠ t in 𝓝 (0:ℝ),∀ u,Q t (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j t) u) =
      sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j t) (Q 0 u) := by
    filter_upwards [hEvent] with t ht
    intro u
    let P0 := sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j t)
    let P1 := sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j t)
    have hOp := hCovariant floor hf ε hε hSmall d hd y hy A hA S hS hz V hp0 hRep R hCoercive hStrong hNormal hRestrict i j t ht
    have hValue : Da (c t) (P1 u) = P0 (Da p0 u) :=
      congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u) hOp
    have hDegree : sphereSobolevDegreeL (P1 u) = P0 (sphereSobolevDegreeL u) :=
      congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T u)
        (sphereSobolevDegreeL_orthogonal_covariance (coordinateRotationIsometry i j t))
    have hSub : Da (c t) (P1 u)-sphereSobolevDegreeL (P1 u) = P0 (Da p0 u-sphereSobolevDegreeL u) :=
      (congrArg₂ (fun x y : SphereSobolev 0 => x-y) hValue hDegree).trans (P0.map_sub _ _).symm
    change Da (c t) (P1 u)-sphereSobolevDegreeL (P1 u) = P0 (Da (c 0) u-sphereSobolevDegreeL u)
    rw [hZero]
    exact hSub
  have hCompat (v : SphereSobolev 1) : sphereSobolevInclusionL 1 0 (by norm_num) (B1 v) =
      B0 (sphereSobolevInclusionL 1 0 (by norm_num) v) := radialCorrectionAdjointSobolevL_coarse q v
  have hComm : (sphereSobolevRotationL 1 i j).comp B1-B0.comp (sphereSobolevRotationL 1 i j) =
      D.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := rotation_radialCorrectionAdjoint_commutator i j q
  have hFirst0 := hasDerivAt_firstRadial_rotation_zero 1 q i j
  simp only [inv_one,one_smul] at hFirst0
  let J : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hFirst := J.hasFDerivAt.comp_hasDerivAt (0:ℝ) hFirst0
  change HasDerivAt (fun t => (coarseFirstRadialVariationL 1
    (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).adjoint) D 0 at hFirst
  let Pre : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.compL ℝ (SphereSobolev 1) (SphereSobolev 0) (SphereSobolev 0)).flip
      (sphereSobolevInclusionL 1 0 (by norm_num))
  have hPre := Pre.hasFDerivAt.comp_hasDerivAt (0:ℝ) hFirst
  have hFirstModel : (fun t => H (c t)) = fun t => Q t-r •
      (coarseFirstRadialVariationL 1 (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).adjoint.comp
        (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    funext t
    exact hd.1.normalFrameRadialAdjointTaylorFamily_rotation hΩ hKpos hyΩ Da i j t
  have hD := hQDiff.hasDerivAt.sub (hPre.const_smul r)
  change HasDerivAt (fun t => Q t-r •
    (coarseFirstRadialVariationL 1 (q.comp (coordinateRotationIsometry i j t).toContinuousLinearEquiv.toContinuousLinearMap)).adjoint.comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))
        (deriv Q 0-r • D.comp (sphereSobolevInclusionL 1 0 (by norm_num))) 0 at hD
  rw [← hFirstModel] at hD
  have hC := hD.deriv
  have hPoint : H p0 = Q 0-r • B0.comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
    dsimp only [Q]
    rw [hZero]
    dsimp only [H,normalFrameRadialAdjointTaylorFamily,p0,r,B0,q]
    rw [hd.1.normalFrameFirstCovector_actual hΩ hKpos hyΩ]
  have hGraph := radial_taylor_rotation_commutator_distribution_of_germ i j r Q (deriv Q 0) (deriv (fun t => H (c t)) 0)
    B0 D B1 hQDiff.hasDerivAt hCov hCompat hComm hC f
  simpa only [← hPoint] using hGraph

end ShrinkingSpheres
