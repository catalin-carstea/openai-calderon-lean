import Proof.NativeFullAdjointNormalization
import Proof.CoarseRotationGraphUnique
import Proof.NativeFullRadialAngularFields
import Proof.RelativeAngularDerivativeCurve
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation
namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C}

lemma fullAdjoint_normalized_angular_graph (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I) (f : SphereSobolev 2) :
    sphereSobolevRotationL 0 i j (t.fullAdjoint p (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (normalFrameRelativeAngularDerivative d.γ t.fullAdjoint i j p
          (sphereSobolevInclusionL 2 1 (by norm_num) f)+t.fullAdjoint p (sphereSobolevRotationL 2 i j f)) := by
  let c := normalFrameRelativeAngularCurve d.γ p i j
  have hpN := V.normalizationStable p hp
  have hSmooth : DifferentiableAt ℝ t.fullAdjoint (normalFrameRelativeNormalization d.γ p) :=
    (t.adjointSmooth.contDiffAt (t.domainOpen.mem_nhds (V.sub hpN))).differentiableAt (by simp)
  have hD := hasDerivAt_relativeAngularFamily d.γ t.fullAdjoint p i j hSmooth
  have hCurve0 : c 0=normalFrameRelativeNormalization d.γ p := normalFrameRelativeAngularCurve_zero _ _ _ _
  have hZero : t.fullAdjoint (c 0)=t.fullAdjoint p :=
    (congrArg t.fullAdjoint hCurve0).trans (t.fullAdjoint_normalization V h hK hZ p hp)
  have hStay : ∀ᶠ θ in 𝓝 (0:ℝ),c θ ∈ V.domain :=
    (hasDerivAt_normalFrameRelativeAngularCurve d.γ p i j).continuousAt.eventually
      (V.domainOpen.mem_nhds (by rw [normalFrameRelativeAngularCurve_zero];exact hpN))
  have hCov : ∀ᶠ θ in 𝓝 (0:ℝ),∀ u,
      t.fullAdjoint (c θ) (sphereSobolevOrthogonalPullbackL 1 (coordinateRotationIsometry i j θ) u) =
        sphereSobolevOrthogonalPullbackL 0 (coordinateRotationIsometry i j θ) (t.fullAdjoint p u) := by
    filter_upwards [hStay] with θ hθ
    intro u
    exact congrArg (fun A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => A u)
      (native_relative_radial_adjoint_rotation_covariance t V h hK hZ p hp i j θ hθ)
  have hh := sphereSobolev_operator_rotation_derivative_distribution_of_germ orthogonalSphereHarmonics denseSphereHarmonics
    2 0 i j (fun θ => t.fullAdjoint (c θ)) (t.fullAdjoint p)
    (normalFrameRelativeAngularDerivative d.γ t.fullAdjoint i j p) hD hZero hCov f
  have hI : sphereSobolevInclusionL 2 ((2:ℝ)-1) (by norm_num)=sphereSobolevInclusionL 2 1 (by norm_num) := by
    congr 1 <;> norm_num
  have hJ : sphereSobolevInclusionL 0 ((0:ℝ)-1) (by norm_num)=sphereSobolevInclusionL 0 (-1) (by norm_num) := by
    congr 1 <;> norm_num
  rw [hI,hJ] at hh
  exact hh

lemma fullAdjointAngularFields_angular_eq (t : NormalFrameRelativeResponsePacket q) (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (i j : I) :
    (t.fullAdjointAngularFields p).angular (i,j) =
      normalFrameRelativeAngularDerivative d.γ t.fullAdjoint i j p := by
  apply coarse_rotation_generator_unique (t.fullAdjoint p) _ _ i j
  · intro f
    have hh := (t.fullAdjointAngularPacket V h hK hZ p hp).graph (i,j) f
    rw [t.fullAdjointAngularPacket_operator V h hK hZ p hp] at hh
    exact hh
  · exact t.fullAdjoint_normalized_angular_graph V h hK hZ p hp i j
end NormalFrameRelativeResponsePacket
end ShrinkingSpheres
