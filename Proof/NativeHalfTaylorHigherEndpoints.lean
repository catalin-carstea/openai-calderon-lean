import Proof.NativeHalfTaylorCompatibility
import Proof.HalfPhysicalAdjoint
import Proof.HigherHalfPhysicalCompatibility
import Proof.HalfDegreeHigherLiftJets
import Proof.SmoothFiniteAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.NormalFrameRelativeResponsePacket
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z C}
  {t : NormalFrameRelativeResponsePacket q}

def SymmetricAdjointDomain.forwardHigherTaylor (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  halfDegreeHigherLift (q.halfTaylor p) (V.degreeFamily h hK hZ p)

def SymmetricAdjointDomain.adjointHigherTaylor (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  halfDegreeHigherLift (q.halfTaylor p).adjoint (-(V.degreeFamily h hK hZ p).adjoint)

lemma SymmetricAdjointDomain.forwardHigherTaylor_physical_block (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (1/2:ℝ) m
      (V.forwardHigherTaylor h hK hZ p (sphereSobolevSingleL (3/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (t.forwardTaylor p) m n z := by
  have hL := V.halfTaylor_physical_block hZ F0 hF0 p hp
  have hS (a b : ℕ) (w : harmonicSphereSubspace b) :
      sphereSobolevCoefficientL (-(1/2:ℝ)) a (V.degreeFamily h hK hZ p (sphereSobolevSingleL (1/2:ℝ) b w)) =
        ((a:ℝ)-(b:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) a (q.halfTaylor p (sphereSobolevSingleL (1/2:ℝ) b w)) := by
    rw [hL]
    exact V.degreeFamily_physical_block h hK hZ p hp a b w
  exact (halfDegreeHigherLift_single_coefficient _ _ hS m n z).trans (hL m n z)

lemma SymmetricAdjointDomain.adjointHigherTaylor_physical_block (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) (m n : ℕ) (z : harmonicSphereSubspace n) :
    sphereSobolevCoefficientL (1/2:ℝ) m
      (V.adjointHigherTaylor h hK hZ p (sphereSobolevSingleL (3/2:ℝ) n z)) =
      coarsePhysicalHarmonicBlock (t.adjointTaylor p) m n z := by
  have hL := V.halfTaylor_physical_block hZ F0 hF0 p hp
  have hLa := half_operator_adjoint_physical_block (t.forwardTaylor p) (t.adjointTaylor p)
    (V.taylorPair p hp) (q.halfTaylor p) hL
  have hS (a b : ℕ) (w : harmonicSphereSubspace b) :
      sphereSobolevCoefficientL (-(1/2:ℝ)) a
        ((-(V.degreeFamily h hK hZ p).adjoint) (sphereSobolevSingleL (1/2:ℝ) b w)) =
        ((a:ℝ)-(b:ℝ)) • sphereSobolevCoefficientL (-(1/2:ℝ)) a
          ((q.halfTaylor p).adjoint (sphereSobolevSingleL (1/2:ℝ) b w)) := by
    rw [hLa]
    exact half_degree_commutator_adjoint_block _ _ (V.taylorPair p hp) (V.degreeFamily h hK hZ p)
      (V.degreeFamily_physical_block h hK hZ p hp) a b w
  exact (halfDegreeHigherLift_single_coefficient _ _ hS m n z).trans (hLa m n z)

lemma SymmetricAdjointDomain.forwardHigherTaylor_coarse_compatible (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (V.forwardHigherTaylor h hK hZ p) =
      (t.forwardTaylor p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) :=
  higher_half_coarse_compatible_of_blocks _ _ (V.forwardHigherTaylor_physical_block h hK hZ F0 hF0 p hp)
lemma SymmetricAdjointDomain.adjointHigherTaylor_coarse_compatible (V : t.SymmetricAdjointDomain)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (hZ : 2 ≤ Z)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (V.adjointHigherTaylor h hK hZ p) =
      (t.adjointTaylor p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) :=
  higher_half_coarse_compatible_of_blocks _ _ (V.adjointHigherTaylor_physical_block h hK hZ F0 hF0 p hp)
end ShrinkingSpheres.NormalFrameRelativeResponsePacket
