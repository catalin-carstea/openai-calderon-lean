import Proof.ParallelNormAssemblyReservedQuadraticWeakPair
import Proof.ParallelNormAssemblyReservedFiveHalfSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Exact point expansion of a quadratic weak Green datum with a genuine
H3/2 derivative source. Its HIGH lift is explicit, and all connection and
coefficient-jet terms are retained before symmetric contraction. -/
lemma quadratic_weak_derivative_source_point (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → SphereSobolev (3/2:ℝ)) (U : X → SphereSobolev (5/2:ℝ)) (y a : X)
    (hH : DifferentiableAt ℝ H y)
    (DQ : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hDQ : quadraticOperatorCovariantDerivativeL d C y a=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        (DQ.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))) :
    quadraticWeakLeftPairDensity d q C
      (fun x => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H x)) H U a y=
      q y*(sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d H y a)
          (C y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))+
        sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H y))
          (C y (fiveHalfSectionCovariantDerivativeL d U y a))+
        sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H y))
          (DQ (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))))+
      fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H y))
        (C y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hD := (J.hasFDerivAt.comp y hH.hasFDerivAt).fderiv
  have hDa := congrArg (fun L : X →L[ℝ] SphereSobolev (1/2:ℝ) => L a) hD
  simp only [ContinuousLinearMap.comp_apply] at hDa
  change fderiv ℝ (fun x => J (H x)) y a=J (fderiv ℝ H y a) at hDa
  dsimp only [J] at hDa
  have hQ := DFunLike.congr_fun hDQ (U y)
  simp only [ContinuousLinearMap.comp_apply] at hQ
  have hPair := quadratic_dual_inclusion_pair (H y)
    (DQ (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))
  simp only [quadraticWeakLeftPairDensity,halfSectionCovariantDerivativeL_apply]
  rw [hDa,hQ,hPair]

/-- Symmetric scalar contraction cancels the complete gradient-gradient
pair for ANY genuine quadratic angular adjoint, including non-selfadjoint
potentials. This is done before taking any norm. -/
lemma symmetric_quadratic_gradient_pair_cancel
    (q : I → I → ℝ) (hq : ∀ a b,q a b=q b a)
    (C A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hAdj : ∀ u v : SphereSobolev (3/2:ℝ),sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (A v)=
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (C u))
    (H : I → SphereSobolev (3/2:ℝ)) :
    (∑ a : I,∑ b : I,q a b*sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b)) (A (H a)))=
    ∑ a : I,∑ b : I,q a b*sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b)) (C (H a)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hq b a,hAdj]

end ShrinkingSpheres.ParallelEnergy
