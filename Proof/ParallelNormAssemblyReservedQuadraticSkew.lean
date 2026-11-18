import Proof.ParallelNormAssemblyReservedAdjointQuadraticJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma quadratic_covariant_derivative_sub (d : Data)
    (C A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hA : ContDiffAt ℝ ∞ A y) :
    quadraticOperatorCovariantDerivativeL d (fun x => C x-A x) y a=
      quadraticOperatorCovariantDerivativeL d C y a-quadraticOperatorCovariantDerivativeL d A y a := by
  have hD := fderiv_fun_sub (hC.differentiableAt (by simp)) (hA.differentiableAt (by simp))
  have hDa : fderiv ℝ (fun x => C x-A x) y a=fderiv ℝ C y a-fderiv ℝ A y a := by
    simpa only [_root_.sub_apply] using
      congrArg (fun T : X →L[ℝ] (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) => T a) hD
  apply ContinuousLinearMap.ext
  intro u
  simp only [quadraticOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,_root_.add_apply,
    _root_.sub_apply,map_sub,hDa]
  abel

lemma quadratic_covariant_sub_graph (d : Data)
    (C A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hA : ContDiffAt ℝ ∞ A y)
    (N M : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hN : quadraticOperatorCovariantDerivativeL d C y a=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        (N.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (hM : quadraticOperatorCovariantDerivativeL d A y a=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        (M.comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)))) :
    quadraticOperatorCovariantDerivativeL d (fun x => C x-A x) y a=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((N-M).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
  rw [quadratic_covariant_derivative_sub d C A y a hC hA,hN,hM,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub]

lemma actual_potential_forward_word_weak_eq {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) (u : SphereSobolev (3/2:ℝ)) :
    quadraticWordForwardWeakValue P y (PhysicalPrincipalData.potentialWordCoefficient d y) u=
      P.potentialQuadraticHalfL y u := by
  rw [P.potentialQuadraticHalfL_eq_word_matrix]
  simp only [quadraticWordForwardWeakValue,PhysicalPrincipalData.potentialWordMatrixL,
    _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]

/-- The forward-minus-true-adjoint weak potential is genuinely skew on
H3/2 through the actual half inclusion, for ANY fixed coherent W. -/
lemma actual_potential_adjoint_difference_skew {Y : Set X} {d : Data} {CF CT ε CN CJ CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (A : PotentialAdjointFirstJetPacket P ε CN CJ)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (u v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      ((P.potentialQuadraticHalfL y-A.weak y) v)=
    -sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
      ((P.potentialQuadraticHalfL y-A.weak y) u) := by
  have hAdj (u v : SphereSobolev (3/2:ℝ)) := quadratic_word_weak_adjunction P hy W
    (PhysicalPrincipalData.potentialWordCoefficient d y) u v
  have hUV := hAdj u v
  have hVU := hAdj v u
  rw [A.actual_graph CG CK y hy W v,actual_potential_forward_word_weak_eq] at hUV
  rw [A.actual_graph CG CK y hy W u,actual_potential_forward_word_weak_eq] at hVU
  simp only [sphereSobolevDualPairing,_root_.sub_apply,inner_sub_right] at hUV hVU ⊢
  linarith only [hUV,hVU]

end ShrinkingSpheres.ParallelEnergy
