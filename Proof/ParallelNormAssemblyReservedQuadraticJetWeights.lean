import Proof.ParallelNormAssemblyReservedQuadraticJetAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma quadratic_covariant_smul (d : Data) (f : X → ℝ)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y a : X)
    (hf : DifferentiableAt ℝ f y) (hC : DifferentiableAt ℝ C y) :
    quadraticOperatorCovariantDerivativeL d (fun x => f x • C x) y a=
      (fderiv ℝ f y a) • ((sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((C y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))+
      f y • quadraticOperatorCovariantDerivativeL d C y a := by
  have hProduct : HasFDerivAt (fun x => f x • C x)
      (f y • fderiv ℝ C y+(fderiv ℝ f y).smulRight (C y)) y :=
    hf.hasFDerivAt.smul hC.hasFDerivAt
  have hd := hProduct.fderiv
  have hAt : fderiv ℝ (fun x => f x • C x) y a=
      f y • fderiv ℝ C y a+fderiv ℝ f y a • C y := by
    simpa only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.smulRight_apply] using
      congrArg (fun A : X →L[ℝ] SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A a) hd
  apply ContinuousLinearMap.ext
  intro u
  simp only [quadraticOperatorCovariantDerivativeL,ContinuousLinearMap.comp_apply,hAt,
    _root_.add_apply,_root_.sub_apply,_root_.smul_apply,map_add,map_smul]
  module

lemma quadratic_covariant_sum {ι : Type*} [Fintype ι] (d : Data)
    (C : ι → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y a : X)
    (hC : ∀ c,DifferentiableAt ℝ (C c) y) :
    quadraticOperatorCovariantDerivativeL d (fun x => ∑ c,C c x) y a=
      ∑ c,quadraticOperatorCovariantDerivativeL d (C c) y a := by
  have hd := (HasFDerivAt.fun_sum (fun c (_ : c ∈ (Finset.univ : Finset ι)) => (hC c).hasFDerivAt)).fderiv
  apply ContinuousLinearMap.ext
  intro u
  simp only [quadraticOperatorCovariantDerivativeL,hd,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.add_apply,_root_.sub_apply,map_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

lemma quadratic_covariant_congr_germ {d : Data} {y a : X}
    {C F : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    (hCF : C=ᶠ[𝓝 y] F) :
    quadraticOperatorCovariantDerivativeL d C y a=quadraticOperatorCovariantDerivativeL d F y a := by
  simp only [quadraticOperatorCovariantDerivativeL,hCF.eq_of_nhds,hCF.fderiv_eq]

/-- Norm algebra for the complete first covariant jet of one weighted
quadratic word. It keeps the scalar and two genuine operator jet terms. -/
lemma weighted_quadratic_first_jet_norm
    (L DL : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H DH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (p dp CP CG CL CH ε β : ℝ) (hCP : 0 ≤ CP) (hCG : 0 ≤ CG)
    (hCL : 0 ≤ CL) (hCH : 0 ≤ CH) (hε : 0 ≤ ε) (hβ : 0 ≤ β)
    (hp : |p| ≤ CP*ε) (hdp : |dp| ≤ CP*ε*β)
    (hL : ‖L‖ ≤ CG) (hH : ‖H‖ ≤ CG) (hDL : ‖DL‖ ≤ CL*β) (hDH : ‖DH‖ ≤ CH*β) :
    ‖dp • L.comp H+p • (DL.comp H+L.comp DH)‖ ≤
      CP*(CG^2+CG*(CL+CH))*ε*β := by
  have h1 : ‖dp • L.comp H‖ ≤ (CP*ε*β)*(CG*CG) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hdp ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hL hH (norm_nonneg _) hCG)) (norm_nonneg _) (by positivity)
  have h2 : ‖p • DL.comp H‖ ≤ (CP*ε)*((CL*β)*CG) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hp ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hDL hH (norm_nonneg _) (by positivity))) (norm_nonneg _) (by positivity)
  have h3 : ‖p • L.comp DH‖ ≤ (CP*ε)*(CG*(CH*β)) := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hp ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hL hDH (norm_nonneg _) hCG)) (norm_nonneg _) (by positivity)
  rw [smul_add]
  exact ((norm_add_le _ _).trans (add_le_add h1 ((norm_add_le _ _).trans (add_le_add h2 h3)))).trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
