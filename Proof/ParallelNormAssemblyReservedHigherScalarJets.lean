import Proof.ParallelNormAssemblyReservedHigherApply
import Proof.HalfCovariantScalarProduct

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
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma weighted_half_covariant_higher_graph (d : Data)
    (f : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hf : ContDiffAt ℝ ∞ f y) (hC : ContDiffAt ℝ ∞ C y)
    (hB : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hN : halfOperatorCovariantDerivativeL d C H y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp N) :
    halfOperatorCovariantDerivativeL d (fun x => f x • C x) (fun x => f x • H x) y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (fderiv ℝ f y a • H y+f y • N) := by
  rw [halfOperatorCovariantDerivativeL_smul d f C H y a hf hC,←hB,hN]
  simp only [directionalFDeriv,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul]

/-- Genuine first HIGH graph for a scalar-normalized actual family.
All family germs are explicit; no endpoint regularity follows from a norm. -/
lemma weighted_higher_covariant_jet_graph (d : Data)
    (f : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hf : ContDiffAt ℝ ∞ f y) (hC : ContDiffAt ℝ ∞ C y) (hH : ContDiffAt ℝ ∞ H y)
    (hB : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H x)=
      (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (N : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hN : halfOperatorCovariantDerivativeL d C H y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp N) :
    higherOperatorCovariantDerivativeL d (fun x => f x • H x) y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        ((fderiv ℝ f y a • H y+f y • N).comp
          (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
  have hScaled : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (f x • H x)=
      (f x • C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hB] with x hx
    simp only [ContinuousLinearMap.comp_smul,ContinuousLinearMap.smul_comp,hx]
  rw [higher_covariant_derivative_eq_half d (fun x => f x • C x) (fun x => f x • H x) y a
    (hf.smul hC) (hf.smul hH) hScaled,
    weighted_half_covariant_higher_graph d f C H y a hf hC hB.self_of_nhds N hN,
    ContinuousLinearMap.comp_assoc]

end ShrinkingSpheres.ParallelEnergy
