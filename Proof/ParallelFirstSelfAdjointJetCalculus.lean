import Proof.HalfCovariantScalarProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- Finite scalar assembly of genuine HIGH covariant jets. This lemma
keeps the lower family smooth and uses higher choices only through their
graphs and point values. It is equally valid for forward or true-adjoint data. -/
lemma half_covariant_sum_smul_higher_graph
    (d : Data) (w : I → X → ℝ)
    (C : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (A : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (H : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y b : X) (hw : ∀ i,ContDiffAt ℝ ∞ (w i) y) (hC : ∀ i,ContDiffAt ℝ ∞ (C i) y)
    (hA : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A i y)=
      (C i y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hD : ∀ i,halfOperatorCovariantDerivativeL d (C i) (A i) y b=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H i)) :
    halfOperatorCovariantDerivativeL d (fun x => ∑ i : I,w i x • C i x)
      (fun x => ∑ i : I,w i x • A i x) y b=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (∑ i : I,(directionalFDeriv b (w i) y • A i y+w i y • H i)) := by
  have hOne (i : I) : halfOperatorCovariantDerivativeL d
      (fun x => w i x • C i x) (fun x => w i x • A i x) y b=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        (directionalFDeriv b (w i) y • A i y+w i y • H i) := by
    rw [halfOperatorCovariantDerivativeL_smul d (w i) (C i) (A i) y b (hw i) (hC i),hD i,←hA i]
    rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_smul]
  rw [halfOperatorCovariantDerivativeL_sum_three d
    (fun i x => w i x • C i x) (fun i x => w i x • A i x) y b (fun i => (hw i).smul (hC i))]
  apply ContinuousLinearMap.ext
  intro u
  simp only [hOne,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]

end ShrinkingSpheres.ParallelEnergy
