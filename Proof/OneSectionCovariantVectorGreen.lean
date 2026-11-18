import Proof.OneSectionCovariantDerivativeLinear
import Proof.OneSectionCovariantInner
import Proof.FischerIntegration

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma oneSectionCovariantDerivative_axis_expansion (d : Data) (U : X → SphereSobolev 1) (y a : X) :
    oneSectionCovariantDerivative d U y a=
      ∑ i : I,a i • oneSectionCovariantDerivative d U y (axis i) := by
  let L := oneSectionCovariantDerivativeLinear d U y
  have hh := congrArg L ((EuclideanSpace.basisFun I ℝ).sum_repr a)
  simpa only [map_sum,map_smul,EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,axis,
    L,oneSectionCovariantDerivativeLinear_apply] using hh.symm

def oneSectionCovariantVectorInnerDensity (d : Data) (q : X → ℝ) (U V : X → SphereSobolev 1)
    (A : X → X) (x : X) : ℝ :=
  q x*(⟪sphereSobolevInclusionL 1 0 (by norm_num) (U x),oneSectionCovariantDerivative d V x (A x)⟫_ℝ+
    ⟪oneSectionCovariantDerivative d U x (A x),sphereSobolevInclusionL 1 0 (by norm_num) (V x)⟫_ℝ)+
    weightedDivergence q A x*⟪sphereSobolevInclusionL 1 0 (by norm_num) (U x),
      sphereSobolevInclusionL 1 0 (by norm_num) (V x)⟫_ℝ

/-- Genuine covariant Green for a variable base vector field. Its full
weighted divergence is retained exactly, with no quantitative frame bound. -/
theorem oneSectionCovariantDerivative_vector_inner_data (d : Data) (q : X → ℝ)
    (U V : X → SphereSobolev 1) (A : X → X)
    (S : Set X) (hS : IsCompact S) (hq : ∀ x ∈ S,ContDiffAt ℝ ∞ q x)
    (hA : ∀ x ∈ S,ContDiffAt ℝ ∞ A x)
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) :
    Integrable (oneSectionCovariantVectorInnerDensity d q U V A) ∧
      (∫ x,oneSectionCovariantVectorInnerDensity d q U V A x)=0 := by
  let w := fun (i : I) x => q x*A x i
  have hw (i : I) (x : X) (hx : x ∈ S) : ContDiffAt ℝ ∞ (w i) x :=
    (hq x hx).mul ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp x (hA x hx))
  have hData (i : I) := oneSectionCovariantDerivative_weighted_inner_data d (w i) U V S hS
    (hw i) hU hV h0U h0V (axis i)
  let G := fun (i : I) => oneSectionCovariantInnerDensity d (w i) U V (axis i)
  have hPoint (x : X) : oneSectionCovariantVectorInnerDensity d q U V A x=∑ i : I,G i x := by
    rw [oneSectionCovariantVectorInnerDensity,
      oneSectionCovariantDerivative_axis_expansion d V x (A x),
      oneSectionCovariantDerivative_axis_expansion d U x (A x)]
    simp only [G,oneSectionCovariantInnerDensity,inner_sum,sum_inner,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,weightedDivergence,coordDeriv,w,Fin.sum_univ_three]
    ring
  have hInt : Integrable (fun x => ∑ i : I,G i x) :=
    integrable_finsetSum Finset.univ (fun i _ => (hData i).1)
  refine ⟨hInt.congr (Eventually.of_forall (fun x => (hPoint x).symm)),?_⟩
  calc
    _ = ∫ x,∑ i : I,G i x := integral_congr_ae (Eventually.of_forall hPoint)
    _ = ∑ i : I,∫ x,G i x := integral_finsetSum Finset.univ (fun i _ => (hData i).1)
    _ = 0 := by simp only [G,(hData _).2,Finset.sum_const_zero]

end ShrinkingSpheres
