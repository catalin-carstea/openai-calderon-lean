import Proof.PoissonTaylorDerivative
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F U Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Exact rectangular inverse remainder: every term contains either the
    quadratic coefficient residual or two first-order coefficient factors. -/
theorem inverse_affine_remainder_factorization
    (A A0 A1 : E →L[ℝ] F) (hA : A.IsInvertible) (hA0 : A0.IsInvertible) (r : ℝ) :
    A.inverse-A0.inverse+r • A0.inverse.comp (A1.comp A0.inverse) =
      -(A.inverse.comp ((A-A0-r • A1).comp A0.inverse))+
        r • A.inverse.comp ((A-A0).comp (A0.inverse.comp (A1.comp A0.inverse))) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.add_apply,
    _root_.smul_apply,_root_.neg_apply,map_sub,map_smul,
    hA.inverse_apply_self,hA0.self_apply_inverse]
  module

/-- Exact zero-boundary Poisson correction remainder. The same actual inverse
    multiplies its gained forcing; no independent solution is introduced. -/
theorem poisson_affine_remainder_factorization
    (A A0 : E →L[ℝ] F) (T T0 T1 : U →L[ℝ] F) (H : Z →L[ℝ] U)
    (hA : A.IsInvertible) (hA0 : A0.IsInvertible) (hFlat : T0.comp H = 0) (r : ℝ) :
    A.inverse.comp (T.comp H)-r • A0.inverse.comp (T1.comp H) =
      A.inverse.comp (((T-T0-r • T1).comp H)-
        r • (A-A0).comp (A0.inverse.comp (T1.comp H))) := by
  apply ContinuousLinearMap.ext
  intro x
  have hZero : T0 (H x) = 0 := congrArg (fun L : Z →L[ℝ] F => L x) hFlat
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,_root_.smul_apply,
    map_sub,map_smul,hA.inverse_apply_self,hA0.self_apply_inverse,hZero,sub_zero]
  module

variable [CompleteSpace E]

theorem eventually_isInvertible_of_continuousAt (A : P → E →L[ℝ] F) (x : P)
    (hA : ContinuousAt A x) (hAx : (A x).IsInvertible) :
    ∀ᶠ p in 𝓝 x,(A p).IsInvertible :=
  hA.preimage_mem_nhds (ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hAx)

theorem inverse_affine_remainder_factorization_germ
    (A A1 : P → E →L[ℝ] F) (A0 : E →L[ℝ] F) (x : P)
    (hA : ContinuousAt A x) (hAx : (A x).IsInvertible) (hA0 : A0.IsInvertible) (r : ℝ) :
    (fun p => (A p).inverse-A0.inverse+r • A0.inverse.comp ((A1 p).comp A0.inverse)) =ᶠ[𝓝 x]
      (fun p => -((A p).inverse.comp ((A p-A0-r • A1 p).comp A0.inverse))+
        r • (A p).inverse.comp ((A p-A0).comp (A0.inverse.comp ((A1 p).comp A0.inverse)))) := by
  filter_upwards [eventually_isInvertible_of_continuousAt A x hA hAx] with p hp
  exact inverse_affine_remainder_factorization (A p) A0 (A1 p) hp hA0 r

theorem poisson_affine_remainder_factorization_germ
    (A : P → E →L[ℝ] F) (A0 : E →L[ℝ] F) (T T1 : P → U →L[ℝ] F)
    (T0 : U →L[ℝ] F) (H : Z →L[ℝ] U) (x : P)
    (hA : ContinuousAt A x) (hAx : (A x).IsInvertible) (hA0 : A0.IsInvertible)
    (hFlat : T0.comp H = 0) (r : ℝ) :
    (fun p => (A p).inverse.comp ((T p).comp H)-r • A0.inverse.comp ((T1 p).comp H)) =ᶠ[𝓝 x]
      (fun p => (A p).inverse.comp (((T p-T0-r • T1 p).comp H)-
        r • (A p-A0).comp (A0.inverse.comp ((T1 p).comp H)))) := by
  filter_upwards [eventually_isInvertible_of_continuousAt A x hA hAx] with p hp
  exact poisson_affine_remainder_factorization (A p) A0 (T p) T0 (T1 p) H hp hA0 hFlat r

end ShrinkingSpheres
