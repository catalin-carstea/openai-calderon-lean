import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Normed.Operator.Basic
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
/-- Inverses preserve an already established endpoint square. -/
lemma inverse_endpoint_compatible {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : E →L[ℝ] F) (M : E →L[ℝ] E) (C : F →L[ℝ] F)
    (hM : M.IsInvertible) (hC : C.IsInvertible) (h : I.comp M=C.comp I) :
    I.comp M.inverse=C.inverse.comp I := by
  apply ContinuousLinearMap.ext
  intro u
  have hImage : C (I (M.inverse u))=I u :=
    (DFunLike.congr_fun h (M.inverse u)).symm.trans (congrArg I (hM.self_apply_inverse u))
  exact (hC.inverse_apply_self (I (M.inverse u))).symm.trans (congrArg C.inverse hImage)
end ShrinkingSpheres
