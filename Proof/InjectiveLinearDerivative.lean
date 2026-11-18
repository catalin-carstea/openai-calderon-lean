import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Comp
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ShrinkingSpheres
lemma hasDerivAt_of_injective_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Injective L) (f : ℝ → E) (df : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f t) (hLf : HasDerivAt (fun s => L (f s)) (L df) t) : HasDerivAt f df t := by
  have hh := L.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
  have hEq := hL (hh.unique hLf)
  exact hEq ▸ hf.hasDerivAt
end ShrinkingSpheres
