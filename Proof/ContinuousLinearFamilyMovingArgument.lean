import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace ShrinkingSpheres

/-- A continuous operator family only needs a derivative at the fixed
argument to differentiate its action on a moving argument. This separates
the fixed-multiplier derivative from the genuine derivative of the multiplier. -/
theorem hasDerivAt_clm_apply_of_continuous_family
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ → E →L[ℝ] F) (q : ℝ → E) (x : ℝ) (v : F) (w : E)
    (hL : ContinuousAt L x) (hv : HasDerivAt (fun t => L t (q x)) v x)
    (hq : HasDerivAt q w x) :
    HasDerivAt (fun t => L t (q t)) (v+L x w) x := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hSlope (t : ℝ) : slope (fun s => L s (q s)) x t =
      slope (fun s => L s (q x)) x t+L t (slope q x t) := by
    simp only [slope_def_module,map_smul,map_sub]
    module
  have hFun : slope (fun s => L s (q s)) x =
      fun t => slope (fun s => L s (q x)) x t+L t (slope q x t) := funext hSlope
  rw [hFun]
  have hEval : Continuous (fun p : (E →L[ℝ] F) × E => p.1 p.2) := by fun_prop
  have hLt : Tendsto L (𝓝[≠] x) (𝓝 (L x)) := hL.tendsto.mono_left nhdsWithin_le_nhds
  exact hv.tendsto_slope.add (hEval.continuousAt.tendsto.comp (hLt.prodMk_nhds hq.tendsto_slope))

end ShrinkingSpheres
