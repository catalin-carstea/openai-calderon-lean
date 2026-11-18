import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Congr
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Filter
open scoped Topology
namespace ShrinkingSpheres
variable {P V0 V1 W0 W1 : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V0] [NormedSpace ℝ V0] [NormedAddCommGroup V1] [NormedSpace ℝ V1]
  [NormedAddCommGroup W0] [NormedSpace ℝ W0] [NormedAddCommGroup W1] [NormedSpace ℝ W1]

/-- A genuine fixed inclusion square remains compatible after taking an
    actual parameter derivative. No Sobolev order is identified by casting. -/
lemma compatible_endpoint_fderiv (F : P → V0 →L[ℝ] W0) (G : P → V1 →L[ℝ] W1)
    (Iout : W0 →L[ℝ] W1) (Iin : V0 →L[ℝ] V1) (p a : P)
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p)
    (hCompat : ∀ᶠ q in 𝓝 p,Iout.comp (F q)=(G q).comp Iin) :
    Iout.comp (fderiv ℝ F p a)=(fderiv ℝ G p a).comp Iin := by
  have hLeft := (hasFDerivAt_const Iout p).clm_comp hF.hasFDerivAt
  have hRight := hG.hasFDerivAt.clm_comp (hasFDerivAt_const Iin p)
  have hGerm : (fun q => Iout.comp (F q)) =ᶠ[𝓝 p] (fun q => (G q).comp Iin) := hCompat
  have hEq : fderiv ℝ (fun q => Iout.comp (F q)) p=
      fderiv ℝ (fun q => (G q).comp Iin) p := hGerm.fderiv_eq
  have h := DFunLike.congr_fun (hLeft.fderiv.symm.trans (hEq.trans hRight.fderiv)) a
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,_root_.zero_apply,ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero,zero_add,add_zero] using h
end ShrinkingSpheres
