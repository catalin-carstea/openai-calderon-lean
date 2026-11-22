module

public import Proof.CalderonN.Coordinates

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! Adapted from `Proof/AngleSpatialDerivative.lean` in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ}

/-- The angle derivative of the true first spatial coefficient derivative is
    the spatial derivative of its angle generator. This uses actual C2 joint
    regularity and Schwarz symmetry, rather than an independent derivative witness. -/
theorem hasDerivAt_spatial_fderiv_of_angle_generator
    (a : ℝ × (X dim) → ℝ) (ha : ContDiff ℝ ∞ a) (b : (X dim) → ℝ)
    (hb : ∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0) (x : (X dim)) :
    HasDerivAt (fun θ => fderiv ℝ (fun z => a (θ,z)) x) (fderiv ℝ b x) 0 := by
  let V : ℝ × (X dim) := (1,0)
  let J : (X dim) →L[ℝ] ℝ × (X dim) := ContinuousLinearMap.inr ℝ ℝ (X dim)
  have hDa : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hSlice (θ : ℝ) : fderiv ℝ (fun z => a (θ,z)) x = (fderiv ℝ a (θ,x)).comp J := by
    exact ((ha.differentiable (by simp) (θ,x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right θ x)).fderiv
  have hCurve : HasDerivAt (fun θ : ℝ => fderiv ℝ a (θ,x))
      (fderiv ℝ (fderiv ℝ a) ((0:ℝ),x) V) 0 := by
    exact (hDa.differentiable (by simp) ((0:ℝ),x)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) x))
  have hCompose := hCurve.clm_comp (hasDerivAt_const (0:ℝ) J)
  have hB : b = fun z => fderiv ℝ a ((0:ℝ),z) V := by
    funext z
    have h : HasDerivAt (fun t : ℝ => a (t,z)) (fderiv ℝ a ((0:ℝ),z) V) 0 :=
      (ha.differentiable (by simp) ((0:ℝ),z)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z))
    exact (hb z).unique h
  have hBder : fderiv ℝ b x =
      ((fderiv ℝ (fderiv ℝ a) ((0:ℝ),x)).comp J).flip V := by
    rw [hB]
    simpa only [Function.comp_def,ContinuousLinearMap.comp_zero,zero_add,J] using
      (((hDa.differentiable (by simp) ((0:ℝ),x)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_right (0:ℝ) x)).clm_apply (hasFDerivAt_const V x)).fderiv
  have hSym : (fderiv ℝ (fderiv ℝ a) ((0:ℝ),x) V).comp J = fderiv ℝ b x := by
    rw [hBder]
    ext v
    exact (ha.contDiffAt.isSymmSndFDerivAt (by simp)) V (J v)
  have hSame : (fun θ => fderiv ℝ (fun z => a (θ,z)) x) =
      fun θ => (fderiv ℝ a (θ,x)).comp J := funext hSlice
  rw [hSame]
  simpa only [ContinuousLinearMap.comp_zero,add_zero,hSym] using hCompose

end CalderonN
