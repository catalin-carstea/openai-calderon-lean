import Proof.BoundaryAffineCoefficient
import Proof.CoefficientMultiplierTwoJetBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

def realLinearMapOfSubSmul {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (f : E → F)
    (h : ∀ (x y : E) (c : ℝ),f (x-c • y) = f x-c • f y) : E →ₗ[ℝ] F where
  toFun := f
  map_add' x y := by simpa only [neg_one_smul,sub_neg_eq_add] using h x y (-1)
  map_smul' c x := by
    have hz : f 0 = 0 := by simpa only [one_smul,sub_self] using h 0 0 1
    have hs := h 0 x (-c)
    simpa only [RingHom.id_apply,hz,neg_smul,zero_sub,neg_neg] using hs

/-- Normal and each tangential boundary multiplier are linear in the same
    coefficient matrix. Index none denotes the normal component. -/
def boundaryMatrixMultiplier (k : Option I) (F : SmoothCoefficientMatrix 2) :
    SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  match k with
  | none => negativeBoundaryCoefficientMulL (normalCoefficientJet F)
  | some j => negativeBoundaryCoefficientMulL (tangentCoefficientJet F j)

lemma boundaryMatrixMultiplier_sub_smul (k : Option I) (F G : SmoothCoefficientMatrix 2) (c : ℝ) :
    boundaryMatrixMultiplier k (F-c • G) = boundaryMatrixMultiplier k F-c • boundaryMatrixMultiplier k G := by
  cases k with
  | none => exact negativeNormalCoefficient_sub_smul F G c
  | some j => exact negativeTangentCoefficient_sub_smul F G c j

def boundaryMatrixMultiplierLinear (k : Option I) : SmoothCoefficientMatrix 2 →ₗ[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  realLinearMapOfSubSmul (boundaryMatrixMultiplier k) (boundaryMatrixMultiplier_sub_smul k)

/-- Uniform local C1 control for every normal/tangent matrix multiplier. -/
theorem norm_boundaryMatrixMultiplier_local_C1 (k : Option I) (F : SmoothCoefficientMatrix 2)
    (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDeriv : ∀ i j,∀ x ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    ‖boundaryMatrixMultiplier k F‖ ≤ (78*boundaryHalfMultiplierBudget)*q := by
  have hMB := boundaryHalfMultiplierBudget_nonneg
  cases k with
  | none =>
    have hC := normalCoefficientJet_local_C1 F q hq hValue hDeriv
    have hN := norm_nativeNegativeHalfCoefficientMulL_local_C1 (normalCoefficientJet F) (36*q)
      (by positivity) (fun x hx => (hC x hx).1) (fun x hx => (hC x hx).2)
    exact hN.trans (by nlinarith only [mul_nonneg hMB hq])
  | some j =>
    have hC := tangentCoefficientJet_local_C1 F q hq hValue hDeriv j
    have hN := norm_nativeNegativeHalfCoefficientMulL_local_C1 (tangentCoefficientJet F j) (78*q)
      (by positivity) (fun x hx => (hC x hx).1) (fun x hx => (hC x hx).2)
    exact hN.trans_eq (by ring)

theorem norm_boundaryMatrixMultiplier_le (k : Option I) (F : SmoothCoefficientMatrix 2) :
    ‖boundaryMatrixMultiplier k F‖ ≤ (78*boundaryHalfMultiplierBudget)*‖F‖ := by
  have hEntry (i j : I) : ‖F i j‖ ≤ ‖F‖ :=
    (norm_le_pi_norm (F i) j).trans (norm_le_pi_norm F i)
  apply norm_boundaryMatrixMultiplier_local_C1 k F ‖F‖ (norm_nonneg _)
  · intro i j x _
    have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 0 (by omega) x
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h.trans (hEntry i j)
  · intro i j x _
    have h := norm_iteratedFDeriv_coefficientValue_le 2 (F i j) 1 (by omega) x
    simpa only [norm_iteratedFDeriv_one] using h.trans (hEntry i j)

def boundaryMatrixMultiplierL (k : Option I) : SmoothCoefficientMatrix 2 →L[ℝ]
    (SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
  (boundaryMatrixMultiplierLinear k).mkContinuous (78*boundaryHalfMultiplierBudget)
    (norm_boundaryMatrixMultiplier_le k)

end ShrinkingSpheres
