import Proof.OrderedDirectionalHigherJets
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
variable {P Q E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Affine changes of coordinates with invertible linear part commute with
    the total derivative, including at nondifferentiability points. -/
lemma fderiv_comp_affine_equiv (e : P ≃L[ℝ] Q) (b : Q) (F : Q → E) (p : P) :
    fderiv ℝ (fun q => F (b+e q)) p = (fderiv ℝ F (b+e p)).comp e.toContinuousLinearMap := by
  have hh := e.comp_right_fderiv (f:=fun q => F (b+q)) (x:=p)
  simpa only [Function.comp_def,fderiv_comp_add_left] using hh

/-- Ordered directional derivatives transform exactly under an affine
    parameter change, with explicitly related actual vector fields. -/
theorem orderedDirectionalFamily_affine_equiv
    (e : P ≃L[ℝ] Q) (b : Q) (V : ℕ → Q → Q) (W : ℕ → P → P)
    (hVW : ∀ n p,e (W n p) = V n (b+e p)) (F : Q → E) (n : ℕ) :
    orderedDirectionalFamily W (fun p => F (b+e p)) n =
      fun p => orderedDirectionalFamily V F n (b+e p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext p
    change fderiv ℝ (orderedDirectionalFamily W (fun p => F (b+e p)) n) p (W n p) = _
    rw [ih,fderiv_comp_affine_equiv]
    change fderiv ℝ (orderedDirectionalFamily V F n) (b+e p) (e (W n p)) = _
    rw [hVW]
    rfl

/-- Multiplying every vector field by one constant contributes exactly one
    factor per ordered derivative. This is a total-derivative identity. -/
theorem orderedDirectionalFamily_const_smul_fields
    (V : ℕ → P → P) (F : P → E) (c : ℝ) (n : ℕ) :
    orderedDirectionalFamily (fun j p => c • V j p) F n =
      (c^n) • orderedDirectionalFamily V F n := by
  induction n with
  | zero => simp only [orderedDirectionalFamily,pow_zero,one_smul]
  | succ n ih =>
    funext p
    change fderiv ℝ (orderedDirectionalFamily (fun j p => c • V j p) F n) p (c • V n p) = _
    rw [ih,fderiv_const_smul_field]
    simp only [Pi.smul_apply,ContinuousLinearMap.smul_apply,map_smul,orderedDirectionalFamily]
    rw [smul_smul]
    congr 1
    ring

end ShrinkingSpheres
