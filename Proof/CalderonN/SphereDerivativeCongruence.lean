module

public import Proof.CalderonN.SmoothSphereRotation
public import Proof.CalderonN.SphereHarmonicBridge

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ}
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Agreement on an open family of unit spheres determines base derivatives. -/
lemma fderiv_base_eq_of_eqOn_spheres {Y : Set (X N)} (hY : IsOpen Y) {y : (X N)} (hy : y ∈ Y)
    (z : (UnitSphere N)) (F G : (X N) × (X N) → E) (hF : DifferentiableAt ℝ F (y,z.val))
    (hG : DifferentiableAt ℝ G (y,z.val))
    (hEq : ∀ x ∈ Y,∀ w : (UnitSphere N),F (x,w.val) = G (x,w.val)) (a : (X N)) :
    fderiv ℝ F (y,z.val) (a,0) = fderiv ℝ G (y,z.val) (a,0) := by
  have hP : HasFDerivAt (fun x : (X N) => (x,z.val))
      ((ContinuousLinearMap.id ℝ (X N)).prod (0 : (X N) →L[ℝ] (X N))) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const z.val y)
  have he : (fun x => F (x,z.val)) =ᶠ[nhds y] (fun x => G (x,z.val)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hEq x hx z
  have hd := congrArg (fun L : (X N) →L[ℝ] E => L a) he.fderiv_eq
  have hf : HasFDerivAt (fun x => F (x,z.val)) ((fderiv ℝ F (y,z.val)).comp
      ((ContinuousLinearMap.id ℝ (X N)).prod (0 : (X N) →L[ℝ] (X N)))) y := hF.hasFDerivAt.comp y hP
  have hg : HasFDerivAt (fun x => G (x,z.val)) ((fderiv ℝ G (y,z.val)).comp
      ((ContinuousLinearMap.id ℝ (X N)).prod (0 : (X N) →L[ℝ] (X N)))) y := hG.hasFDerivAt.comp y hP
  rw [hf.fderiv,hg.fderiv] at hd
  exact hd

/-- Agreement on the unit sphere determines every angular rotation derivative. -/
lemma fderiv_rotation_eq_of_eqOn_sphere (z : (UnitSphere N)) (F G : (X N) → E)
    (hF : DifferentiableAt ℝ F z.val) (hG : DifferentiableAt ℝ G z.val)
    (hEq : ∀ w : (UnitSphere N),F w.val = G w.val) (i j : (I N)) :
    fderiv ℝ F z.val (rotationVector i j z.val) =
      fderiv ℝ G z.val (rotationVector i j z.val) := by
  have hr : HasDerivAt (fun t => coordinateRotation i j t z.val) (rotationVector i j z.val) 0 := by
    simpa only [coordinateRotation_zero] using hasDerivAt_coordinateRotation i j 0 z.val
  have hf : HasFDerivAt F (fderiv ℝ F z.val) (coordinateRotation i j 0 z.val) := by
    simpa only [coordinateRotation_zero] using hF.hasFDerivAt
  have hg : HasFDerivAt G (fderiv ℝ G z.val) (coordinateRotation i j 0 z.val) := by
    simpa only [coordinateRotation_zero] using hG.hasFDerivAt
  have hdF := hf.comp_hasDerivAt 0 hr
  have hdG := hg.comp_hasDerivAt 0 hr
  have he : (fun t => F (coordinateRotation i j t z.val)) =
      (fun t => G (coordinateRotation i j t z.val)) := by
    funext t
    exact hEq ⟨coordinateRotation i j t z.val,by
      simpa only [Metric.mem_sphere,dist_zero_right,coordinateRotation_norm] using z.property⟩
  change HasDerivAt (fun t => F (coordinateRotation i j t z.val))
    (fderiv ℝ F z.val (rotationVector i j z.val)) 0 at hdF
  rw [he] at hdF
  exact hdF.unique hdG

lemma fderiv_vertical_rotation_eq_of_eqOn_spheres (y : (X N)) (z : (UnitSphere N)) (F G : (X N) × (X N) → E)
    (hF : DifferentiableAt ℝ F (y,z.val)) (hG : DifferentiableAt ℝ G (y,z.val))
    (hEq : ∀ w : (UnitSphere N),F (y,w.val) = G (y,w.val)) (i j : (I N)) :
    fderiv ℝ F (y,z.val) (0,rotationVector i j z.val) =
      fderiv ℝ G (y,z.val) (0,rotationVector i j z.val) := by
  have hP : HasFDerivAt (fun z : (X N) => (y,z))
      ((0 : (X N) →L[ℝ] (X N)).prod (ContinuousLinearMap.id ℝ (X N))) z.val :=
    (hasFDerivAt_const y z.val).prodMk (hasFDerivAt_id z.val)
  have hh := fderiv_rotation_eq_of_eqOn_sphere z (fun z => F (y,z)) (fun z => G (y,z))
    (hF.comp z.val hP.differentiableAt) (hG.comp z.val hP.differentiableAt) hEq i j
  have hf : HasFDerivAt (fun z => F (y,z)) ((fderiv ℝ F (y,z.val)).comp
      ((0 : (X N) →L[ℝ] (X N)).prod (ContinuousLinearMap.id ℝ (X N)))) z.val := hF.hasFDerivAt.comp z.val hP
  have hg : HasFDerivAt (fun z => G (y,z)) ((fderiv ℝ G (y,z.val)).comp
      ((0 : (X N) →L[ℝ] (X N)).prod (ContinuousLinearMap.id ℝ (X N)))) z.val := hG.hasFDerivAt.comp z.val hP
  rw [hf.fderiv,hg.fderiv] at hh
  exact hh

end CalderonN
