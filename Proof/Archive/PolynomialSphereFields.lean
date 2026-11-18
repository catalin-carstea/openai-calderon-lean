/- Adopted from the selected ZIP, lean/Calderon/CovariantHarmonicEnergy.lean.
   Generic finite L2 polynomial field/derivative and rotation lemmas only; proof bodies preserved.
-/
import Proof.HarmonicFiniteFields
import Proof.Archive.SmoothSphereRotationProjection

set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.CovariantHarmonicEnergy
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity
  SmoothSphereRotationProjection ShrinkingSpheres
variable {ι : Type*} [Fintype ι]

def finitePolynomialSphereMap (b : ι → MvPolynomial (Fin 3) ℝ) :
    (ι → ℝ) →L[ℝ] SphereL2 :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (polynomialSphereL2 (b j))

lemma finitePolynomialSphereMap_apply (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (x : R3) :
    finitePolynomialSphereMap b (c x) = polynomialSphereL2 (finitePolynomialField b c x) := by
  simp [finitePolynomialSphereMap,finitePolynomialField,map_sum,map_smul]

lemma contDiff_polynomialSphereL2_finite (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun x => polynomialSphereL2 (finitePolynomialField b c x)) := by
  simpa only [Function.comp_def,finitePolynomialSphereMap_apply] using
    (finitePolynomialSphereMap b).contDiff.comp hc

lemma fderiv_polynomialSphereL2_finite (b : ι → MvPolynomial (Fin 3) ℝ)
    (c : R3 → ι → ℝ) (hc : ContDiff ℝ ∞ c) (x X : R3) :
    fderiv ℝ (fun y => polynomialSphereL2 (finitePolynomialField b c y)) x X =
      polynomialSphereL2 (finitePolynomialFieldDerivative b c x X) := by
  have h := ((finitePolynomialSphereMap b).hasFDerivAt.comp x
    (hc.differentiable (by simp) x).hasFDerivAt).fderiv
  have heq : (fun y => finitePolynomialSphereMap b (c y)) =
      fun y => polynomialSphereL2 (finitePolynomialField b c y) := by
    funext y; exact finitePolynomialSphereMap_apply b c y
  change fderiv ℝ (fun y => finitePolynomialSphereMap b (c y)) x = _ at h
  rw [heq] at h
  rw [h,ContinuousLinearMap.comp_apply]
  simp [finitePolynomialSphereMap,finitePolynomialFieldDerivative,map_sum,map_smul]

 
lemma polynomialSphereL2_finite_derivative_eq (k : ℕ)
    (b : ι → MvPolynomial (Fin 3) ℝ) (c : R3 → ι → ℝ)
    (U : R3 → harmonicSphereSubspace k) (hc : ContDiff ℝ ∞ c)
    (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ x, polynomialSphereL2 (finitePolynomialField b c x) = (U x : SphereL2))
    (x X : R3) :
    polynomialSphereL2 (finitePolynomialFieldDerivative b c x X) =
      (fderiv ℝ U x X : SphereL2) := by
  have heq : (fun y => polynomialSphereL2 (finitePolynomialField b c y)) =
      fun y => (U y : SphereL2) := funext hrep
  rw [← fderiv_polynomialSphereL2_finite b c hc x X,heq]
  have h := ((harmonicSphereSubspace k).subtypeL.hasFDerivAt.comp x
    (hU.differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun A : R3 →L[ℝ] SphereL2 => A X) h

lemma polynomialSphereL2_rotation_eq (k : ℕ) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) ℝ) (hp : p ∈ harmonicHomogeneous k)
    (v : harmonicSphereSubspace k) (hrep : polynomialSphereL2 p = (v : SphereL2)) :
    polynomialSphereL2 (polynomialRotation i j p) =
      (harmonicSphereRotation k i j v : SphereL2) := by
  have hv : harmonicPolynomialSphereMap k ⟨p,hp⟩ = v := by
    apply Subtype.ext; exact hrep
  rw [← hv,harmonicSphereRotation_apply_image]
  rfl


end OAI.AnisotropicCalderon.CovariantHarmonicEnergy
