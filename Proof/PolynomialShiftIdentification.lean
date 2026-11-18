import Proof.FiberFischer
import Proof.Archive.RaisingAdjointSum
import Proof.Archive.HarmonicDerivativeOperator
import Proof.FiniteFockEnergy

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.SphereDerivativeAdjoint
open OAI.AnisotropicCalderon.HarmonicDerivativeOperator
open OAI.AnisotropicCalderon.HarmonicRaisingModel

lemma polynomialSphereRaising_eq_sphereRaising (m : ℕ) (q : I → MvPolynomial I ℝ) :
    polynomialSphereRaising m q = sphereRaising m q := by
  unfold polynomialSphereRaising sphereRaising
  congr 2
  norm_num
  ring

lemma polynomialSphereL2_derivativeAdjoint_eq (k : ℕ) (i : I) (p : MvPolynomial I ℝ)
    (hp : p ∈ harmonicHomogeneous k) (v : harmonicSphereSubspace k)
    (hrep : polynomialSphereL2 p = (v : SphereL2)) :
    polynomialSphereL2 (sphereDerivativeAdjoint k i p) =
      (harmonicDerivativeAdjoint sphereFischerInner k i v : SphereL2) := by
  have hv : harmonicPolynomialSphereMap k ⟨p,hp⟩ = v := Subtype.ext hrep
  rw [← hv,harmonicDerivativeAdjoint_apply_image]
  rfl

lemma polynomialSphereL2_derivative_eq (k : ℕ) (i : I) (p : MvPolynomial I ℝ)
    (hp : p ∈ harmonicHomogeneous (k+1)) (v : harmonicSphereSubspace (k+1))
    (hrep : polynomialSphereL2 p = (v : SphereL2)) :
    polynomialSphereL2 (pderiv i p) = (harmonicDerivative sphereFischerInner k i v : SphereL2) := by
  have hv : harmonicPolynomialSphereMap (k+1) ⟨p,hp⟩ = v := Subtype.ext hrep
  rw [← hv,harmonicDerivative_apply_image]
  rfl

lemma polynomialSphereL2_raising_eq (m : ℕ) (q : I → MvPolynomial I ℝ)
    (hq : ∀ i,q i ∈ harmonicHomogeneous (m+1)) (v : I → harmonicSphereSubspace (m+1))
    (hrep : ∀ i,polynomialSphereL2 (q i) = (v i : SphereL2)) :
    polynomialSphereL2 (polynomialSphereRaising m q) =
      ∑ i,(harmonicDerivativeAdjoint sphereFischerInner (m+1) i (v i) : SphereL2) := by
  rw [polynomialSphereRaising_eq_sphereRaising,sphereRaising_eq_sum_sphereDerivativeAdjoint,map_sum]
  exact Finset.sum_congr rfl (fun i _ => polynomialSphereL2_derivativeAdjoint_eq (m+1) i (q i) (hq i) (v i) (hrep i))

lemma polynomialSphereL2_lowering_eq (m : ℕ) (q : I → MvPolynomial I ℝ)
    (hq : ∀ i,q i ∈ harmonicHomogeneous (m+1)) (v : I → harmonicSphereSubspace (m+1))
    (hrep : ∀ i,polynomialSphereL2 (q i) = (v i : SphereL2)) :
    polynomialSphereL2 (polynomialDivergence q) =
      ∑ i,(harmonicDerivative sphereFischerInner m i (v i) : SphereL2) := by
  rw [polynomialDivergence,map_sum]
  exact Finset.sum_congr rfl (fun i _ => polynomialSphereL2_derivative_eq m i (q i) (hq i) (v i) (hrep i))

end ShrinkingSpheres
