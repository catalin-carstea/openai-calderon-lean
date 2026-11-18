import Proof.Archive.PolynomialSphereFields
import Proof.HorizontalRepresentative
import Proof.FischerFields

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereRotationProjection
open OAI.AnisotropicCalderon.CovariantHarmonicEnergy

lemma polynomialConnectionAction_eq_rotations (A : I → I → ℝ) (hA : ∀ i j,A i j = -A j i)
    (p : MvPolynomial I ℝ) :
    polynomialConnectionAction A p = ∑ i,∑ j,(-(1/2 : ℝ)*A i j) • polynomialRotation i j p := by
  have hd (i : I) : A i i = 0 := by have hh := hA i i; linarith
  have hc : C (1/2 : ℝ)*(2 : MvPolynomial I ℝ) = 1 := by
    calc
      _ = C ((1/2 : ℝ)*2) := by simp only [map_mul,map_ofNat]
      _ = 1 := by norm_num
  simp [polynomialConnectionAction,polynomialRotation,smul_eq_C_mul,Fin.sum_univ_three,
    hd,hA 1 0,hA 2 0,hA 2 1]
  ring_nf
  simp only [mul_assoc,hc,mul_one]

def harmonicCovariantDerivative (g : MetricField) (e : Frame) (k : ℕ)
    (U : X → harmonicSphereSubspace k) (y a : X) : harmonicSphereSubspace k :=
  fderiv ℝ U y a + ∑ i,∑ j,(-(1/2 : ℝ)*frameConnectionCoefficient g e y a i j) •
    harmonicSphereRotation k i j (U y)

/-- The actual finite polynomial covariant derivative is the intrinsic Hilbert harmonic
    covariant derivative for any smooth orthonormal frame and metric. -/
theorem polynomialSphereL2_covariantDerivative {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {ι : Type*} [Fintype ι] (k : ℕ) (b : ι → MvPolynomial I ℝ) (hb : ∀ j,b j ∈ harmonicHomogeneous k)
    (c : X → ι → ℝ) (U : X → harmonicSphereSubspace k)
    (hc : ContDiff ℝ ∞ c) (hU : ContDiff ℝ ∞ U)
    (hrep : ∀ y,polynomialSphereL2 (finitePolynomialField b c y) = (U y : SphereL2))
    {y : X} (hy : y ∈ Y) (a : X) :
    polynomialSphereL2 (covariantPolynomialDerivative g e b c y a) =
      (harmonicCovariantDerivative g e k U y a : SphereL2) := by
  rw [covariantPolynomialDerivative,map_add,
    polynomialSphereL2_finite_derivative_eq k b c U hc hU hrep y a,
    polynomialConnectionAction_eq_rotations _ (frameConnection_skew hY h hK e he hframe hy a)]
  have hrot (i j : I) := polynomialSphereL2_rotation_eq k i j
    (finitePolynomialField b c y) (finitePolynomialField_harmonicHomogeneous k b hb c y) (U y) (hrep y)
  simp only [map_sum,map_smul,hrot,harmonicCovariantDerivative,Submodule.coe_add,Submodule.coe_sum,Submodule.coe_smul]

end ShrinkingSpheres
