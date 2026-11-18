import Proof.FischerFields
import Proof.Archive.SphereHarmonicBridge

noncomputable section
set_option autoImplicit false
open MvPolynomial
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

lemma finitePolynomialField_harmonicHomogeneous {ι : Type*} [Fintype ι] (k : ℕ)
    (b : ι → MvPolynomial I ℝ) (hb : ∀ i,b i ∈ harmonicHomogeneous k) (c : X → ι → ℝ) (y : X) :
    finitePolynomialField b c y ∈ harmonicHomogeneous k :=
  ⟨finitePolynomialField_homogeneous b (fun i => (hb i).1) c y,
    finitePolynomialField_harmonic b (fun i => (hb i).2) c y⟩

end ShrinkingSpheres
