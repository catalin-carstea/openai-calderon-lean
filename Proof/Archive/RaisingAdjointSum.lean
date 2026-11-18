/- Adopted from the selected ZIP, lean/Calderon/HarmonicRaisingModel.lean.
   Generic polynomial raising-as-adjoint-sum lemma only; proof body preserved.
-/
import Proof.Archive.SphereDerivativeAdjoint

set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.FiniteRaisingEnergy
open SphereHarmonic AngularPolynomial

lemma sphereRaising_sum_family {σ : Type*} [Fintype σ] (m : ℕ)
    (q : σ → Fin 3 → MvPolynomial (Fin 3) ℝ) :
    sphereRaising m (fun i => ∑ a : σ, q a i) = ∑ a : σ, sphereRaising m (q a) := by
  simp only [sphereRaising,harmonicRaising,polynomialRaising,polynomialDivergence,
    Fin.sum_univ_three,map_sum]
  simp only [mul_add,mul_sub,Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]

end OAI.AnisotropicCalderon.FiniteRaisingEnergy

namespace OAI.AnisotropicCalderon.HarmonicRaisingModel
open SphereHarmonic SphereDerivativeAdjoint AngularPolynomial FiniteRaisingEnergy

lemma sphereRaising_eq_sum_sphereDerivativeAdjoint (m : ℕ)
    (q : Fin 3 → MvPolynomial (Fin 3) ℝ) :
    sphereRaising m q = ∑ i : Fin 3, sphereDerivativeAdjoint (m+1) i (q i) := by
  simp_rw [sphereDerivativeAdjoint_eq_raisingComponent (m+1) (by omega)]
  simp only [raisingComponent,Nat.add_sub_cancel]
  rw [← sphereRaising_sum_family]
  congr 1
  funext j
  simp [Pi.single_apply]


end OAI.AnisotropicCalderon.HarmonicRaisingModel
