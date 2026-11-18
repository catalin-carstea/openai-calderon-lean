import Proof.SmoothFiniteJetBounds
import Proof.BanachInverseFamilyJetBounds
noncomputable section
set_option autoImplicit false
namespace ShrinkingSpheres
open scoped ContDiff
namespace SmoothFiniteJetBound
lemma inverse {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : P → E →L[ℝ] E} {p : P} {N : ℕ} {B I : ℝ}
    (hA : SmoothFiniteJetBound A p N B) (hInv : (A p).IsInvertible)
    (hI : 0 ≤ I) (hBound : ‖(A p).inverse‖ ≤ I) :
    SmoothFiniteJetBound (fun q => (A q).inverse) p N
      (I*((N.factorial:ℝ)*(N.factorial:ℝ)*(1+I*B)^N)) := by
  have hB := hA.nonneg
  refine ⟨by positivity,hInv.contDiffAt_map_inverse.comp p hA.smooth,?_⟩
  intro n hn
  exact norm_iteratedFDeriv_inverse_family_le_of_isInvertible A p hInv hA.smooth N I B hI hA.nonneg
    hBound (fun j _ hj => hA.bound j hj) n hn
end SmoothFiniteJetBound
end ShrinkingSpheres
