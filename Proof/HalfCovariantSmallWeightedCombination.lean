import Proof.HalfCovariantWeightedCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- The complementary product estimate: the scalar weights carry the
    smallness, while the physical background operator and its covariant
    derivative have fixed bounds. It reuses the same finite product rule. -/
theorem half_small_weighted_combination_bounds (d : Data) (w : I → X → ℝ)
    (Lo : I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi : I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (y a : X)
    (hwS : ∀ i,ContDiffAt ℝ ∞ (w i) y) (hLS : ∀ i,ContDiffAt ℝ ∞ (Lo i) y)
    {B Q eps β : ℝ} (hB : 0 ≤ B) (hQ : 0 ≤ Q) (heps : 0 ≤ eps) (hβ : 1 ≤ β)
    (hw : ∀ i,|w i y| ≤ B*eps/β) (hdw : ∀ i,|directionalFDeriv a (w i) y| ≤ B*eps)
    (hLo : ∀ i,‖Lo i y‖ ≤ Q) (hHi : ∀ i,‖Hi i y‖ ≤ Q)
    (hD : ∀ i,‖halfOperatorCovariantDerivativeL d (Lo i) (Hi i) y a‖ ≤ Q) :
    ‖∑ i : I,w i y • Lo i y‖ ≤ (6*B*Q)*eps/β ∧
    ‖∑ i : I,w i y • Hi i y‖ ≤ (6*B*Q)*eps/β ∧
    ‖halfOperatorCovariantDerivativeL d (fun x => ∑ i : I,w i x • Lo i x)
      (fun x => ∑ i : I,w i x • Hi i x) y a‖ ≤ (6*B*Q)*eps := by
  have hβP : 0 < β := zero_lt_one.trans_le hβ
  let Bs := B*eps/β
  have hBs : 0 ≤ Bs := div_nonneg (mul_nonneg hB heps) hβP.le
  have hW (i : I) : |directionalFDeriv a (w i) y| ≤ Bs*β :=
    (hdw i).trans_eq (by dsimp only [Bs];field_simp <;> ring)
  have hL (i : I) : ‖Lo i y‖ ≤ Q*β/β := by simpa only [mul_div_cancel_right₀ Q hβP.ne'] using hLo i
  have hH (i : I) : ‖Hi i y‖ ≤ Q*β/β := by simpa only [mul_div_cancel_right₀ Q hβP.ne'] using hHi i
  have hQβ : Q ≤ Q*β := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hQ
  have hAll := half_weighted_combination_bounds d w Lo Hi y a hwS hLS hBs hQ hβP.le hβP
    hw hW hL hH (fun i => (hD i).trans hQβ)
  refine ⟨hAll.1.trans_eq ?_,hAll.2.1.trans_eq ?_,hAll.2.2.trans_eq ?_⟩ <;>
    dsimp only [Bs] <;> field_simp <;> ring
end ShrinkingSpheres
