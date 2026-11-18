import Proof.QuarticCommutatorForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma commutator_product_eq_four_words {R : Type*} [Ring R] (A B C D : R) :
    (A*B)*(C*D)-(C*D)*(A*B)=
      A*(B*C-C*B)*D+A*C*(B*D-D*B)+(A*C-C*A)*D*B+C*(A*D-D*A)*B := by
  noncomm_ring

/-- The polarized four-word weak expression for a mixed adjoint
    commutator of two quadratic words. Its identification with actual
    physical norm squares additionally requires the adjunction/core identity. -/
def polarizedQuarticWeakForm {ι : Type*}
    (SL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (SH SDH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (KL : ι → ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : ι → ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (a b c e : ι) (u : SphereSobolev (3/2:ℝ)) : ℝ :=
  sphereSobolevDualPairing (-(1/2:ℝ)) (KL b c (SH e u)) (SH a u)+
  sphereSobolevDualPairing (-(1/2:ℝ)) (SL c (KH b e u)) (SH a u)+
  sphereSobolevDualPairing (-(1/2:ℝ)) (SL e (SDH b u)) (KH c a u)+
  sphereSobolevDualPairing (-(1/2:ℝ)) (KL a e (SDH b u)) (SDH c u)

theorem abs_polarizedQuarticWeakForm_le {ι : Type*}
    (SL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (SH SDH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (KL : ι → ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : ι → ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (w : ι → ℝ) {CG CK : ℝ} (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hw : ∀ i,0 ≤ w i)
    (hSL : ∀ i,‖SL i‖ ≤ CG*w i) (hSH : ∀ i,‖SH i‖ ≤ CG*w i) (hSDH : ∀ i,‖SDH i‖ ≤ CG*w i)
    (hKL : ∀ i j,‖KL i j‖ ≤ CK*w i*w j) (hKH : ∀ i j,‖KH i j‖ ≤ CK*w i*w j)
    (a b c e : ι) (u : SphereSobolev (3/2:ℝ)) :
    |polarizedQuarticWeakForm SL SH SDH KL KH a b c e u| ≤
      (4*CG^2*CK*(w a*w b*w c*w e))*‖u‖^2 := by
  have hWord (A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
      (B D : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
      {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) (hD : ‖D‖ ≤ c) :
      |sphereSobolevDualPairing (-(1/2:ℝ)) (A (B u)) (D u)| ≤ a*b*c*‖u‖^2 :=
    (abs_sphereSobolevDualPairing_comp_apply_le A B D u).trans (by gcongr)
  have hG (i : ι) : 0 ≤ CG*w i := mul_nonneg hCG (hw i)
  have hK (i j : ι) : 0 ≤ CK*w i*w j := mul_nonneg (mul_nonneg hCK (hw i)) (hw j)
  have h1 := hWord (KL b c) (SH e) (SH a) (hK b c) (hG e) (hG a) (hKL b c) (hSH e) (hSH a)
  have h2 := hWord (SL c) (KH b e) (SH a) (hG c) (hK b e) (hG a) (hSL c) (hKH b e) (hSH a)
  have h3 := hWord (SL e) (SDH b) (KH c a) (hG e) (hG b) (hK c a) (hSL e) (hSDH b) (hKH c a)
  have h4 := hWord (KL a e) (SDH b) (SDH c) (hK a e) (hG b) (hG c) (hKL a e) (hSDH b) (hSDH c)
  have hAbs (A B C D : ℝ) : |A+B+C+D| ≤ |A|+|B|+|C|+|D| :=
    (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
  exact ((hAbs _ _ _ _).trans (add_le_add (add_le_add (add_le_add h1 h2) h3) h4)).trans_eq (by ring)
end ShrinkingSpheres
