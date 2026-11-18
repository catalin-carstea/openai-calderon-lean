import Proof.PolarizedQuarticWeakForm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def quadraticWordCoefficientMass {ι : Type*} [Fintype ι] (p : ι → ι → ℝ) (w : ι → ℝ) : ℝ :=
  ∑ a,∑ b,|p a b| *w a*w b

def finitePolarizedQuarticWeakForm {ι : Type*} [Fintype ι]
    (p q : ι → ι → ℝ)
    (SL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (SH SDH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (KL : ι → ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : ι → ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (u : SphereSobolev (3/2:ℝ)) : ℝ :=
  ∑ a,∑ b,∑ c,∑ e,(p a b*q c e)*polarizedQuarticWeakForm SL SH SDH KL KH b a c e u

/-- The complete matrix of mixed four-word expressions is controlled
    by the product of weighted coefficient masses, including all cross terms. -/
theorem abs_finitePolarizedQuarticWeakForm_le {ι : Type*} [Fintype ι]
    (p q : ι → ι → ℝ)
    (SL : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (SH SDH : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (KL : ι → ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KH : ι → ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (w : ι → ℝ) {CG CK : ℝ} (hCG : 0 ≤ CG) (hCK : 0 ≤ CK) (hw : ∀ i,0 ≤ w i)
    (hSL : ∀ i,‖SL i‖ ≤ CG*w i) (hSH : ∀ i,‖SH i‖ ≤ CG*w i) (hSDH : ∀ i,‖SDH i‖ ≤ CG*w i)
    (hKL : ∀ i j,‖KL i j‖ ≤ CK*w i*w j) (hKH : ∀ i j,‖KH i j‖ ≤ CK*w i*w j)
    (u : SphereSobolev (3/2:ℝ)) :
    |finitePolarizedQuarticWeakForm p q SL SH SDH KL KH u| ≤
      (4*CG^2*CK)*(quadraticWordCoefficientMass p w*quadraticWordCoefficientMass q w)*‖u‖^2 := by
  have hTerm (a b c e : ι) : |(p a b*q c e)*polarizedQuarticWeakForm SL SH SDH KL KH b a c e u| ≤
      (4*CG^2*CK)*((|p a b| *w a*w b)*(|q c e| *w c*w e))*‖u‖^2 := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_left
      (abs_polarizedQuarticWeakForm_le SL SH SDH KL KH w hCG hCK hw hSL hSH hSDH hKL hKH b a c e u)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by ring)
  have hAbs (f : ι → ι → ι → ι → ℝ) :
      |∑ a,∑ b,∑ c,∑ e,f a b c e| ≤ ∑ a,∑ b,∑ c,∑ e,|f a b c e| :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun b _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun c _ => Finset.abs_sum_le_sum_abs _ _))))))
  let R := 4*CG^2*CK
  have hInner (A : ℝ) :
      (∑ c,∑ e,R*(A*(|q c e| *w c*w e))*‖u‖^2)=
        R*A*quadraticWordCoefficientMass q w*‖u‖^2 := by
    simp only [quadraticWordCoefficientMass,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  have hOuter (A : ℝ) :
      (∑ a,∑ b,R*(|p a b| *w a*w b)*A*‖u‖^2)=
        R*quadraticWordCoefficientMass p w*A*‖u‖^2 := by
    simp only [quadraticWordCoefficientMass,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  apply (hAbs _).trans
  calc
    _ ≤ ∑ a,∑ b,∑ c,∑ e,(4*CG^2*CK)*((|p a b| *w a*w b)*(|q c e| *w c*w e))*‖u‖^2 :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => Finset.sum_le_sum
        (fun c _ => Finset.sum_le_sum (fun e _ => hTerm a b c e))))
    _ = ∑ a,∑ b,R*(|p a b| *w a*w b)*quadraticWordCoefficientMass q w*‖u‖^2 :=
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hInner _))
    _ = R*quadraticWordCoefficientMass p w*quadraticWordCoefficientMass q w*‖u‖^2 := hOuter _
    _ = _ := by ring
end ShrinkingSpheres
