module

public import Proof.CalderonN.MovingTracePerturbationBaseNormal

import Mathlib.Tactic

/-! The radius is central in the angular fiber ring. Cancel its
inverse in each coefficient before taking any base derivatives. -/

public section

set_option autoImplicit false
namespace CalderonN

variable {R ι : Type*} [Ring R] [Fintype ι]

theorem normalize_movingTrace_coefficients (a q : ι → ι → R) (r s : R)
    (hR : r*s = 1) (hS : s*r = 1)
    (hr : ∀ P : R,P*r = r*P) (hs : ∀ P : R,P*s = s*P)
    (V K G F : ι → R) (DK : ι → ι → R) :
    let h (i j : ι) := r*(r*q i j)
    let U (i : ι) := s*V i
    let E (i : ι) := r*G i
    let W (i : ι) := E i+F i
    (∀ i,movingTraceFirstBaseCoeff a h 0 U K E F i =
      (∑ j,(a i j*(K j+W j)+(r*q i j)*V j))+(∑ j,(a j i*(K j+W j)+(r*q j i)*V j))) ∧
    movingTraceZeroBaseCoeff a h 0 U K E F DK =
      ∑ i,∑ j,(((q i j*V i)*V j+(r*q i j)*(V i*K j+V j*K i))+
        a i j*(V i*G j+G i*V j+K i*K j+W j*K i+W i*K j+W i*W j+DK i j)) := by
  dsimp only
  have cancel (X P : R) : (r*X)*(s*P) = X*P := by
    rw [mul_assoc r X (s*P),← mul_assoc X s P,hs X,← mul_assoc r (s*X) P,
      ← mul_assoc r s X,hR,one_mul]
  have hVV (i j : ι) : (r*(r*q i j))*((s*V i)*(s*V j)) = (q i j*V i)*V j := by
    rw [← mul_assoc (r*(r*q i j)) (s*V i),cancel,mul_assoc r (q i j) (V i),cancel]
  have hVE (i j : ι) : (s*V i)*(r*G j) = V i*G j := by
    rw [mul_assoc s (V i) (r*G j),← mul_assoc (V i) r (G j),hr (V i),
      ← mul_assoc s (r*V i) (G j),← mul_assoc s r (V i),hS,one_mul]
  have hEV (i j : ι) : (r*G i)*(s*V j) = G i*V j := cancel _ _
  have hVK (i j k l : ι) : (r*(r*q i j))*((s*V k)*K l) = ((r*q i j)*V k)*K l := by
    rw [← mul_assoc,cancel]
  constructor
  · intro i
    unfold movingTraceFirstBaseCoeff
    simp only [Pi.zero_apply,zero_add,Pi.add_apply,cancel]
  · unfold movingTraceZeroBaseCoeff movingTracePerturbation
    simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero,Pi.add_apply]
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [mul_add,hVV,hVE,hEV,hVK]
    simp only [← mul_assoc]
    abel

end CalderonN
