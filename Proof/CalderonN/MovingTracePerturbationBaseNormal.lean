module

public import Proof.CalderonN.PhysicalMovingTraceDecomposition

import Mathlib.Tactic

/-! The actual perturbation has a scalar second-base coefficient.
Its other coefficients are products of the fiber operators and the
explicit derivative of the horizontal connection. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace CalderonN

variable {R ι : Type*} [Ring R] [Fintype ι]

@[expose] def movingTraceFirstBaseCoeff (a h : ι → ι → R) (b V K E F : ι → R) (i : ι) : R :=
  let W := E+F
  b i+(∑ j,(a i j*(K j+W j)+h i j*V j))+(∑ j,(a j i*(K j+W j)+h j i*V j))

@[expose] def movingTraceZeroBaseCoeff (a h : ι → ι → R) (b V K E F : ι → R) (DK : ι → ι → R) : R :=
  movingTracePerturbation a h b V K E F+∑ i,∑ j,a i j*DK i j

theorem movingTracePerturbation_base_normal (a h : ι → ι → R) (b V D K E F : ι → R)
    (DK : ι → ι → R) (hDK : ∀ i j,D i*K j = K j*D i+DK i j) :
    movingTracePerturbation a h b V (D+K) E F =
      (∑ i,∑ j,a i j*(D i*D j))+
        (∑ i,movingTraceFirstBaseCoeff a h b V K E F i*D i)+
        movingTraceZeroBaseCoeff a h b V K E F DK := by
  let W := E+F
  let Q := D+K
  have h₁ (i j : ι) : V i*V j+V i*Q j+V j*Q i =
      (V i*V j+V i*K j+V j*K i)+(V i*D j+V j*D i) := by
    dsimp only [Q,Pi.add_apply]
    noncomm_ring
  have h₂ (i j : ι) :
      (Q i*Q j+W j*Q i+W i*Q j+W i*W j) =
        (K i*K j+W j*K i+W i*K j+W i*W j)+
          D i*D j+(K j+W j)*D i+(K i+W i)*D j+DK i j := by
    dsimp only [Q,Pi.add_apply]
    noncomm_ring [hDK i j]
  have h₃ (i : ι) : b i*(Q i+W i) = b i*(K i+W i)+b i*D i := by
    dsimp only [Q,Pi.add_apply]
    noncomm_ring
  unfold movingTraceZeroBaseCoeff movingTraceFirstBaseCoeff
  unfold movingTracePerturbation
  change ((∑ i,∑ j,h i j*(V i*V j+V i*Q j+V j*Q i))+
      (∑ i,∑ j,a i j*(V i*E j+E i*V j+(Q i*Q j+W j*Q i+W i*Q j+W i*W j)))+
      (∑ i,b i*(Q i+W i))) = _
  simp_rw [h₁,h₂,h₃]
  simp only [mul_add,Finset.sum_add_distrib,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm (f:=fun i j => h i j*(V i*D j)),
    Finset.sum_comm (f:=fun i j => a i j*((K i+W i)*D j))]
  simp only [W,add_mul,mul_add,Finset.sum_add_distrib,Finset.sum_mul,mul_assoc]
  abel

end CalderonN
