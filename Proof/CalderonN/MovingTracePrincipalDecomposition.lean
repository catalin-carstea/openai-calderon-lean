module

public import Proof.CalderonN.MovingTraceBaseCommutators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Defs

import Mathlib.Tactic

/-! Exact separation of the raised model in the moving trace equation.
All coefficients act on the left. The only cancellation assumptions are
the flat second raising identity and symmetry of the background coefficient. -/

public section

open scoped BigOperators
set_option autoImplicit false
namespace CalderonN

section
variable {R ι : Type*} [Ring R] [Fintype ι]

private theorem movingTrace_square_monomial (V V' D D' E E' F F' : R) :
    (V+D+E+F)*(V'+D'+E'+F') =
      V*V' + (V*D'+V'*D) + (D*V'-V'*D) +
      (V*E'+E*V') + (V*F'+F*V') +
      (D*D'+(E'+F')*D+(E+F)*D'+(E+F)*(E'+F')) +
      (D*(E'+F')-(E'+F')*D) := by
  noncomm_ring

/-- On any common operator core, the exact moving trace square separates
into the background raising cross term, the perturbation of total order two,
and the specified commutators and lower order coefficient products. -/
theorem movingTrace_principal_decomposition
    (g h : ι → ι → R) (b V D E F : ι → R)
    (hg : ∀ i j, g i j = g j i)
    (hVV : (∑ i, ∑ j, g i j*(V i*V j)) = 0) :
    let a := g+h
    let W := E+F
    let T := ∑ i, ∑ j, g i j*(V i*D j)
    let U := (∑ i, ∑ j, h i j*(V i*V j+V i*D j+V j*D i)) +
      (∑ i, ∑ j, a i j*(V i*E j+E i*V j+
        (D i*D j+W j*D i+W i*D j+W i*W j))) + ∑ i, b i*(D i+W i)
    let J := (∑ i, ∑ j, a i j*((D i*V j-V j*D i)+(V i*F j+F i*V j)+
      (D i*W j-W j*D i))) + ∑ i, b i*V i
    (∑ i, ∑ j, a i j*((V i+D i+E i+F i)*(V j+D j+E j+F j))) +
      (∑ i, b i*(V i+D i+E i+F i)) = T+T+U+J := by
  classical
  dsimp only [Pi.add_apply]
  let a := g+h
  let W := E+F
  let T := ∑ i, ∑ j, g i j*(V i*D j)
  have hVT : (∑ i, ∑ j, g i j*(V j*D i)) = T := by
    rw [Finset.sum_comm]
    dsimp only [T]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro j _
    rw [hg j i]
  have hStep (i j : ι) :
      a i j*((V i+D i+E i+F i)*(V j+D j+E j+F j)) =
        g i j*(V i*V j)+g i j*(V i*D j)+g i j*(V j*D i)+
        h i j*(V i*V j+V i*D j+V j*D i)+
        a i j*(V i*E j+E i*V j+(D i*D j+W j*D i+W i*D j+W i*W j))+
        a i j*((D i*V j-V j*D i)+(V i*F j+F i*V j)+(D i*W j-W j*D i)) := by
    rw [movingTrace_square_monomial]
    dsimp only [a,W,Pi.add_apply]
    noncomm_ring
  change (∑ i, ∑ j, a i j*((V i+D i+E i+F i)*(V j+D j+E j+F j))) +
    (∑ i, b i*(V i+D i+E i+F i)) = T+T+
      ((∑ i, ∑ j, h i j*(V i*V j+V i*D j+V j*D i)) +
       (∑ i, ∑ j, a i j*(V i*E j+E i*V j+
        (D i*D j+W j*D i+W i*D j+W i*W j))) + ∑ i, b i*(D i+W i))+
      ((∑ i, ∑ j, a i j*((D i*V j-V j*D i)+(V i*F j+F i*V j)+
        (D i*W j-W j*D i))) + ∑ i, b i*V i)
  simp_rw [hStep]
  simp only [Finset.sum_add_distrib]
  have hDrift (i : ι) : b i*(V i+D i+E i+F i) = b i*V i+b i*(D i+W i) := by
    simp only [W,Pi.add_apply]
    noncomm_ring
  simp_rw [hDrift, Finset.sum_add_distrib]
  rw [hVV,hVT]
  dsimp only [T]
  abel

end

end CalderonN
