module

public import Proof.CalderonN.PhysicalMovingTraceDecomposition
public import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus

import Mathlib.Tactic

/-! Exact formal adjoint of the physical perturbation before collecting
coordinate-base derivatives. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace CalderonN

variable {V ι : Type*} [AddCommGroup V] [Module ℝ V] [Fintype ι]

@[expose] def movingTracePerturbationAdjoint
    (a h : ι → ι → Module.End ℝ V) (b L D E F : ι → Module.End ℝ V) : Module.End ℝ V :=
  let W := E+F
  (∑ i,∑ j,(L j*L i+D j*L i+D i*L j)*h i j)+
    (∑ i,∑ j,(E j*L i+L j*E i+
      (D j*D i+D i*W j+D j*W i+W j*W i))*a i j)+
    ∑ i,(D i+W i)*b i

theorem pairedAdjoint_movingTracePerturbation
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (a h : ι → ι → Module.End ℝ V)
    (b L D E F L' D' E' F' : ι → Module.End ℝ V)
    (ha : ∀ i j,PairedAdjoint B (a i j) (a i j)) (hh : ∀ i j,PairedAdjoint B (h i j) (h i j))
    (hb : ∀ i,PairedAdjoint B (b i) (b i))
    (hL : ∀ i,PairedAdjoint B (L i) (L' i)) (hD : ∀ i,PairedAdjoint B (D i) (D' i))
    (hE : ∀ i,PairedAdjoint B (E i) (E' i)) (hF : ∀ i,PairedAdjoint B (F i) (F' i)) :
    PairedAdjoint B (movingTracePerturbation a h b L D E F)
      (movingTracePerturbationAdjoint a h b L' D' E' F') := by
  let W := E+F
  let W' := E'+F'
  have hW (i : ι) : PairedAdjoint B (W i) (W' i) := (hE i).add (hF i)
  unfold movingTracePerturbation movingTracePerturbationAdjoint
  dsimp only
  apply PairedAdjoint.add (PairedAdjoint.add ?_ ?_)
    (PairedAdjoint.sum Finset.univ _ _ (fun i _ => (hb i).mul ((hD i).add (hW i))))
  · apply PairedAdjoint.sum Finset.univ _ _
    intro i _
    exact PairedAdjoint.sum Finset.univ _ _ (fun j _ =>
      (hh i j).mul (((hL i).mul (hL j)).add ((hL i).mul (hD j)) |>.add ((hL j).mul (hD i))))
  · apply PairedAdjoint.sum Finset.univ _ _
    intro i _
    exact PairedAdjoint.sum Finset.univ _ _ (fun j _ => (ha i j).mul
      ((((hL i).mul (hE j)).add ((hE i).mul (hL j))).add
        (((((hD i).mul (hD j)).add ((hW j).mul (hD i))).add ((hW i).mul (hD j))).add ((hW i).mul (hW j)))))

end CalderonN
