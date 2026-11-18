import Proof.GradedWeightedCombinationAlgebra
import Proof.GradedHigherEndpointCommutatorBound
import Proof.ActualFrameFirstAdjointError
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace ShrinkingSpheres
variable {Hi Mid Lo : Type*} [NormedAddCommGroup Hi] [NormedSpace ℝ Hi]
  [NormedAddCommGroup Mid] [NormedSpace ℝ Mid] [NormedAddCommGroup Lo] [NormedSpace ℝ Lo]

/-- Separate low/high families may be combined with real frame values.
This includes adjoint versus unsigned physical first-error endpoints. -/
lemma graded_higher_weighted_three_cross_commutator (I0 : Mid →L[ℝ] Lo)
    (Ga Gb : I → Mid →L[ℝ] Lo) (Gah Gbh : I → Hi →L[ℝ] Mid)
    (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hComm : ∀ i j,GradedHigherEndpointCommutatorBound I0 (Ga i) (Gb j) (Gah i) (Gbh j) B)
    (u v : I → ℝ) (hu : ∀ i,|u i| ≤ K) (hv : ∀ j,|v j| ≤ K) :
    GradedHigherEndpointCommutatorBound I0 (∑ i,u i • Ga i) (∑ j,v j • Gb j)
      (∑ i,u i • Gah i) (∑ j,v j • Gbh j) (9*K^2*B) := by
  classical
  choose S hSquare hNorm using hComm
  let R := ∑ i : I,u i • (∑ j : I,v j • S i j)
  have hRow (i : I) : ‖∑ j : I,v j • S i j‖ ≤ 3*K*B :=
    norm_weighted_sum_three_le v (S i) K B hK hv (hNorm i)
  have hRN : ‖R‖ ≤ 9*K^2*B := (norm_weighted_sum_three_le u
    (fun i => ∑ j : I,v j • S i j) K (3*K*B) hK hu hRow).trans_eq (by ring)
  refine ⟨R,?_,hRN⟩
  rw [finite_real_combination_commutator_expansion]
  calc
    _ = ∑ i,∑ j,(u i*v j) • I0.comp (S i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hSquare i j]
    _ = I0.comp R := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [R,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,Finset.smul_sum,smul_smul,map_sum,map_smul]
end ShrinkingSpheres
