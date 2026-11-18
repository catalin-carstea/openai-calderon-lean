import Proof.ParallelModelFirstZeroJet
import Proof.ParallelNormAssemblyReservedCubicCorePair
import Proof.ParallelScalarModelSkew

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Only the exact background R_c D word occurs here. The corrected
reverse word remains the true R_c†(D−I), through genuine adjunction. -/
def modelFirstZeroWordCoefficient (d : Data) (c : I) (y : X) :
    PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ
  | .inr (.inl i),.inl _ => frameCoordinateLinear d.γ d.frame y i (axis c)
  | _,_ => 0

lemma model_first_zero_forward_weak_word {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (c : I) (y : X) (u : SphereSobolev (3/2:ℝ)) :
    quadraticWordForwardWeakValue P y (modelFirstZeroWordCoefficient d c y) u=
      framedRaisingHalfL d y (axis c) (degreeHigherL u) := by
  simp only [quadraticWordForwardWeakValue,modelFirstZeroWordCoefficient,Fintype.sum_sum_type,Fintype.sum_unique,
    zero_smul,Finset.sum_const_zero,add_zero,zero_add,PhysicalPrincipalData.potentialGeneratorLow,
    PhysicalPrincipalData.potentialGeneratorHigh,framedRaisingHalfL,_root_.sum_apply,_root_.smul_apply]
  rfl

lemma model_first_zero_adjoint_weak_word {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (c : I) (u : SphereSobolev (3/2:ℝ)) :
    quadraticWordAdjointWeakValue P W (modelFirstZeroWordCoefficient d c y) u=modelFirstZeroAdjointWeakL d c y u := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  apply (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).eq_of_inner_right ℝ
  intro z
  change sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z)
    (quadraticWordAdjointWeakValue P W (modelFirstZeroWordCoefficient d c y) u)=_
  rw [quadratic_word_weak_adjunction P hy W,model_first_zero_forward_weak_word]
  exact framed_raising_degree_half_pair Q hQ d y (axis c) u z

/-- The sparse raw-word core has precisely the actual model zero term
on the SAME H5/2 source, independent of the packet's pointwise lift choice. -/
lemma model_first_zero_forward_core_word {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (c : I) (y : X) (u5 : SphereSobolev (5/2:ℝ))
    (V : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=
      P.potentialGeneratorHigh y a (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5)) :
    quadraticWordForwardCoreValue P y (modelFirstZeroWordCoefficient d c y) V=
      framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0) := by
  have hD : V (.inl ())=scalarModelDegreeSection (fun _ : X => u5) 0 := by
    apply sphereSobolevInclusionL_injective (3/2:ℝ) (1/2:ℝ) (by norm_num)
    rw [hV (.inl ()),scalarModelDegreeSection_half_inclusion]
    rfl
  simp only [quadraticWordForwardCoreValue,modelFirstZeroWordCoefficient,Fintype.sum_sum_type,Fintype.sum_unique,
    zero_smul,Finset.sum_const_zero,add_zero,zero_add,hD,PhysicalPrincipalData.potentialGeneratorHigh,
    framedRaisingHigherL,_root_.sum_apply,_root_.smul_apply]

lemma model_first_zero_word_mass_bound
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y) (c : I) :
    quadraticWordCoefficientMass (modelFirstZeroWordCoefficient d c y) (potentialGeneratorWeight (d.radius y)) ≤ 3*K := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hC (i : I) : |frameCoordinateLinear d.γ d.frame y i (axis c)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hd.2.1.center_mem hy) hFrame c i
  simp only [quadraticWordCoefficientMass,modelFirstZeroWordCoefficient,Fintype.sum_sum_type,Fintype.sum_unique,
    potentialGeneratorWeight,abs_zero,zero_mul,mul_zero,Finset.sum_const_zero,add_zero,zero_add,mul_one]
  exact (Finset.sum_le_sum (fun i _ => hC i)).trans_eq (by simp only [Fin.sum_univ_three];ring)

end ShrinkingSpheres.ParallelEnergy
