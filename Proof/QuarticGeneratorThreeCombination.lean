import Proof.NativePotentialQuarticData
import Proof.GradedWeightedThreeCrossCommutator
import Proof.GradedHigherWeightedThreeCrossCommutator
import Proof.FrameAdjointEndpointCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A real three-term change of coefficients preserves every genuine
quartic generator graph, with explicit finite contraction budgets. Each
selected source row retains the target row's weight. -/
lemma SphereQuarticGeneratorData.three_linear_combinations {ι κ : Type*}
    {L : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))}
    {H : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)} {w : ι → ℝ} {CA CK : ℝ}
    (W : SphereQuarticGeneratorData L H w CA CK)
    (f : κ → I → ι) (c : κ → I → ℝ) (v : κ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hCK : 0 ≤ CK) (hv : ∀ a,0 ≤ v a)
    (hc : ∀ a j,|c a j| ≤ K) (hw : ∀ a j,w (f a j)=v a) :
    Nonempty (SphereQuarticGeneratorData
      (fun a => ∑ j : I,c a j • L (f a j)) (fun a => ∑ j : I,c a j • H (f a j)) v
      (3*K*CA) (9*K^2*CK)) := by
  classical
  let LR (a : κ) := ∑ j : I,c a j • L (f a j)
  let HR (a : κ) := ∑ j : I,c a j • H (f a j)
  let AR (a : κ) := ∑ j : I,c a j • W.adjointHigh (f a j)
  have hLA (a : κ) : (LR a).adjoint=∑ j : I,c a j • (L (f a j)).adjoint := by
    simp only [LR,Fin.sum_univ_three,LinearIsometryEquiv.map_add,LinearIsometryEquiv.map_smulₛₗ,
      starRingEnd_apply,star_trivial]
  have hA (a : κ) : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AR a)=
      (LR a).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
    finite_real_adjoint_balanced_combination
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (fun j => L (f a j)) (fun j => W.adjointHigh (f a j))
      (fun j => W.adjoint_compatible (f a j)) (c a)
  have hAN (a : κ) : ‖AR a‖ ≤ (3*K*CA)*v a := by
    have hNorm (j : I) : ‖W.adjointHigh (f a j)‖ ≤ CA*v a := by
      simpa only [hw a j] using W.adjoint_bound (f a j)
    exact (norm_weighted_sum_three_le (c a) (fun j => W.adjointHigh (f a j)) K (CA*v a)
      hK (hc a) hNorm).trans_eq (by ring)
  have hRows (a b : κ) : Nonempty (GradedBalancedCommutatorBound
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (LR a).adjoint (LR b) (AR a) (HR b) ((9*K^2*CK)*v a*v b)) := by
    let B := CK*v a*v b
    have hB : 0 ≤ B := mul_nonneg (mul_nonneg hCK (hv a)) (hv b)
    have hLo (j k : I) : GradedEndpointCommutatorBound
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
        (L (f a j)).adjoint (L (f b k)) (W.adjointHigh (f a j)) (H (f b k)) B := by
      refine ⟨W.commLow (f a j) (f b k),
        (W.commutator_compatible (f a j) (f b k)).trans (W.commutator_balanced (f a j) (f b k)),?_⟩
      simpa only [hw a j,hw b k] using W.commLow_bound (f a j) (f b k)
    have hHi (j k : I) : GradedHigherEndpointCommutatorBound
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
        (L (f a j)).adjoint (L (f b k)) (W.adjointHigh (f a j)) (H (f b k)) B := by
      refine ⟨W.commHigh (f a j) (f b k),W.commutator_compatible (f a j) (f b k),?_⟩
      simpa only [hw a j,hw b k] using W.commHigh_bound (f a j) (f b k)
    have hFinLo := graded_weighted_three_cross_commutator
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
      (fun j => (L (f a j)).adjoint) (fun k => L (f b k))
      (fun j => W.adjointHigh (f a j)) (fun k => H (f b k)) B K hB hK hLo (c a) (c b) (hc a) (hc b)
    have hFinHi := graded_higher_weighted_three_cross_commutator
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (fun j => (L (f a j)).adjoint) (fun k => L (f b k))
      (fun j => W.adjointHigh (f a j)) (fun k => H (f b k)) B K hB hK hHi (c a) (c b) (hc a) (hc b)
    have hFinLo' := (hFinLo.mono (le_of_eq (by dsimp only [B];ring :
      9*K^2*B=(9*K^2*CK)*v a*v b))).congr (hLA a).symm rfl rfl rfl
    have hFinHi' := (hFinHi.mono (le_of_eq (by dsimp only [B];ring :
      9*K^2*B=(9*K^2*CK)*v a*v b))).congr (hLA a).symm rfl rfl rfl
    exact gradedBalancedCommutatorBound_of_low_high hFinLo' hFinHi' le_rfl le_rfl
  let R (a b : κ) := Classical.choice (hRows a b)
  exact ⟨{ adjointHigh := AR
           commLow := fun a b => (R a b).low
           commHigh := fun a b => (R a b).high
           adjoint_compatible := hA
           commutator_compatible := fun a b => (R a b).graph
           commutator_balanced := fun a b => (R a b).balanced
           adjoint_bound := hAN
           commLow_bound := fun a b => (R a b).low_bound
           commHigh_bound := fun a b => (R a b).high_bound }⟩
end ShrinkingSpheres
