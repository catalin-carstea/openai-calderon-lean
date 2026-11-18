import Proof.ParallelNormAssemblyReservedSectors
import Proof.PhysicalPotentialCoreNormIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma inner_weighted_sum_pair_sub {V H κ : Type*} [Fintype κ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : V →L[ℝ] H) (p q : κ → ℝ) (f r : κ → V) (R : κ → κ → ℝ)
    (hR : ∀ z v,⟪J (f z),J (f v)⟫_ℝ-⟪J (r z),J (r v)⟫_ℝ=R z v) :
    ⟪J (∑ z,p z • f z),J (∑ v,q v • f v)⟫_ℝ-
      ⟪J (∑ z,p z • r z),J (∑ v,q v • r v)⟫_ℝ=
      ∑ z,∑ v,(p z*q v)*R z v := by
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro v _
  rw [← mul_assoc,← mul_assoc,← mul_sub,hR z v]
  ring

def quadraticWordForwardCoreValue {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (V : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ)) : SphereSobolev (1/2:ℝ) :=
  ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
    p a b • P.potentialGeneratorHigh y a (V b)

def quadraticWordAdjointCoreValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ)) : SphereSobolev (1/2:ℝ) :=
  ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
    p a b • W.adjointHigh b (v a)

/-- Exact mixed physical quadratic-word identity, with all p/q cross
contractions and actual forward/reversed adjoints on the SAME true core. -/
theorem quadratic_word_mixed_core_identity {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (p q : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=P.potentialGeneratorHigh y a u)
    (hv : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v a)=W.adjointHigh a u) :
    let J := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    ⟪J (quadraticWordForwardCoreValue P y p V),J (quadraticWordForwardCoreValue P y q V)⟫_ℝ-
      ⟪J (quadraticWordAdjointCoreValue P W p v),J (quadraticWordAdjointCoreValue P W q v)⟫_ℝ=
      finitePolarizedQuarticWeakForm p q (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y)
        W.adjointHigh W.commLow W.commHigh u := by
  let f := fun z : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex =>
    P.potentialGeneratorHigh y z.1 (V z.2)
  let r := fun z : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex =>
    W.adjointHigh z.2 (v z.1)
  let R := fun (z w : PhysicalPotentialGeneratorIndex × PhysicalPotentialGeneratorIndex) =>
    polarizedQuarticWeakForm (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y)
      W.adjointHigh W.commLow W.commHigh z.2 z.1 w.1 w.2 u
  have h := inner_weighted_sum_pair_sub (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
    (fun z => p z.1 z.2) (fun z => q z.1 z.2) f r R
    (fun z w => P.potential_word_norm_pair_difference hy W u V v hV hv z.1 z.2 w.1 w.2)
  simpa only [quadraticWordForwardCoreValue,quadraticWordAdjointCoreValue,
    finitePolarizedQuarticWeakForm,Fintype.sum_prod_type,f,r,R] using h

/-- Uniform pointwise mixed word bound for any actual potential packet.
The forward-generator budget is enlarged numerically, retaining W itself. -/
theorem quadratic_word_mixed_core_bound {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (hr : 0 ≤ d.radius y) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (p q : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V a)=P.potentialGeneratorHigh y a u)
    (hv : ∀ a,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v a)=W.adjointHigh a u) :
    let J := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    let G := max (physicalPotentialGeneratorBudget CF) CG
    |⟪J (quadraticWordForwardCoreValue P y p V),J (quadraticWordForwardCoreValue P y q V)⟫_ℝ-
      ⟪J (quadraticWordAdjointCoreValue P W p v),J (quadraticWordAdjointCoreValue P W q v)⟫_ℝ| ≤
      (4*G^2*CK)*(quadraticWordCoefficientMass p (potentialGeneratorWeight (d.radius y))*
        quadraticWordCoefficientMass q (potentialGeneratorWeight (d.radius y)))*‖u‖^2 := by
  dsimp only
  rw [quadratic_word_mixed_core_identity P hy W p q u V v hV hv]
  let G := max (physicalPotentialGeneratorBudget CF) CG
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hw := potentialGeneratorWeight_nonneg hr
  have hF (a : PhysicalPotentialGeneratorIndex) := P.potential_generator_norm_bounds hy hr a
  apply abs_finitePolarizedQuarticWeakForm_le p q _ _ _ _ _ _ hG hCK hw
  · intro a
    exact (hF a).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw a))
  · intro a
    exact (hF a).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hw a))
  · intro a
    exact (W.adjoint_bound a).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hw a))
  · exact W.commLow_bound
  · exact W.commHigh_bound

end ShrinkingSpheres.ParallelEnergy
