import Proof.ParallelNormAssemblyReservedCubicAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma reverse_linear_commutator_step {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : F) (L : E →L[ℝ] F) (x y : E) : X-L y= -(L x-X)+L (x-y) := by
  rw [map_sub]
  abel

private lemma reverse_linear_commutator_value {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x y z : E) (t k : F)
    (hG : L x-t=k) (hN : x-y= -z) : t-L y= -(L z+k) := by
  calc
    _ = -(L x-t)+L (x-y) := reverse_linear_commutator_step t L x y
    _ = -k+L (-z) := congrArg₂ (fun a b => -a+L b) hG hN
    _ = _ := by rw [map_neg];abel

def quadraticWordForwardWeakValue {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
    p c e • P.potentialGeneratorLow y c (P.potentialGeneratorHigh y e u)

def quadraticWordAdjointWeakValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
    p c e • (P.potentialGeneratorLow y e).adjoint (W.adjointHigh c u)

lemma quadratic_word_weak_adjunction {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (quadraticWordAdjointWeakValue P W p v)=
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (quadraticWordForwardWeakValue P y p u) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hSelf : T.adjoint=T := sphereSobolevHalfNegativeInclusion_adjoint
  have hForward (c : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (P.potential_generator_balanced hy c) u
  have hAdj (c : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (W.adjoint_compatible c) v
  simp only [ContinuousLinearMap.comp_apply] at hForward hAdj
  have hTerm (c e : PhysicalPotentialGeneratorIndex) :
      ⟪J u,(P.potentialGeneratorLow y e).adjoint (W.adjointHigh c v)⟫_ℝ=
      ⟪J v,P.potentialGeneratorLow y c (P.potentialGeneratorHigh y e u)⟫_ℝ := by
    calc
      _ = ⟪P.potentialGeneratorLow y e (J u),W.adjointHigh c v⟫_ℝ :=
        (P.potentialGeneratorLow y e).adjoint_inner_right _ _
      _ = ⟪T (P.potentialGeneratorHigh y e u),W.adjointHigh c v⟫_ℝ := by rw [hForward]
      _ = ⟪P.potentialGeneratorHigh y e u,T (W.adjointHigh c v)⟫_ℝ := by
        simpa only [hSelf] using (T.adjoint_inner_right _ _).symm
      _ = ⟪P.potentialGeneratorHigh y e u,(P.potentialGeneratorLow y c).adjoint (J v)⟫_ℝ := by rw [hAdj]
      _ = ⟪P.potentialGeneratorLow y c (P.potentialGeneratorHigh y e u),J v⟫_ℝ :=
        (P.potentialGeneratorLow y c).adjoint_inner_right _ _
      _ = _ := real_inner_comm _ _
  simp only [sphereSobolevDualPairing,quadraticWordForwardWeakValue,quadraticWordAdjointWeakValue,
    inner_sum,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  rw [hTerm]

/-- The reverse core cubic identity retains the degree shift and every
true adjoint word. Its sign is needed before the leading model Green step. -/
theorem cubic_adjoint_word_core_identity {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V b)=P.potentialGeneratorHigh y b u)
    (hv : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v b)=W.adjointHigh b u) :
    P.potentialGeneratorLow y a (quadraticWordAdjointCoreValue P W p v)-
      quadraticWordAdjointWeakValue P W p (V a)= -cubicWordAdjointCommutatorValue P W a p u := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hMixed (c : PhysicalPotentialGeneratorIndex) :
      W.adjointHigh c (V a)-P.potentialGeneratorHigh y a (v c)=W.commHigh c a u := by
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    have hA := DFunLike.congr_fun (W.adjoint_compatible c) (V a)
    have hF := DFunLike.congr_fun (P.potential_generator_balanced hy a) (v c)
    simp only [ContinuousLinearMap.comp_apply] at hA hF
    rw [map_sub,hA,hF,hV a,hv c]
    exact DFunLike.congr_fun (W.commutator_compatible c a) u
  have hTerm (c e : PhysicalPotentialGeneratorIndex) :
      P.potentialGeneratorLow y a (W.adjointHigh e (v c))-
        (P.potentialGeneratorLow y e).adjoint (W.adjointHigh c (V a))=
      -((P.potentialGeneratorLow y e).adjoint (W.commHigh c a u)+W.commLow e a (W.adjointHigh c u)) := by
    have hG := DFunLike.congr_fun ((W.commutator_compatible e a).trans (W.commutator_balanced e a)) (v c)
    simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at hG
    have hG1 := hG.trans (congrArg (W.commLow e a) (hv c))
    have hNeg : P.potentialGeneratorHigh y a (v c)-W.adjointHigh c (V a)= -W.commHigh c a u := by
      calc
        _ = -(W.adjointHigh c (V a)-P.potentialGeneratorHigh y a (v c)) := by abel
        _ = _ := congrArg Neg.neg (hMixed c)
    exact reverse_linear_commutator_value (P.potentialGeneratorLow y e).adjoint
      (P.potentialGeneratorHigh y a (v c)) (W.adjointHigh c (V a)) (W.commHigh c a u)
      (P.potentialGeneratorLow y a (W.adjointHigh e (v c)))
      (W.commLow e a (W.adjointHigh c u)) hG1 hNeg
  simp only [quadraticWordAdjointCoreValue,quadraticWordAdjointWeakValue,cubicWordAdjointCommutatorValue,
    map_sum,map_smul,←Finset.sum_sub_distrib,←smul_sub,hTerm,smul_neg,Finset.sum_neg_distrib]

private lemma half_pair_inclusion_inner (u v : SphereSobolev (1/2:ℝ)) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) u,
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) v⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) u
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) v) := by
  have h := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2:ℝ) (by norm_num) v u
  exact (real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _))

/-- The actual adjoint core/model-leading pairing is its exact weak
Green partner minus the transposed cubic commutator. No norm is taken
until this identity has cancelled the unwanted higher horizontal order. -/
theorem adjoint_generator_quadratic_core_pair {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u h : SphereSobolev (3/2:ℝ))
    (V v : PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ))
    (hV : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V b)=P.potentialGeneratorHigh y b u)
    (hv : ∀ b,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (v b)=W.adjointHigh b u) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (W.adjointHigh a h),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (quadraticWordAdjointCoreValue P W p v)⟫_ℝ=
    sphereSobolevDualPairing (1/2:ℝ) (P.potentialGeneratorHigh y a u) (quadraticWordForwardWeakValue P y p h)-
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h) (cubicWordAdjointCommutatorValue P W a p u) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hCore := cubic_adjoint_word_core_identity P hy W a p u V v hV hv
  have hExpand : P.potentialGeneratorLow y a (quadraticWordAdjointCoreValue P W p v)=
      quadraticWordAdjointWeakValue P W p (V a)-cubicWordAdjointCommutatorValue P W a p u := by
    calc
      _ = -cubicWordAdjointCommutatorValue P W a p u+quadraticWordAdjointWeakValue P W p (V a) :=
        eq_add_of_sub_eq hCore
      _ = _ := by abel
  have hSelf : T.adjoint=T := sphereSobolevHalfNegativeInclusion_adjoint
  have hA := DFunLike.congr_fun (W.adjoint_compatible a) h
  simp only [ContinuousLinearMap.comp_apply] at hA
  calc
    _ = sphereSobolevDualPairing (1/2:ℝ) (W.adjointHigh a h) (T (quadraticWordAdjointCoreValue P W p v)) :=
      half_pair_inclusion_inner _ _
    _ = sphereSobolevDualPairing (1/2:ℝ) (T (W.adjointHigh a h)) (quadraticWordAdjointCoreValue P W p v) := by
      change ⟪W.adjointHigh a h,T (quadraticWordAdjointCoreValue P W p v)⟫_ℝ=_
      simpa only [sphereSobolevDualPairing,hSelf] using
        T.adjoint_inner_right (W.adjointHigh a h) (quadraticWordAdjointCoreValue P W p v)
    _ = sphereSobolevDualPairing (1/2:ℝ) (J h)
        (P.potentialGeneratorLow y a (quadraticWordAdjointCoreValue P W p v)) := by
      rw [hA]
      exact (P.potentialGeneratorLow y a).adjoint_inner_left _ _
    _ = _ := by
      rw [hExpand]
      have hh := quadratic_word_weak_adjunction P hy W p h (V a)
      have hPair : sphereSobolevDualPairing (1/2:ℝ) (J h) (quadraticWordAdjointWeakValue P W p (V a))=
          sphereSobolevDualPairing (1/2:ℝ) (P.potentialGeneratorHigh y a u) (quadraticWordForwardWeakValue P y p h) := by
        simpa only [hV a] using hh
      dsimp only [sphereSobolevDualPairing] at hPair ⊢
      rw [inner_sub_right]
      exact congrArg (fun r : ℝ => r-⟪J h,cubicWordAdjointCommutatorValue P W a p u⟫_ℝ) hPair

end ShrinkingSpheres.ParallelEnergy
