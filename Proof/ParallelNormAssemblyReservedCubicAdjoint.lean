import Proof.ParallelNormAssemblyReservedCubicWords
import Proof.DenseOperatorRestrictionUnique

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

private lemma selfadjoint_exchange {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : T.adjoint=T) (u v : E) : ⟪T u,v⟫_ℝ=⟪T v,u⟫_ℝ := by
  calc
    _ = ⟪u,T v⟫_ℝ := by simpa only [hT] using (T.adjoint_inner_right u v).symm
    _ = _ := real_inner_comm _ _

/-- Mixed commutator adjunction follows from genuine normalized endpoint
squares and dense inclusion. Only bounded declared endpoints occur. -/
private lemma mixed_low_adjoint {E H ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : E →L[ℝ] E) (J : H →L[ℝ] E) (hT : T.adjoint=T) (hJ : DenseRange J)
    (L : ι → E →L[ℝ] E) (F A : ι → H →L[ℝ] E) (K : ι → ι → E →L[ℝ] E)
    (hF : ∀ a,T.comp (F a)=(L a).comp J)
    (hA : ∀ a,T.comp (A a)=(L a).adjoint.comp J)
    (hK : ∀ a b,(K a b).comp J=(L a).adjoint.comp (F b)-(L b).comp (A a))
    (a b : ι) : (K a b).adjoint=K b a := by
  have hf (c : ι) (u : H) := DFunLike.congr_fun (hF c) u
  have ha (c : ι) (u : H) := DFunLike.congr_fun (hA c) u
  simp only [ContinuousLinearMap.comp_apply] at hf ha
  have hFirst (c e : ι) (u v : H) : ⟪J u,(L c).adjoint (F e v)⟫_ℝ=⟪T (F c u),F e v⟫_ℝ := by
    exact ((L c).adjoint_inner_right (J u) (F e v)).trans
      (congrArg (fun z => ⟪z,F e v⟫_ℝ) (hf c u).symm)
  have hSecond (c e : ι) (u v : H) : ⟪J u,L e (A c v)⟫_ℝ=⟪T (A e u),A c v⟫_ℝ := by
    exact ((L e).adjoint_inner_left (A c v) (J u)).symm.trans
      (congrArg (fun z => ⟪z,A c v⟫_ℝ) (ha e u).symm)
  have hPair (u v : H) : ⟪J u,K a b (J v)⟫_ℝ=⟪J v,K b a (J u)⟫_ℝ := by
    have h0 := DFunLike.congr_fun (hK a b) v
    have h1 := DFunLike.congr_fun (hK b a) u
    simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply] at h0 h1
    rw [h0,h1,inner_sub_right,inner_sub_right,hFirst,hFirst,hSecond,hSecond]
    rw [selfadjoint_exchange T hT (F a u) (F b v),selfadjoint_exchange T hT (A b u) (A a v)]
  apply clm_eq_of_dense_restriction J hJ
  apply ContinuousLinearMap.ext
  intro u
  apply hJ.eq_of_inner_right ℝ
  intro v
  change ⟪J v,(K a b).adjoint (J u)⟫_ℝ=⟪J v,K b a (J u)⟫_ℝ
  calc
    _ = ⟪K a b (J v),J u⟫_ℝ := (K a b).adjoint_inner_right (J v) (J u)
    _ = ⟪J u,K a b (J v)⟫_ℝ := real_inner_comm _ _
    _ = _ := hPair u v

lemma potential_comm_low_adjoint {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (a b : PhysicalPotentialGeneratorIndex) :
    (W.commLow a b).adjoint=W.commLow b a := by
  apply mixed_low_adjoint
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    sphereSobolevHalfNegativeInclusion_adjoint (denseRange_sphereSobolevInclusionL _ _ _)
    (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y) W.adjointHigh W.commLow
    (fun c => P.potential_generator_balanced hy c) W.adjoint_compatible
  intro c e
  exact ((W.commutator_compatible c e).trans (W.commutator_balanced c e)).symm

def cubicWordAdjointCommutatorValue {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (W : PhysicalPotentialQuarticData P y CG CK)
    (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u : SphereSobolev (3/2:ℝ)) : SphereSobolev (-(1/2:ℝ)) :=
  ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,p c e •
    ((P.potentialGeneratorLow y e).adjoint (W.commHigh c a u)+W.commLow e a (W.adjointHigh c u))

/-- Transpose the actual cubic commutator before norms. This puts the
horizontal source at H1/2 and the undifferentiated source at H3/2. -/
theorem cubic_word_commutator_dual_adjoint {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex)
    (p : PhysicalPotentialGeneratorIndex → PhysicalPotentialGeneratorIndex → ℝ)
    (u v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (cubicWordCommutatorValue P W a p u)=
    sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (cubicWordAdjointCommutatorValue P W a p v) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hForward (b : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (P.potential_generator_balanced hy b) u
  have hAdj (b : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (W.adjoint_compatible b) v
  have hComm (b c : PhysicalPotentialGeneratorIndex) (z : SphereSobolev (3/2:ℝ)) :=
    DFunLike.congr_fun (W.commutator_balanced b c) z
  simp only [ContinuousLinearMap.comp_apply] at hForward hAdj hComm
  have hSelf : T.adjoint=T := sphereSobolevHalfNegativeInclusion_adjoint
  have hTranspose (x z : SphereSobolev (1/2:ℝ)) : ⟪T x,z⟫_ℝ=⟪x,T z⟫_ℝ := by
    simpa only [hSelf] using (T.adjoint_inner_right x z).symm
  have h1 (c e : PhysicalPotentialGeneratorIndex) :
      ⟪J v,W.commLow a c (P.potentialGeneratorHigh y e u)⟫_ℝ=
        ⟪J u,(P.potentialGeneratorLow y e).adjoint (W.commHigh c a v)⟫_ℝ := by
    calc
      _ = ⟪(W.commLow a c).adjoint (J v),P.potentialGeneratorHigh y e u⟫_ℝ :=
        ((W.commLow a c).adjoint_inner_left _ _).symm
      _ = ⟪T (W.commHigh c a v),P.potentialGeneratorHigh y e u⟫_ℝ := by
        rw [potential_comm_low_adjoint P hy W,hComm]
      _ = ⟪W.commHigh c a v,T (P.potentialGeneratorHigh y e u)⟫_ℝ := hTranspose _ _
      _ = ⟪W.commHigh c a v,P.potentialGeneratorLow y e (J u)⟫_ℝ := by rw [hForward]
      _ = ⟪(P.potentialGeneratorLow y e).adjoint (W.commHigh c a v),J u⟫_ℝ :=
        ((P.potentialGeneratorLow y e).adjoint_inner_left _ _).symm
      _ = _ := real_inner_comm _ _
  have h2 (c e : PhysicalPotentialGeneratorIndex) :
      ⟪J v,P.potentialGeneratorLow y c (W.commHigh a e u)⟫_ℝ=
        ⟪J u,W.commLow e a (W.adjointHigh c v)⟫_ℝ := by
    calc
      _ = ⟪(P.potentialGeneratorLow y c).adjoint (J v),W.commHigh a e u⟫_ℝ :=
        ((P.potentialGeneratorLow y c).adjoint_inner_left _ _).symm
      _ = ⟪T (W.adjointHigh c v),W.commHigh a e u⟫_ℝ := by rw [hAdj]
      _ = ⟪W.adjointHigh c v,T (W.commHigh a e u)⟫_ℝ := hTranspose _ _
      _ = ⟪W.adjointHigh c v,W.commLow a e (J u)⟫_ℝ := by rw [hComm]
      _ = ⟪(W.commLow a e).adjoint (W.adjointHigh c v),J u⟫_ℝ :=
        ((W.commLow a e).adjoint_inner_left _ _).symm
      _ = _ := by rw [potential_comm_low_adjoint P hy W,real_inner_comm]
  simp only [sphereSobolevDualPairing,cubicWordCommutatorValue,cubicWordAdjointCommutatorValue,
    inner_sum,real_inner_smul_right,inner_add_right]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  rw [h1,h2]

end ShrinkingSpheres.ParallelEnergy
