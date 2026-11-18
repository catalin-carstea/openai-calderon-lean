import Proof.PhysicalPotentialActualNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSDoubleQuarticIdentity
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

lemma potential_generator_core_pair (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex)
    (u v : SphereSobolev (3/2:ℝ)) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (P.potentialGeneratorHigh y a u),
      sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) v⟫_ℝ=
    ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (W.adjointHigh a v)⟫_ℝ := by
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let K := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let PL : SphereSobolev (1/2:ℝ) →L[ℝ] (SphereSobolev (-(1/2:ℝ)) →L[ℝ] ℝ) := innerSL ℝ
  let AL := P.potentialGeneratorLow y
  let BL := fun i => (AL i).adjoint
  let A := P.potentialGeneratorHigh y
  let B := W.adjointHigh
  have hA (i : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) : J (A i x)=AL i (I x) :=
    DFunLike.congr_fun (P.potential_generator_balanced hy i) x
  have hB (i : PhysicalPotentialGeneratorIndex) (x : SphereSobolev (3/2:ℝ)) : J (B i x)=BL i (I x) :=
    DFunLike.congr_fun (W.adjoint_compatible i) x
  have hPivot (i : PhysicalPotentialGeneratorIndex) (x z : SphereSobolev (1/2:ℝ)) :
      PL x (AL i z)=PL z (BL i x) :=
    (ContinuousLinearMap.adjoint_inner_left (AL i) z x).symm.trans (real_inner_comm _ _)
  have hPair (x z : SphereSobolev (1/2:ℝ)) : PL x (J z)=⟪K x,K z⟫_ℝ := by
    have h := sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2:ℝ) (by norm_num) z x
    exact (real_inner_comm _ _).trans (h.trans (real_inner_comm _ _))
  have hAdj := (high_pairings_of_low_pivot I J K PL A B AL BL hA hB hPivot hPair).1 a u (I v)
  rw [←hB a v] at hAdj
  have h := hAdj.trans (hPair (I u) (B a v))
  simpa only [I,J,K,A,B,sphereSobolevInclusionL_trans_apply] using h

/-- Genuine physical adjunction for the full quadratic word matrix on a
common H5/2 core. This certifies the reverse output used in the norm identity. -/
lemma potentialQuadraticCoreL_pair (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    {CG CK : ℝ} (W : PhysicalPotentialQuarticData P y CG CK) (u v : SphereSobolev (5/2:ℝ)) :
    ⟪P.potentialQuadraticCoreL W u,sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) u,P.potentialQuadraticAdjointCoreL W v⟫_ℝ := by
  let U := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u
  let V := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) v
  let K := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let J := sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num)
  have hForward (b : PhysicalPotentialGeneratorIndex) :
      J (W.forwardFirstWordHigherL b u)=K (P.potentialGeneratorHigh y b U) := by
    have h := congrArg K (W.forwardFirstWordHigherL_inclusion hy b u)
    simpa only [K,sphereSobolevInclusionL_trans_apply] using h
  have hReverse (a : PhysicalPotentialGeneratorIndex) :
      J (W.reverseFirstWordHigherL a v)=K (W.adjointHigh a V) := by
    have h := congrArg K (W.reverseFirstWordHigherL_inclusion a v)
    simpa only [K,sphereSobolevInclusionL_trans_apply] using h
  have hWord (a b : PhysicalPotentialGeneratorIndex) :
      ⟪K (P.potentialGeneratorHigh y a (W.forwardFirstWordHigherL b u)),J V⟫_ℝ=
        ⟪J U,K (W.adjointHigh b (W.reverseFirstWordHigherL a v))⟫_ℝ := by
    have h1 := P.potential_generator_core_pair hy W a (W.forwardFirstWordHigherL b u) V
    have h2 := P.potential_generator_core_pair hy W b U (W.reverseFirstWordHigherL a v)
    rw [hForward b,←hReverse a] at h1
    exact h1.trans h2
  have hJV : J V=sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) v := sphereSobolevInclusionL_trans_apply _ _ _ _ _ v
  have hJU : J U=sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) u := sphereSobolevInclusionL_trans_apply _ _ _ _ _ u
  simp only [potentialQuadraticCoreL,potentialQuadraticAdjointCoreL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,inner_smul_right]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact congrArg (fun t : ℝ => potentialWordCoefficient d y a b*t)
    (by simpa only [hJV,hJU] using hWord a b)
end PhysicalPrincipalData
end ShrinkingSpheres
