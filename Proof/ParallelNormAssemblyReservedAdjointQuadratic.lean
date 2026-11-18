import Proof.ParallelNormAssemblyReservedAdjointGenerators
import Proof.ParallelNormAssemblyReservedAdjointWordLifts
import Proof.ParallelNormAssemblyReservedAdjointWeakGraph

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

/-- Genuine balanced endpoint squares determine the reverse quadratic
pairing for any finite angular word system, before coefficients are estimated. -/
lemma balanced_quadratic_reverse_pair {ι : Type*} [Fintype ι]
    (L : ι → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H A : ι → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hH : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (H a)=
      (L a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hA : ∀ a,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A a)=
      (L a).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (p : ι → ι → ℝ) (u v : SphereSobolev (3/2:ℝ)) :
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v)
      (∑ c,∑ e,p c e • (L e).adjoint (A c u))=
    sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
      (∑ c,∑ e,p c e • L c (H e v)) := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hSelf : T.adjoint=T := sphereSobolevHalfNegativeInclusion_adjoint
  have hTerm (c e : ι) : ⟪J v,(L e).adjoint (A c u)⟫_ℝ=⟪J u,L c (H e v)⟫_ℝ := by
    have hF := DFunLike.congr_fun (hH e) v
    have hR := DFunLike.congr_fun (hA c) u
    simp only [ContinuousLinearMap.comp_apply] at hF hR
    calc
      _ = ⟪L e (J v),A c u⟫_ℝ := (L e).adjoint_inner_right _ _
      _ = ⟪T (H e v),A c u⟫_ℝ := congrArg (fun z => ⟪z,A c u⟫_ℝ) hF.symm
      _ = ⟪H e v,T (A c u)⟫_ℝ := by
        have hh := T.adjoint_inner_right (H e v) (A c u)
        simpa only [hSelf] using hh.symm
      _ = ⟪H e v,(L c).adjoint (J u)⟫_ℝ := congrArg (fun z => ⟪H e v,z⟫_ℝ) hR
      _ = ⟪L c (H e v),J u⟫_ℝ := (L c).adjoint_inner_right _ _
      _ = _ := real_inner_comm _ _
  simp only [sphereSobolevDualPairing,inner_sum,inner_smul_right]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun t => p c e*t) (hTerm c e)

def normalizedPotentialAdjointWeakL {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (A : PhysicalPotentialGeneratorIndex → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (y : X) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ c : PhysicalPotentialGeneratorIndex,∑ e : PhysicalPotentialGeneratorIndex,
    normalizedPotentialWordCoefficient d y c e • (normalizedPotentialGeneratorLow P y e).adjoint.comp (A c y)

/-- The canonically smooth reverse quadratic coefficient realizes the
SAME actual potential adjoint for ANY coherent fixed W. Equality is through
dense genuine inclusions, never equality of differently graded carriers. -/
lemma actual_potential_adjoint_normalized_eq {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK CA CJ : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (A : NormalizedGeneratorAdjointFirstJets P CA CJ) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (u : SphereSobolev (3/2:ℝ)) :
    quadraticWordAdjointWeakValue P W (PhysicalPrincipalData.potentialWordCoefficient d y) u=
      normalizedPotentialAdjointWeakL P A.high y u := by
  apply (denseRange_sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).eq_of_inner_right ℝ
  intro v
  change sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) _=_
  have hOld := quadratic_word_weak_adjunction P hy W (PhysicalPrincipalData.potentialWordCoefficient d y) v u
  have hNew := balanced_quadratic_reverse_pair (fun a => normalizedPotentialGeneratorLow P y a)
    (fun a => normalizedPotentialGeneratorHigh P y a) (fun a => A.high a y)
    (fun a => normalized_generator_balanced P hy a) (fun a => A.balanced a y hy)
    (normalizedPotentialWordCoefficient d y) u v
  have hForward := DFunLike.congr_fun (potential_quadratic_normalized_coordinate_words P y
    (hd.2.2.2.2.1.2 y hy).1 (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy))) v
  simp only [_root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply] at hForward
  have hOldForward : quadraticWordForwardWeakValue P y (PhysicalPrincipalData.potentialWordCoefficient d y) v=
      P.potentialQuadraticHalfL y v := by
    rw [P.potentialQuadraticHalfL_eq_word_matrix]
    simp only [quadraticWordForwardWeakValue,PhysicalPrincipalData.potentialWordMatrixL,
      _root_.sum_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply]
  rw [hOldForward] at hOld
  have hNew' : sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v) (normalizedPotentialAdjointWeakL P A.high y u)=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (P.potentialQuadraticHalfL y v) := by
    rw [←hForward] at hNew
    simpa only [normalizedPotentialAdjointWeakL,_root_.sum_apply,_root_.smul_apply,
      ContinuousLinearMap.comp_apply] using hNew
  exact hOld.trans hNew'.symm

end ShrinkingSpheres.ParallelEnergy
