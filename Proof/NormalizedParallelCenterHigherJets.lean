import Proof.AffineInverseFamilyJetBounds
import Proof.FiniteJetBudgetAlgebra
import Proof.NormalizedCenterDerivative
import Proof.NormalFrameMatrixInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalizedParallelCenterHigherJetBudget (N : ℕ) (CE CG : ℝ) : ℝ :=
  2^N*inverseFamilyJetBudget N 2 CE*(CE+2^N*CE*(2^N*((N.factorial:ℝ)*CG)))

/-- The actual normalized parallel-center Jacobian has every finite joint
    center/velocity jet from the SAME endpoint, connection and inverse data. -/
theorem normalizedParallelCenter_higher_jets_of_data
    (g : MetricField) (E : X × X → X) (p : X × X)
    (hE : ContDiffAt ℝ ∞ E p) (hG : ContDiffAt ℝ ∞ (connectionBilinear g) p.1)
    (N : ℕ) (CE CG : ℝ) (hCE : 0 ≤ CE) (hCG : 0 ≤ CG) (hv : ‖p.2‖ ≤ 1)
    (hEJets : ∀ j : ℕ,1 ≤ j → j ≤ N+1 → ‖iteratedFDeriv ℝ j E p‖ ≤ CE)
    (hGJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (connectionBilinear g) p.1‖ ≤ CG)
    (hInv : (normalVerticalJacobian E p.1 p.2).IsInvertible)
    (hInvNorm : ‖(normalVerticalJacobian E p.1 p.2).inverse‖ ≤ 2) :
    ContDiffAt ℝ ∞ (fun q : X × X => normalizedParallelCenterJacobian g E q.1 q.2) p ∧
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun q : X × X => normalizedParallelCenterJacobian g E q.1 q.2) p‖ ≤
      normalizedParallelCenterHigherJetBudget N CE CG := by
  let DE := fderiv ℝ E
  let J := fun q : X × X => (DE q).comp (ContinuousLinearMap.inr ℝ X X)
  let A := fun q : X × X => (DE q).comp (ContinuousLinearMap.inl ℝ X X)
  let G := connectionBilinear g ∘ (ContinuousLinearMap.fst ℝ X X)
  let Flip := (ContinuousLinearMap.flipₗᵢ ℝ X X X).toContinuousLinearEquiv.toContinuousLinearMap
  let GF := Flip ∘ G
  let v : X × X → X := ContinuousLinearMap.snd ℝ X X
  let GV := fun q => GF q (v q)
  let C := fun q => A q-(J q).comp (GV q)
  let I := fun q => (J q).inverse
  let W := fun q => (I q).comp (C q)
  let BG := (N.factorial:ℝ)*CG
  let BV := 2^N*BG
  let BC := CE+2^N*CE*BV
  have hBG : 0 ≤ BG := by dsimp only [BG];positivity
  have hBV : 0 ≤ BV := by dsimp only [BV];positivity
  have hBC : 0 ≤ BC := by dsimp only [BC];positivity
  have hDE : ContDiffAt ℝ ∞ DE p := hE.fderiv_right (m:=∞) (by simp)
  have hJ : ContDiffAt ℝ ∞ J p := hDE.clm_comp contDiffAt_const
  have hA : ContDiffAt ℝ ∞ A p := hDE.clm_comp contDiffAt_const
  have hG' : ContDiffAt ℝ ∞ G p := hG.comp p (ContinuousLinearMap.fst ℝ X X).contDiff.contDiffAt
  have hGF : ContDiffAt ℝ ∞ GF p := Flip.contDiff.contDiffAt.comp p hG'
  have hvS : ContDiffAt ℝ ∞ v p := (ContinuousLinearMap.snd ℝ X X).contDiff.contDiffAt
  have hGV : ContDiffAt ℝ ∞ GV p := hGF.clm_apply hvS
  have hC : ContDiffAt ℝ ∞ C p := hA.sub (hJ.clm_comp hGV)
  have hInvJ : (J p).IsInvertible := hInv
  have hI : ContDiffAt ℝ ∞ I p := hInvJ.contDiffAt_map_inverse.comp (f:=J) p hJ
  have hW : ContDiffAt ℝ ∞ W p := hI.clm_comp hC
  have hDEJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j DE p‖ ≤ CE := by
    rw [norm_iteratedFDeriv_fderiv]
    exact hEJets (j+1) (by omega) (by omega)
  have hJJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j J p‖ ≤ CE :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le DE (ContinuousLinearMap.inr ℝ X X) p hDE j).trans
      ((mul_le_mul (ContinuousLinearMap.norm_inr_le_one (𝕜:=ℝ) (E:=X) (F:=X)) (hDEJets j hj)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hAJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j A p‖ ≤ CE :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le DE (ContinuousLinearMap.inl ℝ X X) p hDE j).trans
      ((mul_le_mul (ContinuousLinearMap.norm_inl_le_one (𝕜:=ℝ) (E:=X) (F:=X)) (hDEJets j hj)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hGJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j G p‖ ≤ BG := by
    have hh := iteratedFDeriv_comp_common_bound (ContinuousLinearMap.fst ℝ X X) (connectionBilinear g) p
      (ContinuousLinearMap.fst ℝ X X).contDiff.contDiffAt hG N CG 1 hCG le_rfl hGJets
      (fun k hk _ => norm_iteratedFDeriv_clm_le_one (ContinuousLinearMap.fst ℝ X X)
        (by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one;intro q;change ‖q.1‖ ≤ 1*‖q‖;simpa only [one_mul] using norm_fst_le q) p k hk) j hj
    simpa only [one_pow,mul_one] using hh
  have hFlip : ‖Flip‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro B
    change ‖B.flip‖ ≤ 1*‖B‖
    rw [ContinuousLinearMap.opNorm_flip,one_mul]
  have hGFJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j GF p‖ ≤ BG :=
    (norm_iteratedFDeriv_clm_comp_le Flip G p hG' j).trans
      ((mul_le_mul hFlip (hGJ j hj) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hvJets (j : ℕ) (_hj : j ≤ N) : ‖iteratedFDeriv ℝ j v p‖ ≤ 1 := by
    by_cases hj0 : j=0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      change ‖p.2‖ ≤ 1
      exact hv
    · exact norm_iteratedFDeriv_clm_le_one (ContinuousLinearMap.snd ℝ X X)
        (by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one;intro q;change ‖q.2‖ ≤ 1*‖q‖;simpa only [one_mul] using norm_snd_le q) p j (by omega)
  let ev : X →L[ℝ] (X →L[ℝ] X →L[ℝ] X) →L[ℝ] (X →L[ℝ] X) := ContinuousLinearMap.apply ℝ (X →L[ℝ] X)
  have hEv : ‖ev‖ ≤ 1 := by
    change ‖(ContinuousLinearMap.id ℝ (X →L[ℝ] X →L[ℝ] X)).flip‖ ≤ 1
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.norm_id_le
  have hGVJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j GV p‖ ≤ BV := by
    have hh := norm_iteratedFDeriv_bilinear_common_bound ev v GF p hvS hGF N 1 BG zero_le_one hBG hvJets hGFJets j hj
    exact hh.trans (by
      calc
        _ = ‖ev‖*BV := by dsimp only [BV];ring
        _ ≤ 1*BV := mul_le_mul_of_nonneg_right hEv hBV
        _ = _ := one_mul _)
  have hCJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j C p‖ ≤ BC :=
    (norm_iteratedFDeriv_sub_at_le A (fun q => (J q).comp (GV q)) p hA (hJ.clm_comp hGV) j).trans
      (add_le_add (hAJets j hj) (norm_iteratedFDeriv_operator_comp_common_bound J GV p hJ hGV N CE BV hCE hBV hJJets hGVJets j hj))
  have hIJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j I p‖ ≤ inverseFamilyJetBudget N 2 CE :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible J p hInv hJ N 2 CE (by norm_num) hCE hInvNorm
      (fun k _ hk => hJJets k hk) j hj
  have hCeq : C = fun q : X × X => normalParallelCenterJacobian g E q.1 q.2 := by
    funext q
    apply ContinuousLinearMap.ext
    intro a
    have hGVeq : GV q = (connectionBilinear g q.1).flip q.2 := rfl
    change A q a-J q (GV q a) = _
    rw [hGVeq,normalParallelCenterJacobian_apply]
    change fderiv ℝ E q (a,0)-fderiv ℝ E q (0,connectionBilinear g q.1 a q.2) =
      fderiv ℝ E q (a,-connection g q.1 a q.2)
    rw [← map_sub,← connectionBilinear_apply]
    congr 1
    simp only [Prod.mk_sub_mk,sub_zero,zero_sub]
  have hWeq : W = fun q : X × X => normalizedParallelCenterJacobian g E q.1 q.2 := by
    funext q
    change (J q).inverse.comp (C q) = _
    rw [congrFun hCeq q]
    rfl
  rw [← hWeq]
  refine ⟨hW,?_⟩
  intro n hn
  exact norm_iteratedFDeriv_operator_comp_common_bound I C p hI hC N
    (inverseFamilyJetBudget N 2 CE) BC (inverseFamilyJetBudget_nonneg _ _ _ (by norm_num) hCE)
    hBC hIJets hCJets n hn

end ShrinkingSpheres
