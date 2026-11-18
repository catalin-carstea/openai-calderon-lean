import Proof.CompactFiniteJetBound
import Proof.FiniteJetBoundCalculus
import Proof.NormalFrameMatrixInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

abbrev NormalVelocityInput := ℝ × ((X →L[ℝ] X) × X)

def normalVelocityInputL : (NormalFrameParameter × X) →L[ℝ] NormalVelocityInput :=
  LinearMap.mkContinuous
    { toFun := fun q => (q.1.2.1,(q.1.2.2,q.2))
      map_add' := by intro a b;rfl
      map_smul' := by intro c a;rfl }
    1 (by
      intro q
      change ‖(q.1.2.1,(q.1.2.2,q.2))‖ ≤ 1*‖q‖
      have hR : ‖q.1.2.1‖ ≤ ‖q‖ := (norm_fst_le q.1.2).trans ((norm_snd_le q.1).trans (norm_fst_le q))
      have hL : ‖q.1.2.2‖ ≤ ‖q‖ := (norm_snd_le q.1.2).trans ((norm_snd_le q.1).trans (norm_fst_le q))
      simpa only [Prod.norm_def,one_mul] using max_le hR (max_le hL (norm_snd_le q)))

lemma norm_normalVelocityInputL_le_one : ‖normalVelocityInputL‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def universalNormalVelocity (q : NormalVelocityInput) : X := q.1 • q.2.1 q.2.2

lemma contDiff_universalNormalVelocity : ContDiff ℝ ∞ universalNormalVelocity :=
  contDiff_fst.smul (contDiff_snd.fst.clm_apply contDiff_snd.snd)

theorem uniform_normalFrameInput_positive_jet_bounds (K Z : ℝ) (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ q : NormalFrameParameter × X,
      |q.1.2.1| ≤ 1 → ‖q.1.2.2‖ ≤ K → ‖q.2‖ ≤ Z →
      ∀ n : ℕ,1 ≤ n → n ≤ N → ‖iteratedFDeriv ℝ n normalFrameInput q‖ ≤ C := by
  let T : Set NormalVelocityInput := Metric.closedBall (0:ℝ) 1 ×ˢ
    (Metric.closedBall (0:X →L[ℝ] X) K ×ˢ Metric.closedBall (0:X) Z)
  have hT : IsCompact T := (isCompact_closedBall (0:ℝ) 1).prod
    ((isCompact_closedBall (0:X →L[ℝ] X) K).prod (isCompact_closedBall (0:X) Z))
  obtain ⟨B,hB,hBound⟩ := exists_finite_jet_bound_on_compact universalNormalVelocity T hT
    (fun _ _ => contDiff_universalNormalVelocity.contDiffAt) N
  let C := 1+(N.factorial:ℝ)*B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro q hR hL hZ n hn hnN
  have hMem : normalVelocityInputL q ∈ T := by
    change (q.1.2.1,(q.1.2.2,q.2)) ∈ T
    simpa only [T,mem_prod,Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs] using
      And.intro hR (And.intro hL hZ)
  have hVelocity := iteratedFDeriv_comp_common_bound normalVelocityInputL universalNormalVelocity q
    normalVelocityInputL.contDiff.contDiffAt contDiff_universalNormalVelocity.contDiffAt N B 1 hB0 le_rfl
    (fun j hj => hBound j hj _ hMem)
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one normalVelocityInputL norm_normalVelocityInputL_le_one q j hj) n hnN
  simp only [one_pow,mul_one] at hVelocity
  have hV : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter × X => p.1.2.1 • p.1.2.2 p.2) q :=
    contDiffAt_fst.snd.fst.smul (contDiffAt_fst.snd.snd.clm_apply contDiffAt_snd)
  let pi : (NormalFrameParameter × X) →L[ℝ] X :=
    (ContinuousLinearMap.fst ℝ X (ℝ × (X →L[ℝ] X))).comp (ContinuousLinearMap.fst ℝ NormalFrameParameter X)
  have hpi : ‖pi‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.1.1‖ ≤ 1*‖p‖
    simpa only [one_mul] using (norm_fst_le p.1).trans (norm_fst_le p)
  change ‖iteratedFDeriv ℝ n (fun p : NormalFrameParameter × X => (p.1.1,p.1.2.1 • p.1.2.2 p.2)) q‖ ≤ C
  rw [iteratedFDeriv_prodMk contDiffAt_fst.fst hV (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod]
  refine max_le ((norm_iteratedFDeriv_clm_le_one pi hpi q n hn).trans hC) ?_
  exact hVelocity.trans (by change (N.factorial:ℝ)*B ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
