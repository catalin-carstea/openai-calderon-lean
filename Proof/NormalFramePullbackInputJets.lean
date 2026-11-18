import Proof.PositiveJetCompositionBound
import Proof.NormalVerticalJacobianHigherJets
import Proof.UniversalPullbackMatrixJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def normalFramePullbackInput (g : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) : PullbackMatrixInput :=
  (g (E (normalFrameInput q)),
    (normalVerticalJacobian E (normalFrameInput q).1 (normalFrameInput q).2,q.1.2.2))

lemma contDiffAt_normalFramePullbackInput (g : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) (hE : ContDiffAt ℝ ∞ E (normalFrameInput q))
    (hg : ContDiffAt ℝ ∞ g (E (normalFrameInput q))) :
    ContDiffAt ℝ ∞ (normalFramePullbackInput g E) q := by
  have hV := hE.comp q contDiff_normalFrameInput.contDiffAt
  have hRawJ : ContDiffAt ℝ ∞ (fun p : X × X => normalVerticalJacobian E p.1 p.2) (normalFrameInput q) :=
    (hE.fderiv_right (m:=∞) (by simp)).clm_comp contDiffAt_const
  have hJ := hRawJ.comp q contDiff_normalFrameInput.contDiffAt
  exact (hg.comp q hV).prodMk (hJ.prodMk contDiffAt_fst.snd.snd)

def normalFramePullbackInputJetBudget (N : ℕ) (B Ci Ce K : ℝ) : ℝ :=
  let J := (N.factorial:ℝ)*Ce*Ci^N
  1+(N.factorial:ℝ)*B*(1+J)^N+J+(K+1)

lemma normalFramePullbackInputJetBudget_ge_one (N : ℕ) (B Ci Ce K : ℝ)
    (hB : 0 ≤ B) (hCi : 0 ≤ Ci) (hCe : 0 ≤ Ce) (hK : 0 ≤ K) :
    1 ≤ normalFramePullbackInputJetBudget N B Ci Ce K := by
  have hJ : 0 ≤ (N.factorial:ℝ)*Ce*Ci^N := by positivity
  have hA : 0 ≤ (N.factorial:ℝ)*B*(1+(N.factorial:ℝ)*Ce*Ci^N)^N := by positivity
  dsimp only [normalFramePullbackInputJetBudget]
  linarith only [hJ,hA,hK]

theorem norm_iteratedFDeriv_normalFramePullbackInput_le (g : MetricField) (E : X × X → X)
    (q : NormalFrameParameter × X) (N : ℕ) (B Ci Ce K : ℝ)
    (hB : 0 ≤ B) (hCi : 1 ≤ Ci) (hCe : 0 ≤ Ce) (hK : 0 ≤ K)
    (hE : ContDiffAt ℝ ∞ E (normalFrameInput q))
    (hg : ContDiffAt ℝ ∞ g (E (normalFrameInput q)))
    (hInput : ∀ j : ℕ,1 ≤ j → j ≤ N → ‖iteratedFDeriv ℝ j normalFrameInput q‖ ≤ Ci)
    (hEndpoint : ∀ j : ℕ,1 ≤ j → j ≤ N+1 → ‖iteratedFDeriv ℝ j E (normalFrameInput q)‖ ≤ Ce)
    (hMetric : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j g (E (normalFrameInput q))‖ ≤ B)
    (hFrame : ‖q.1.2.2‖ ≤ K) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (normalFramePullbackInput g E) q‖ ≤
      normalFramePullbackInputJetBudget N B Ci Ce K := by
  let V := E ∘ normalFrameInput
  let JF := (fun p : X × X => normalVerticalJacobian E p.1 p.2) ∘ normalFrameInput
  let AF := g ∘ V
  let BJ := (N.factorial:ℝ)*Ce*Ci^N
  let DE := 1+BJ
  let BA := (N.factorial:ℝ)*B*DE^N
  let C := normalFramePullbackInputJetBudget N B Ci Ce K
  have hCi0 : 0 ≤ Ci := zero_le_one.trans hCi
  have hBJ : 0 ≤ BJ := by dsimp only [BJ];positivity
  have hDE : 1 ≤ DE := by dsimp only [DE];linarith only [hBJ]
  have hBA : 0 ≤ BA := by dsimp only [BA];positivity
  have hBAle : BA ≤ C := by change BA ≤ 1+BA+BJ+(K+1);linarith only [hBJ,hK]
  have hBJle : BJ ≤ C := by change BJ ≤ 1+BA+BJ+(K+1);linarith only [hBA,hK]
  have hKLle : K+1 ≤ C := by change K+1 ≤ 1+BA+BJ+(K+1);linarith only [hBA,hBJ]
  have hV : ContDiffAt ℝ ∞ V q := hE.comp q contDiff_normalFrameInput.contDiffAt
  have hVJets (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) : ‖iteratedFDeriv ℝ j V q‖ ≤ DE := by
    have hh := iteratedFDeriv_comp_positive_common_bound normalFrameInput E q
      contDiff_normalFrameInput.contDiffAt hE N Ce Ci hCe hCi
      (fun k hk hkN => hEndpoint k hk (by omega)) hInput j hj hjN
    exact hh.trans (by change BJ ≤ DE;dsimp only [DE];linarith)
  have hA : ContDiffAt ℝ ∞ AF q := hg.comp q hV
  have hAJets : ‖iteratedFDeriv ℝ n AF q‖ ≤ BA :=
    iteratedFDeriv_comp_common_bound V g q hV hg N B DE hB hDE hMetric hVJets n hn
  have hJ : ContDiffAt ℝ ∞ (fun p : X × X => normalVerticalJacobian E p.1 p.2) (normalFrameInput q) :=
    (hE.fderiv_right (m:=∞) (by simp)).clm_comp contDiffAt_const
  have hJOuter (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun p : X × X => normalVerticalJacobian E p.1 p.2) (normalFrameInput q)‖ ≤ Ce :=
    (norm_iteratedFDeriv_normalVerticalJacobian_le E (normalFrameInput q) hE j).trans
      (hEndpoint (j+1) (by omega) (by omega))
  have hJF : ContDiffAt ℝ ∞ JF q := hJ.comp q contDiff_normalFrameInput.contDiffAt
  have hJBound : ‖iteratedFDeriv ℝ n JF q‖ ≤ BJ := iteratedFDeriv_comp_common_bound
    normalFrameInput _ q contDiff_normalFrameInput.contDiffAt hJ N Ce Ci hCe hCi hJOuter hInput n hn
  have hL : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter × X => p.1.2.2) q := contDiffAt_fst.snd.snd
  have hLBound : ‖iteratedFDeriv ℝ n (fun p : NormalFrameParameter × X => p.1.2.2) q‖ ≤ K+1 := by
    by_cases hn0 : n = 0
    · subst n
      rw [norm_iteratedFDeriv_zero]
      exact hFrame.trans (by linarith)
    · let LP := normalFrameLinearProjection.comp (ContinuousLinearMap.fst ℝ NormalFrameParameter X)
      have hLP : ‖LP‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro p
        change ‖p.1.2.2‖ ≤ 1*‖p‖
        simpa only [one_mul] using (norm_snd_le p.1.2).trans ((norm_snd_le p.1).trans (norm_fst_le p))
      exact (norm_iteratedFDeriv_clm_le_one LP hLP q n (by omega)).trans (by linarith only [hK])
  change ‖iteratedFDeriv ℝ n (fun p => (AF p,(JF p,p.1.2.2))) q‖ ≤ C
  rw [iteratedFDeriv_prodMk hA (hJF.prodMk hL) (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod,
    iteratedFDeriv_prodMk hJF hL (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hAJets.trans hBAle) (max_le (hJBound.trans hBJle) (hLBound.trans hKLle))

end ShrinkingSpheres
