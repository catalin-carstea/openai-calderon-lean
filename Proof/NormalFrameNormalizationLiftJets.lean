import Proof.PositiveJetCompositionBound
import Proof.UniformNormalFrameNormalizationJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalFrameOrthonormalLift (g : MetricField) (q : NormalFrameParameter × X) : NormalFrameParameter × X :=
  (normalizedOrthonormalFrameParameter g q.1,q.2)

lemma normalFrameOrthonormalLift_eq_self (g : MetricField) (q : NormalFrameParameter × X)
    (he : ∀ i j,metricPair g q.1.1 (q.1.2.2 (axis i)) (q.1.2.2 (axis j)) = if i=j then 1 else 0) :
    normalFrameOrthonormalLift g q = q := by
  rw [normalFrameOrthonormalLift,normalizedOrthonormalFrameParameter_eq_self g q.1 he]

lemma orthonormalNormalFrameCoefficient_eq_comp (g g₁ : MetricField) (E : X × X → X) :
    orthonormalNormalFrameCoefficient g g₁ E = normalFrameNormalizedCoefficient g g₁ E ∘ normalFrameOrthonormalLift g := rfl

lemma contDiffAt_normalFrameOrthonormalLift (g : MetricField) (q : NormalFrameParameter × X)
    (hN : ContDiffAt ℝ ∞ (normalizedOrthonormalFrameParameter g) q.1) :
    ContDiffAt ℝ ∞ (normalFrameOrthonormalLift g) q :=
  (hN.comp q contDiffAt_fst).prodMk contDiffAt_snd

/-- Lifted normalization has uniform positive jets; no zeroth-order center
    or spatial-position bound is asserted or needed. -/
theorem uniform_normalFrameOrthonormalLift_positive_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) (N : ℕ) (hNm : N ≤ m) :
    ∃ D : ℝ,1 ≤ D ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ q : NormalFrameParameter × X,q.1.1 ∈ Ω →
      (∀ i j,metricPair g q.1.1 (q.1.2.2 (axis i)) (q.1.2.2 (axis j)) = if i=j then 1 else 0) →
      ∀ n : ℕ,1 ≤ n → n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameOrthonormalLift g) q‖ ≤ D := by
  obtain ⟨CN,hCN,hNorm⟩ := uniform_normalFrame_parameter_normalization_jet_bounds hΩ K M hK N hNm
  let B := (N.factorial:ℝ)*backgroundAllMetricJetBudget M+1
  have hB : 1 ≤ B := by
    have hBG : 0 ≤ backgroundAllMetricJetBudget M := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
    have hh : 0 ≤ (N.factorial:ℝ)*backgroundAllMetricJetBudget M := by positivity
    dsimp only [B]
    linarith only [hh]
  let A := (N.factorial:ℝ)*CN*B^N
  let D := 1+(N.factorial:ℝ)*A
  have hCN0 : 0 ≤ CN := zero_le_one.trans hCN
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hD : 1 ≤ D := by
    have hh : 0 ≤ (N.factorial:ℝ)*A := by positivity
    dsimp only [D]
    linarith only [hh]
  refine ⟨D,hD,?_⟩
  intro g g₁ g₂ e h q hq he n hn hnN
  have hg (i j : I) := (h.1.1 i j).contDiffAt (hΩ.mem_nhds hq)
  have hN := contDiffAt_normalization_at_orthonormal g q.1 hg he
  have hOuter (j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
      ‖iteratedFDeriv ℝ j (normalizedOrthonormalFrameParameter g) q.1‖ ≤ A := by
    have hh := hNorm g g₁ g₂ e h q.1 hq he j hj hjN
    have hFac : (j.factorial:ℝ) ≤ (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_le hjN
    have hPow : B^j ≤ B^N := pow_le_pow_right₀ hB hjN
    apply hh.trans
    change (j.factorial:ℝ)*CN*B^j ≤ (N.factorial:ℝ)*CN*B^N
    gcongr
  let pi : (NormalFrameParameter × X) →L[ℝ] NormalFrameParameter := ContinuousLinearMap.fst ℝ NormalFrameParameter X
  have hpi : ‖pi‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.1‖ ≤ 1*‖p‖
    simpa only [one_mul] using norm_fst_le p
  have hh := iteratedFDeriv_comp_positive_common_bound pi (normalizedOrthonormalFrameParameter g) q
    pi.contDiff.contDiffAt hN N A 1 hA le_rfl hOuter
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one pi hpi q j hj) n hn hnN
  simp only [one_pow,mul_one] at hh
  have hNormalized : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter × X => normalizedOrthonormalFrameParameter g p.1) q :=
    hN.comp q contDiffAt_fst
  have hSpatial : ContDiffAt ℝ ∞ (fun p : NormalFrameParameter × X => p.2) q := contDiffAt_snd
  change ‖iteratedFDeriv ℝ n (fun p => (normalizedOrthonormalFrameParameter g p.1,p.2)) q‖ ≤ D
  rw [iteratedFDeriv_prodMk hNormalized hSpatial (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod]
  refine max_le (hh.trans (by change (N.factorial:ℝ)*A ≤ D;dsimp only [D];linarith)) ?_
  have hSnd : ‖(ContinuousLinearMap.snd ℝ NormalFrameParameter X)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    change ‖p.2‖ ≤ 1*‖p‖
    simpa only [one_mul] using norm_snd_le p
  exact (norm_iteratedFDeriv_clm_le_one (ContinuousLinearMap.snd ℝ NormalFrameParameter X) hSnd q n hn).trans hD

end ShrinkingSpheres
