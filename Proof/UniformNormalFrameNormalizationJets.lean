import Proof.NormalFrameMatrixInputJets
import Proof.FirstMetricNormalDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- All finite independent jets of the genuine frame normalization are
uniform over admitted metrics. Constants come from the fixed universal
matrix normalization and the frozen metric budgets; no quantitative jet
of the arbitrary supplied frame field is assumed. -/
theorem uniform_normalFrame_normalization_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) (N : ℕ) (hNm : N ≤ m) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),
      Background Ω K M g g₁ g₂ e → ∀ p : NormalFrameParameter,p.1 ∈ Ω →
      (∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) →
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameNormalizedLinear g) p‖ ≤
        (n.factorial:ℝ)*C*(((N.factorial:ℝ)*backgroundAllMetricJetBudget M+1)^n) := by
  obtain ⟨C,hC,hBound⟩ := exists_universalMatrixFrameNormalizer_jet_bound |M 0| K N
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h p hp he n hn
  have hg : ContDiffAt ℝ ∞ g p.1 :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hp)))
  have hG0 : ‖g p.1‖ ≤ |M 0| := by
    have ht := h.reference_matrix_jet_bound hΩ (0:Fin (m+1)) hp
    change ‖iteratedFDeriv ℝ 0 g p.1‖ ≤ |M 0| at ht
    rwa [norm_iteratedFDeriv_zero] at ht
  let eL : Frame := fun _ i => p.2.2 (axis i)
  have hL : frameVectorLinear eL p.1 = p.2.2 := by
    apply ContinuousLinearMap.ext
    intro v
    exact frameVector_linear_axes p.2.2 p.1 v
  have hLNorm : ‖p.2.2‖ ≤ K := by
    rw [← hL]
    exact h.1.norm_frameVectorLinear_le hK hp eL he
  have hGram : universalFrameGram (g p.1,p.2.2) = ContinuousLinearMap.id ℝ X :=
    normalFrameGramMetric_eq_id g p he
  have hHere : normalFrameMatrixInput g p ∈ universalOrthonormalFrameSet |M 0| K := ⟨hG0,hLNorm,hGram⟩
  have hSmooth := contDiffAt_universalMatrixFrameNormalizer_of_gram_id (normalFrameMatrixInput g p) hGram
  have hInput := contDiffAt_normalFrameMatrixInput g p hg
  have hEq : normalFrameNormalizedLinear g = universalMatrixFrameNormalizer ∘ normalFrameMatrixInput g := by
    funext q
    rfl
  rw [hEq]
  exact norm_iteratedFDeriv_comp_at_bound (normalFrameMatrixInput g) universalMatrixFrameNormalizer p
    hInput hSmooth n C ((N.factorial:ℝ)*backgroundAllMetricJetBudget M+1)
    (fun i hi => hBound i (hi.trans hn) _ hHere)
    (fun i hi hin => h.normalFrameMatrixInput_jet_bound hΩ N hNm hp i hi (hin.trans hn))

def normalFrameRadiusProjection : NormalFrameParameter →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (X →L[ℝ] X)).comp
    (ContinuousLinearMap.snd ℝ X (ℝ × (X →L[ℝ] X)))

lemma norm_normalFrameRadiusProjection_le_one : ‖normalFrameRadiusProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p.2.1‖ ≤ 1*‖p‖
  simpa only [one_mul] using (norm_fst_le p.2).trans (norm_snd_le p)

/-- The complete normalized independent parameter has the same uniform
positive-order jet bounds. Its unrestricted center value is not included
in a zeroth-order size claim. -/
theorem uniform_normalFrame_parameter_normalization_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) (N : ℕ) (hNm : N ≤ m) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),
      Background Ω K M g g₁ g₂ e → ∀ p : NormalFrameParameter,p.1 ∈ Ω →
      (∀ i j,metricPair g p.1 (p.2.2 (axis i)) (p.2.2 (axis j)) = if i=j then 1 else 0) →
      ∀ n : ℕ,1 ≤ n → n ≤ N → ‖iteratedFDeriv ℝ n (normalizedOrthonormalFrameParameter g) p‖ ≤
        (n.factorial:ℝ)*C*(((N.factorial:ℝ)*backgroundAllMetricJetBudget M+1)^n) := by
  obtain ⟨C,hC,hFrame⟩ := uniform_normalFrame_normalization_jet_bounds hΩ K M hK N hNm
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h p hp he n hn hnN
  let D := (N.factorial:ℝ)*backgroundAllMetricJetBudget M+1
  have hB0 : 0 ≤ backgroundAllMetricJetBudget M := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  have hDB : 0 ≤ (N.factorial:ℝ)*backgroundAllMetricJetBudget M := by positivity
  have hD1 : 1 ≤ D := by dsimp only [D];linarith
  have hFact : (1:ℝ) ≤ n.factorial := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos n)
  have hFC : 1 ≤ (n.factorial:ℝ)*C := by
    nlinarith only [hFact,hC,mul_nonneg (sub_nonneg.mpr hFact) (sub_nonneg.mpr hC)]
  have hPow : 1 ≤ D^n := one_le_pow₀ hD1
  have hOne : 1 ≤ (n.factorial:ℝ)*C*D^n := by
    nlinarith only [hFC,hPow,mul_nonneg (sub_nonneg.mpr hFC) (sub_nonneg.mpr hPow)]
  have hg (i j : I) := (h.1.1 i j).contDiffAt (hΩ.mem_nhds hp)
  have hNormalized := contDiffAt_normalization_at_orthonormal g p hg he
  have hFrameSmooth : ContDiffAt ℝ ∞ (normalFrameNormalizedLinear g) p := hNormalized.snd.snd
  let π : NormalFrameParameter →L[ℝ] X := ContinuousLinearMap.fst ℝ X (ℝ × (X →L[ℝ] X))
  have hπ : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_fst_le q
  have hCenter := norm_iteratedFDeriv_clm_le_one π hπ p n hn
  have hRadius := norm_iteratedFDeriv_clm_le_one normalFrameRadiusProjection norm_normalFrameRadiusProjection_le_one p n hn
  change ‖iteratedFDeriv ℝ n (fun q : NormalFrameParameter => (q.1,(q.2.1,normalFrameNormalizedLinear g q))) p‖ ≤ _
  rw [iteratedFDeriv_prodMk (f:=fun q : NormalFrameParameter => q.1)
      (g:=fun q => (q.2.1,normalFrameNormalizedLinear g q)) contDiffAt_fst
      (contDiffAt_snd.fst.prodMk hFrameSmooth) (i:=n) (by simp),
    iteratedFDeriv_prodMk contDiffAt_snd.fst hFrameSmooth (i:=n) (by simp),
    ContinuousMultilinearMap.opNorm_prod,ContinuousMultilinearMap.opNorm_prod]
  exact max_le (hCenter.trans hOne) (max_le (hRadius.trans hOne) (hFrame g g₁ g₂ e h p hp he n hnN))

end ShrinkingSpheres
