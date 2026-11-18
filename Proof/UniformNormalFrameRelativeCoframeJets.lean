import Proof.NormalFrameRelativeCoframeGeometry
import Proof.MatrixCoframeHigherJetBounds
import Proof.UniformNormalFrameNormalizationJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Genuine normalized coframe multipliers have every prescribed joint jet
    from finite metric budgets, uniformly over arbitrary admitted frames. -/
theorem uniform_normalFrameRelativeCoframe_higher_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ v : X,∀ j : I,ContDiffAt ℝ ∞ (normalFrameRelativeCoframeValue g v j) ((y,L),0) ∧
        ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameRelativeCoframeValue g v j) ((y,L),0)‖ ≤ C*‖v‖ := by
  obtain ⟨CN,hCN,hNormalize⟩ := uniform_normalFrame_normalization_jet_bounds hΩ K M hK N hNm
  let BG := backgroundAllMetricJetBudget M
  let D := (N.factorial:ℝ)*BG+1
  let CG := (N.factorial:ℝ)*BG
  let FRaw := (N.factorial:ℝ)*CN*D^N
  let CF := (N.factorial:ℝ)*FRaw
  let C := 1+9*2^N*CG*CF
  have hBG : 0 ≤ BG := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  have hCG : 0 ≤ CG := by dsimp only [CG];positivity
  have hD : 1 ≤ D := by dsimp only [D];linarith only [hCG]
  have hFRaw : 0 ≤ FRaw := by dsimp only [FRaw];positivity
  have hCF : 0 ≤ CF := by dsimp only [CF];positivity
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (9:ℝ)*2^N*CG*CF := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e h y hy L he v j
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  let G := g ∘ normalFrameRelativeCenterL
  let Frame := normalFrameNormalizedLinear g ∘ normalFrameRelativeZeroL
  have hg : ContDiffAt ℝ ∞ g y := contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k =>
    (h.1.1 i k).contDiffAt (hΩ.mem_nhds hy)))
  have hRawFrame : ContDiffAt ℝ ∞ (normalFrameNormalizedLinear g) (y,(0,L)) :=
    (contDiffAt_normalization_at_orthonormal g (y,(0,L))
      (fun i k => (h.1.1 i k).contDiffAt (hΩ.mem_nhds hy)) he).snd.snd
  have hFrame : ContDiffAt ℝ ∞ Frame p0 :=
    hRawFrame.comp (f:=normalFrameRelativeZeroL) p0 normalFrameRelativeZeroL.contDiff.contDiffAt
  have hG : ContDiffAt ℝ ∞ G p0 :=
    hg.comp (f:=normalFrameRelativeCenterL) p0 normalFrameRelativeCenterL.contDiff.contDiffAt
  have hRawJets (n : ℕ) (hn : n ≤ N) :
      ‖iteratedFDeriv ℝ n (normalFrameNormalizedLinear g) (y,(0,L))‖ ≤ FRaw := by
    have hh := hNormalize g g₁ g₂ e h (y,(0,L)) hy he n hn
    apply hh.trans
    change (n.factorial:ℝ)*CN*D^n ≤ (N.factorial:ℝ)*CN*D^N
    gcongr
  have hFrameJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n Frame p0‖ ≤ CF := by
    have hh := iteratedFDeriv_comp_common_bound normalFrameRelativeZeroL (normalFrameNormalizedLinear g) p0
      normalFrameRelativeZeroL.contDiff.contDiffAt hRawFrame N FRaw 1 hFRaw le_rfl hRawJets
      (fun k hk _ => norm_iteratedFDeriv_clm_le_one normalFrameRelativeZeroL norm_normalFrameRelativeZeroL_le_one _ k hk) n hn
    simpa only [one_pow,mul_one] using hh
  have hMetricJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n g y‖ ≤ BG :=
    (h.reference_matrix_jet_bound hΩ ⟨n,by omega⟩ hy).trans (abs_metricJet_le_all_budget M ⟨n,by omega⟩)
  have hGJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n G p0‖ ≤ CG := by
    have hh := iteratedFDeriv_comp_common_bound normalFrameRelativeCenterL g p0
      normalFrameRelativeCenterL.contDiff.contDiffAt hg N BG 1 hBG le_rfl hMetricJets
      (fun k hk _ => norm_iteratedFDeriv_clm_le_one normalFrameRelativeCenterL norm_normalFrameRelativeCenterL_le_one _ k hk) n hn
    simpa only [one_pow,mul_one] using hh
  have hScalar : ContDiffAt ℝ ∞ (fun p => ∑ i : I,∑ k : I,G p i k*v i*(Frame p (axis j)) k) p0 :=
    ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ =>
      (((matrixEntryL i k).contDiff.contDiffAt.comp p0 hG).mul contDiffAt_const).mul
        ((frameAxisCoordinateL j k).contDiff.contDiffAt.comp p0 hFrame)))
  have hEq : normalFrameRelativeCoframeValue g v j =
      fun p => ∑ i : I,∑ k : I,G p i k*v i*(Frame p (axis j)) k := by
    funext p
    exact normalFrameRelativeCoframeValue_apply g v j p
  rw [hEq]
  refine ⟨hScalar,?_⟩
  intro n hn
  exact (norm_iteratedFDeriv_matrix_coframe_le G Frame p0 hG hFrame N CG CF hCG hCF hGJets hFrameJets v j n hn).trans
    (mul_le_mul_of_nonneg_right (by dsimp only [C];linarith) (norm_nonneg v))

end ShrinkingSpheres
