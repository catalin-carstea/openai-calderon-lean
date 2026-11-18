import Proof.NormalizedRelativeAngularCurve
import Proof.UniformNormalFrameRelativeCoframeJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Linear insertion of the rotation tangent of a normalized frame. -/
def relativeAngularTangentFromFrameL (i j : I) : (X →L[ℝ] X) →L[ℝ] NormalFrameRelativeParameter :=
  (ContinuousLinearMap.inl ℝ (X × (X →L[ℝ] X)) ℝ).comp
    ((ContinuousLinearMap.inr ℝ X (X →L[ℝ] X)).comp
      ((ContinuousLinearMap.compL ℝ X X X).flip (rotationVectorL i j)))

lemma norm_relativeAngularTangentFromFrameL_le_two (i j : I) :
    ‖relativeAngularTangentFromFrameL i j‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro L
  change ‖(((0:X),L.comp (rotationVectorL i j)),(0:ℝ))‖ ≤ 2*‖L‖
  simp only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _),max_eq_left (norm_nonneg _)]
  exact (ContinuousLinearMap.opNorm_comp_le L (rotationVectorL i j)).trans
    ((mul_le_mul_of_nonneg_left (norm_rotationVectorL_le_two i j) (norm_nonneg L)).trans_eq (by ring))

/-- Uniform finite jets of the actual relative normalization and its
    normalized angular tangents, including the zeroth tangent jet. -/
theorem uniform_relative_angular_normalization_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ D : ℝ,1 ≤ D ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ContDiffAt ℝ ∞ (normalFrameRelativeNormalization g) ((y,L),0) ∧
      (∀ n : ℕ,1 ≤ n → n ≤ N →
        ‖iteratedFDeriv ℝ n (normalFrameRelativeNormalization g) ((y,L),0)‖ ≤ D) ∧
      ∀ i j : I,ContDiffAt ℝ ∞ (fun p => normalFrameRelativeAngularTangent g p i j) ((y,L),0) ∧
        ∀ n : ℕ,n ≤ N →
          ‖iteratedFDeriv ℝ n (fun p => normalFrameRelativeAngularTangent g p i j) ((y,L),0)‖ ≤ 2*D := by
  obtain ⟨CN,hCN,hNormalize⟩ := uniform_normalFrame_normalization_jet_bounds hΩ K M hK N hNm
  let BG := backgroundAllMetricJetBudget M
  let D0 := (N.factorial:ℝ)*BG+1
  let FRaw := (N.factorial:ℝ)*CN*D0^N
  let CF := (N.factorial:ℝ)*FRaw
  let D := 1+CF
  have hBG : 0 ≤ BG := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  have hD0 : 1 ≤ D0 := by
    have hh : 0 ≤ (N.factorial:ℝ)*BG := by positivity
    dsimp only [D0]
    linarith only [hh]
  have hFRaw : 0 ≤ FRaw := by dsimp only [FRaw];positivity
  have hCF : 0 ≤ CF := by dsimp only [CF];positivity
  have hD : 1 ≤ D := by dsimp only [D];linarith only [hCF]
  have hCFD : CF ≤ D := by dsimp only [D];linarith
  refine ⟨D,hD,?_⟩
  intro g g₁ g₂ e h y hy L he
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  let Frame := normalFrameNormalizedLinear g ∘ normalFrameRelativeZeroL
  have hRawFrame : ContDiffAt ℝ ∞ (normalFrameNormalizedLinear g) (y,(0,L)) :=
    (contDiffAt_normalization_at_orthonormal g (y,(0,L))
      (fun i k => (h.1.1 i k).contDiffAt (hΩ.mem_nhds hy)) he).snd.snd
  have hFrame : ContDiffAt ℝ ∞ Frame p0 :=
    hRawFrame.comp (f:=normalFrameRelativeZeroL) p0 normalFrameRelativeZeroL.contDiff.contDiffAt
  have hRawJets (n : ℕ) (hn : n ≤ N) :
      ‖iteratedFDeriv ℝ n (normalFrameNormalizedLinear g) (y,(0,L))‖ ≤ FRaw := by
    have hh := hNormalize g g₁ g₂ e h (y,(0,L)) hy he n hn
    apply hh.trans
    change (n.factorial:ℝ)*CN*D0^n ≤ (N.factorial:ℝ)*CN*D0^N
    gcongr
  have hFrameJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n Frame p0‖ ≤ CF := by
    have hh := iteratedFDeriv_comp_common_bound normalFrameRelativeZeroL (normalFrameNormalizedLinear g) p0
      normalFrameRelativeZeroL.contDiff.contDiffAt hRawFrame N FRaw 1 hFRaw le_rfl hRawJets
      (fun k hk _ => norm_iteratedFDeriv_clm_le_one normalFrameRelativeZeroL norm_normalFrameRelativeZeroL_le_one _ k hk) n hn
    simpa only [one_pow,mul_one] using hh
  let π := normalFrameRelativeCenterL
  let τ : NormalFrameRelativeParameter →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ _ _
  have hπ : ‖π‖ ≤ 1 := norm_normalFrameRelativeCenterL_le_one
  have hτ : ‖τ‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ _ _
  have hQ : ContDiffAt ℝ ∞ (normalFrameRelativeNormalization g) p0 :=
    (π.contDiff.contDiffAt.prodMk hFrame).prodMk τ.contDiff.contDiffAt
  refine ⟨hQ,?_,?_⟩
  · intro n hn hnN
    change ‖iteratedFDeriv ℝ n (fun q => ((π q,Frame q),τ q)) p0‖ ≤ D
    rw [iteratedFDeriv_prodMk (π.contDiff.contDiffAt.prodMk hFrame) τ.contDiff.contDiffAt (i:=n) (by simp),
      iteratedFDeriv_prodMk π.contDiff.contDiffAt hFrame (i:=n) (by simp),
      ContinuousMultilinearMap.opNorm_prod,ContinuousMultilinearMap.opNorm_prod]
    exact max_le (max_le ((norm_iteratedFDeriv_clm_le_one π hπ p0 n hn).trans hD)
      ((hFrameJets n hnN).trans hCFD)) ((norm_iteratedFDeriv_clm_le_one τ hτ p0 n hn).trans hD)
  · intro i j
    let A := relativeAngularTangentFromFrameL i j
    have hEq : (fun p => normalFrameRelativeAngularTangent g p i j) = A ∘ Frame := rfl
    rw [hEq]
    refine ⟨A.contDiff.contDiffAt.comp p0 hFrame,?_⟩
    intro n hn
    exact (norm_iteratedFDeriv_clm_comp_le A Frame p0 hFrame n).trans
      ((mul_le_mul (norm_relativeAngularTangentFromFrameL_le_two i j)
        ((hFrameJets n hn).trans hCFD) (norm_nonneg _) (by norm_num)).trans_eq (by ring))

end ShrinkingSpheres
