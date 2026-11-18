import Proof.NormalFrameRelativeParallelCenterError
import Proof.MetricPairFamilyHigherJetBounds
import Proof.NormalFrameRelativeCoframeGeometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def normalFrameRelativeCenterErrorWeight (g : MetricField) (E : X × X → X)
    (r : ℝ) (a : X) (j : I) (q : NormalFrameRelativeParameter × X) : ℝ :=
  metricPair g q.1.1.1 (normalFrameRelativeParallelCenterError g E r q a) (q.1.1.2 (axis j))

/-- Uniform mixed jets of the genuine nonconstant angular weights of the
    Jacobi center error, retaining the quadratic radius gain. -/
theorem uniform_normalFrameRelative_center_error_weight_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ a : X,∀ j : I,∀ z : X,‖z‖ ≤ Z →
      (∃ U : Set (NormalFrameRelativeParameter × X),IsOpen U ∧ (((y,L),0),z) ∈ U ∧
        ContDiffOn ℝ ∞ (normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j) U) ∧
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j)
        (((y,L),0),z)‖ ≤ C*‖a‖*(d.radius y)^2 := by
  obtain ⟨η,CG,hη,hη1,hCG,hError⟩ := uniform_normalFrameRelative_parallelCenter_error_joint_jets hY hΩ N hNm
    K ρ c₀ M Cj hK hρ Z hZ
  let BG := backgroundAllMetricJetBudget M
  let CM := (N.factorial:ℝ)*BG
  let C := 1+9*(2^N*(2^N*CM*CG)*K)
  have hBG : 0 ≤ BG := zero_le_one.trans (backgroundAllMetricJetBudget_ge_one M)
  have hCM : 0 ≤ CM := by dsimp only [CM];positivity
  have hCG0 : 0 ≤ CG := zero_le_one.trans hCG
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC : 1 ≤ C := by
    have hh : 0 ≤ 9*(2^N*(2^N*CM*CG)*K) := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he a j z hz
  let p0 : NormalFrameRelativeParameter × X := (((y,L),0),z)
  let H := normalFrameRelativeParallelCenterError d.γ d.expMap (d.radius y)
  let centerL := normalFrameRelativeCenterL.comp (ContinuousLinearMap.fst ℝ NormalFrameRelativeParameter X)
  let A := d.γ ∘ centerL
  let v := fun q => H q a
  let frameL : (NormalFrameRelativeParameter × X) →L[ℝ] (X →L[ℝ] X) :=
    (ContinuousLinearMap.snd ℝ X (X →L[ℝ] X)).comp
      ((ContinuousLinearMap.fst ℝ (X × (X →L[ℝ] X)) ℝ).comp
        (ContinuousLinearMap.fst ℝ NormalFrameRelativeParameter X))
  let W := (ContinuousLinearMap.apply ℝ X (axis j)).comp frameL
  obtain ⟨⟨U,hU,hMem,hHU⟩,hHJets⟩ := hError floor hf ε hε hSmall d hd y hy L he z hz
  have hCenter := hd.2.1.center_mem hy
  have hH : ContDiffAt ℝ ∞ H p0 := hHU.contDiffAt (hU.mem_nhds hMem)
  have hg : ContDiffAt ℝ ∞ d.γ y := contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k =>
    (hd.1.1.1 i k).contDiffAt (hΩ.mem_nhds hCenter)))
  have hA : ContDiffAt ℝ ∞ A p0 := hg.comp (f:=centerL) p0 centerL.contDiff.contDiffAt
  have hv : ContDiffAt ℝ ∞ v p0 := hH.clm_apply contDiffAt_const
  have hW : ContDiffAt ℝ ∞ W p0 := W.contDiff.contDiffAt
  let V := U ∩ centerL ⁻¹' Ω
  have hV : IsOpen V := hU.inter (hΩ.preimage centerL.continuous)
  have hMemV : p0 ∈ V := ⟨hMem,hCenter⟩
  have hScalar : ContDiffOn ℝ ∞ (normalFrameRelativeCenterErrorWeight d.γ d.expMap (d.radius y) a j) V := by
    intro q hq
    have hHq : ContDiffAt ℝ ∞ H q := hHU.contDiffAt (hU.mem_nhds hq.1)
    have hAq : ContDiffAt ℝ ∞ A q :=
      (contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun k =>
        (hd.1.1.1 i k).contDiffAt (hΩ.mem_nhds hq.2)))).comp (f:=centerL) q centerL.contDiff.contDiffAt
    have hvq : ContDiffAt ℝ ∞ v q := hHq.clm_apply contDiffAt_const
    have hs : ContDiffAt ℝ ∞ (fun p => ∑ i : I,∑ k : I,A p i k*v p i*(W p) k) q :=
      ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun k _ =>
        (((matrixEntryL i k).contDiff.contDiffAt.comp q hAq).mul
          ((EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp q hvq)).mul
          ((EuclideanSpace.proj (𝕜:=ℝ) k).contDiff.contDiffAt.comp q W.contDiff.contDiffAt)))
    exact hs.contDiffWithinAt
  refine ⟨⟨V,hV,hMemV,hScalar⟩,?_⟩
  have hCenterL : ‖centerL‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul norm_normalFrameRelativeCenterL_le_one
        (ContinuousLinearMap.norm_fst_le ℝ NormalFrameRelativeParameter X)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hMetricJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n d.γ y‖ ≤ BG :=
    (hd.1.reference_matrix_jet_bound hΩ ⟨n,by omega⟩ hCenter).trans
      (abs_metricJet_le_all_budget M ⟨n,by omega⟩)
  have hAJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n A p0‖ ≤ CM := by
    have hh := iteratedFDeriv_comp_common_bound centerL d.γ p0 centerL.contDiff.contDiffAt hg N BG 1 hBG le_rfl hMetricJets
      (fun k hk _ => norm_iteratedFDeriv_clm_le_one centerL hCenterL _ k hk) n hn
    simpa only [one_pow,mul_one] using hh
  let ev := ContinuousLinearMap.apply ℝ X a
  have hEv : ‖ev‖ ≤ ‖a‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro T
    exact (T.le_opNorm a).trans_eq (mul_comm _ _)
  have hvJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n v p0‖ ≤ ‖a‖*(CG*(d.radius y)^2) :=
    (norm_iteratedFDeriv_clm_comp_le ev H p0 hH n).trans
      (mul_le_mul hEv (hHJets n hn) (norm_nonneg _) (norm_nonneg _))
  have hWNorm : ‖W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1.1.2 (axis j)‖ ≤ 1*‖q‖
    calc
      _ ≤ ‖q.1.1.2‖*‖axis j‖ := q.1.1.2.le_opNorm _
      _ = ‖q.1.1.2‖ := by rw [norm_axis,mul_one]
      _ ≤ 1*‖q‖ := by simpa only [one_mul] using
        (norm_snd_le q.1.1).trans ((norm_fst_le q.1).trans (norm_fst_le q))
  let eL : Frame := fun _ i => L (axis i)
  have hLeq : frameVectorLinear eL y = L := by
    apply ContinuousLinearMap.ext
    intro b
    exact frameVector_linear_axes L y b
  have hL : ‖L‖ ≤ K := by rw [← hLeq];exact hd.1.1.norm_frameVectorLinear_le hK hCenter eL he
  have hWJets (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n W p0‖ ≤ K := by
    by_cases hn0 : n=0
    · subst n
      rw [norm_iteratedFDeriv_zero]
      change ‖L (axis j)‖ ≤ K
      exact (L.le_opNorm _).trans (by rw [norm_axis,mul_one];exact hL)
    · exact (norm_iteratedFDeriv_clm_le_one W hWNorm p0 n (by omega)).trans hK
  intro n hn
  have hh := norm_iteratedFDeriv_metricPair_families_le A v W p0 hA hv hW N CM
    (‖a‖*(CG*(d.radius y)^2)) K hCM (by positivity) hK0 hAJets hvJets hWJets n hn
  exact hh.trans (by
    calc
      _ = (9*(2^N*(2^N*CM*CG)*K))*‖a‖*(d.radius y)^2 := by ring
      _ ≤ C*‖a‖*(d.radius y)^2 := by gcongr;dsimp only [C];linarith)

end ShrinkingSpheres
