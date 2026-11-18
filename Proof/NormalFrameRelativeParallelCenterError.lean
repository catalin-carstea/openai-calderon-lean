import Proof.UniformRelativeParallelCenterErrorJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalFrameRelativeParallelCenterError (g : MetricField) (E : X × X → X) (r : ℝ)
    (q : NormalFrameRelativeParameter × X) : X →L[ℝ] X :=
  normalFrameRadialParallelCenter g E (normalFrameRelativeRadiusInput r q)-ContinuousLinearMap.id ℝ X

/-- Genuine local smoothness and uniform finite joint quadratic jets for
    the same physical Jacobi center error in relative-radius coordinates. -/
theorem uniform_normalFrameRelative_parallelCenter_error_joint_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z →
      (∃ U : Set (NormalFrameRelativeParameter × X),IsOpen U ∧ (((y,L),0),z) ∈ U ∧
        ContDiffOn ℝ ∞ (normalFrameRelativeParallelCenterError d.γ d.expMap (d.radius y)) U) ∧
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (normalFrameRelativeParallelCenterError d.γ d.expMap (d.radius y))
        (((y,L),0),z)‖ ≤ C*(d.radius y)^2 := by
  obtain ⟨ηA,B,hηA,hηA1,hB,hRaw⟩ := uniform_relative_parallelCenter_error_finite_jets hY hΩ N hNm
    K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hDomains⟩ := uniform_normalFrameRadialParallelCenter_higher_jet_data hY hΩ
    0 (by omega) K ρ c₀ M Cj hK hρ Z hZ
  let C := 1+(N.factorial:ℝ)*B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨min ηA ηD,C,lt_min hηA hηD,(min_le_left _ _).trans hηA1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz
  let r := d.radius y
  let p : NormalFrameSpatialParameter := ((y,L),z)
  let F := normalFrameRadialParallelCenter d.γ d.expMap
  let G := fun q : NormalFrameSpatialParameter × ℝ => F (q.1,(1+q.2)*r)-ContinuousLinearMap.id ℝ X
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨U,hU,hMem,hF⟩ := (hDomains floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy L he z hz
    r (by simpa only [abs_of_pos hr] using (le_rfl : r ≤ d.radius y))).1
  have hInputMem : normalFrameRelativeRadiusInput r (((y,L),0),z) ∈ U := by
    simpa only [normalFrameRelativeRadiusInput,add_zero,one_mul] using hMem
  have hLocal : ∃ V : Set (NormalFrameRelativeParameter × X),IsOpen V ∧ (((y,L),0),z) ∈ V ∧
      ContDiffOn ℝ ∞ (normalFrameRelativeParallelCenterError d.γ d.expMap r) V := by
    refine ⟨normalFrameRelativeRadiusInput r ⁻¹' U,hU.preimage (contDiff_normalFrameRelativeRadiusInput r).continuous,
      hInputMem,?_⟩
    exact (hF.comp (contDiff_normalFrameRelativeRadiusInput r).contDiffOn (fun q hq => hq)).sub contDiffOn_const
  refine ⟨hLocal,?_⟩
  have hDil : ContDiffAt ℝ ∞ (fun q : NormalFrameSpatialParameter × ℝ => (q.1,(1+q.2)*r)) (p,0) :=
    contDiffAt_fst.prodMk ((contDiffAt_const.add contDiffAt_snd).mul contDiffAt_const)
  have hFAt : ContDiffAt ℝ ∞ F ((fun q : NormalFrameSpatialParameter × ℝ => (q.1,(1+q.2)*r)) (p,0)) := by
    simpa only [add_zero,one_mul] using hF.contDiffAt (hU.mem_nhds hMem)
  have hG : ContDiffAt ℝ ∞ G (p,0) :=
    (hFAt.comp (f:=fun q : NormalFrameSpatialParameter × ℝ => (q.1,(1+q.2)*r)) (g:=F) (p,0) hDil).sub contDiffAt_const
  have hOuter (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j G (p,0)‖ ≤ B*r^2 :=
    hRaw floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he z hz r
      (by simpa only [abs_of_pos hr] using (le_rfl : r ≤ d.radius y)) j hj
  intro n hn
  have hh := iteratedFDeriv_comp_common_bound normalFrameRelativeReorderL G (((y,L),0),z)
    normalFrameRelativeReorderL.contDiff.contDiffAt hG N (B*r^2) 1 (by positivity) le_rfl hOuter
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one normalFrameRelativeReorderL
      norm_normalFrameRelativeReorderL_le_one _ j hj) n hn
  change ‖iteratedFDeriv ℝ n (G ∘ normalFrameRelativeReorderL) (((y,L),0),z)‖ ≤ C*r^2
  simp only [one_pow,mul_one] at hh
  exact hh.trans (by
    calc
      _ = ((N.factorial:ℝ)*B)*r^2 := by ring
      _ ≤ C*r^2 := mul_le_mul_of_nonneg_right (by dsimp only [C];linarith) (sq_nonneg r))

end ShrinkingSpheres
