import Proof.UniformNormalFrameRadialParallelCenterJets
import Proof.LocalDilatedAffineRemainderBound
import Proof.NormalFrameRelativeJetInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

/-- Every mixed parameter derivative of the actual Jacobi center error
    retains its quadratic radius gain. -/
theorem uniform_relative_parallelCenter_error_parameter_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (n : ℕ) (hNm : n+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ r : ℝ,|r| ≤ d.radius y →
      ‖iteratedFDeriv ℝ n (fun q : NormalFrameSpatialParameter × ℝ =>
        normalFrameRadialParallelCenter d.γ d.expMap (q.1,(1+q.2)*r)-ContinuousLinearMap.id ℝ X)
        (((y,L),z),0)‖ ≤ C*r^2 := by
  obtain ⟨η,B,hη,hη1,hB,hData⟩ := uniform_normalFrameRadialParallelCenter_higher_jet_data hY hΩ
    (n+2) (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨C,hC,hBound⟩ := exists_dilated_affine_residual_parameter_jet_bound
    (P:=NormalFrameSpatialParameter) (V:=X →L[ℝ] X) n B (zero_le_one.trans hB)
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz r hr
  let F := normalFrameRadialParallelCenter d.γ d.expMap
  let p : NormalFrameSpatialParameter := ((y,L),z)
  have hRpos := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hRpos.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hLocal (t : ℝ) (ht : |t| ≤ d.radius y) :
      ∃ U : Set (NormalFrameSpatialParameter × ℝ),IsOpen U ∧ (p,t) ∈ U ∧ ContDiffOn ℝ ∞ F U :=
    (hData floor hf ε hε hSmall d hd y hy L he z hz t ht).1
  have hFBound (t : ℝ) (ht : |t| ≤ d.radius y) (j : ℕ) (hj : j ≤ n+2) :
      ‖iteratedFDeriv ℝ j F (p,t)‖ ≤ B :=
    (hData floor hf ε hε hSmall d hd y hy L he z hz t ht).2 j hj
  have hAffine := hBound F p (d.radius y) hRpos.le (hrε.trans (hSmall.trans hη1)) hLocal hFBound r hr
  obtain ⟨U0,hU0,hMem0,hF0⟩ := hLocal 0 (by simpa only [abs_zero] using hRpos.le)
  obtain ⟨hZero,hFirst⟩ := hd.1.normalFrameRadialParallelCenter_zero_germs hY hΩ
    (zero_lt_one.trans_le hK) (by omega) hd.2.1
    (fun x hx => hd.normal_radius_continuousAt hY hx) p hy hU0 hMem0 hF0
  have hZeroQ := hZero.comp_tendsto (continuous_fst.continuousAt (x:=(p,(0:ℝ)))).tendsto
  have hFirstQ := hFirst.comp_tendsto (continuous_fst.continuousAt (x:=(p,(0:ℝ)))).tendsto
  have hGerm : (fun q : NormalFrameSpatialParameter × ℝ =>
      F (q.1,(1+q.2)*r)-ContinuousLinearMap.id ℝ X) =ᶠ[𝓝 (p,0)]
      (fun q => radialAffineResidual F (q.1,(1+q.2)*r)) := by
    filter_upwards [hZeroQ,hFirstQ] with q hq0 hq1
    change F (q.1,0) = ContinuousLinearMap.id ℝ X at hq0
    change radialFirstDerivative F (q.1,0) = 0 at hq1
    simp only [radialAffineResidual,hq0,hq1,smul_zero,sub_zero]
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hAffine

/-- A common threshold and budget for all lower orders of the same family. -/
theorem uniform_relative_parallelCenter_error_finite_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ r : ℝ,|r| ≤ d.radius y → ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (fun q : NormalFrameSpatialParameter × ℝ =>
        normalFrameRadialParallelCenter d.γ d.expMap (q.1,(1+q.2)*r)-ContinuousLinearMap.id ℝ X)
        (((y,L),z),0)‖ ≤ C*r^2 := by
  revert hNm
  induction N with
  | zero =>
    intro hNm
    obtain ⟨η,C,hη,hη1,hC,hBound⟩ := uniform_relative_parallelCenter_error_parameter_jets
      hY hΩ 0 hNm K ρ c₀ M Cj hK hρ Z hZ
    refine ⟨η,C,hη,hη1,hC,?_⟩
    intro floor hf ε hε hSmall d hd y hy L he z hz r hr n hn
    have hn0 : n=0 := by omega
    subst n
    exact hBound floor hf ε hε hSmall d hd y hy L he z hz r hr
  | succ N ih =>
    intro hNm
    obtain ⟨ηA,CA,hηA,hηA1,hCA,hBoundA⟩ := ih (by omega)
    obtain ⟨ηB,CB,hηB,hηB1,hCB,hBoundB⟩ := uniform_relative_parallelCenter_error_parameter_jets
      hY hΩ (N+1) hNm K ρ c₀ M Cj hK hρ Z hZ
    refine ⟨min ηA ηB,max CA CB,lt_min hηA hηB,(min_le_left _ _).trans hηA1,
      hCA.trans (le_max_left _ _),?_⟩
    intro floor hf ε hε hSmall d hd y hy L he z hz r hr n hn
    by_cases hnN : n ≤ N
    · exact (hBoundA floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he z hz r hr n hnN).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg r))
    · have hnEq : n=N+1 := by omega
      subst n
      exact (hBoundB floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy L he z hz r hr).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg r))

end ShrinkingSpheres
