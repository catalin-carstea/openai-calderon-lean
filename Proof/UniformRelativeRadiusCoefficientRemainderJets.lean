import Proof.LocalDilatedAffineRemainderBound
import Proof.UniformNormalFrameRadialCoefficientHigherJets
import Proof.NormalFrameRadialAffineModelGerms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

/-- The actual coefficient remainder has a uniform quadratic gain in all
    mixed center/frame/spatial/relative-radius parameter directions. -/
theorem uniform_relative_radius_coefficient_remainder_parameter_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (n : ℕ) (hNm : n+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ r : ℝ,|r| ≤ d.radius y →
      ‖iteratedFDeriv ℝ n (fun q : NormalFrameSpatialParameter × ℝ =>
          normalFrameRadialRemainder d.γ d.g₁ d.expMap (q.1,(1+q.2)*r)) (((y,L),z),0)‖ ≤ C*r^2 := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨ηF,B,hηF,hηF1,hB,hCoeff⟩ := uniform_normalFrameRadialCoefficient_higher_jet_bounds hY hΩ
    (n+2) (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hηD1,hDomains⟩ := uniform_orthonormal_coefficient_smooth_domains (Y:=Y) hΩ
    (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨C,hC,hBound⟩ := exists_dilated_affine_residual_parameter_jet_bound
    (P:=NormalFrameSpatialParameter) (V:=Mat) n B (zero_le_one.trans hB)
  refine ⟨min ηF ηD,C,lt_min hηF hηD,(min_le_left _ _).trans hηF1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz r hr
  let F := normalFrameRadialCoefficient d.γ d.g₁ d.expMap
  let p : NormalFrameSpatialParameter := ((y,L),z)
  have hSmallF := hSmall.trans (min_le_left _ _)
  have hSmallD := hSmall.trans (min_le_right _ _)
  have hRpos := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hRpos.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hR1 : d.radius y ≤ 1 := hrε.trans (hSmallF.trans hηF1)
  have hLocal (t : ℝ) (ht : |t| ≤ d.radius y) :
      ∃ U : Set (NormalFrameSpatialParameter × ℝ),IsOpen U ∧ (p,t) ∈ U ∧ ContDiffOn ℝ ∞ F U := by
    obtain ⟨U,hU,hMem,hA⟩ := hDomains floor hf ε hε hSmallD d hd y hy L he z hz t ht
    refine ⟨normalFrameRadialReorderL ⁻¹' U,hU.preimage normalFrameRadialReorderL.continuous,hMem,?_⟩
    exact hA.comp normalFrameRadialReorderL.contDiff.contDiffOn (fun q hq => hq)
  have hFBound (t : ℝ) (ht : |t| ≤ d.radius y) (j : ℕ) (hj : j ≤ n+2) :
      ‖iteratedFDeriv ℝ j F (p,t)‖ ≤ B :=
    hCoeff floor hf ε hε hSmallF d hd y hy L he z hz t ht j hj
  have hAffine := hBound F p (d.radius y) hRpos.le hR1 hLocal hFBound r hr
  have h0 : |(0:ℝ)| ≤ d.radius y := by simpa only [abs_zero] using hRpos.le
  obtain ⟨U0,hU0,hMem0,hF0⟩ := hLocal 0 h0
  have hPositive : (y,(0,L)) ∈ normalFramePositiveDomain Ω :=
    normalFramePositiveDomain_mem_of_orthonormal d.γ (y,(0,L)) (hd.2.1.center_mem hy) he
  obtain ⟨hZero,hFirst⟩ := hd.1.normalFrameRadial_affine_model_germs hY hΩ hKpos hd.2.1 p hy
    hPositive hU0 hMem0 hF0
  have hZeroQ : (fun q : NormalFrameSpatialParameter × ℝ => F (q.1,0)) =ᶠ[𝓝 (p,0)] (fun _ => (1:Mat)) :=
    hZero.comp_tendsto continuousAt_fst.tendsto
  have hFirstQ : (fun q : NormalFrameSpatialParameter × ℝ => radialFirstDerivative F (q.1,0)) =ᶠ[𝓝 (p,0)]
      (fun q => normalFrameRadialFirstModel d.γ d.g₁ q.1) := hFirst.comp_tendsto continuousAt_fst.tendsto
  have hGerm : (fun q : NormalFrameSpatialParameter × ℝ => normalFrameRadialRemainder d.γ d.g₁ d.expMap
      (q.1,(1+q.2)*r)) =ᶠ[𝓝 (p,0)] (fun q => radialAffineResidual F (q.1,(1+q.2)*r)) := by
    filter_upwards [hZeroQ,hFirstQ] with q hq0 hq1
    rw [normalFrameRadialRemainder_apply]
    change F (q.1,(1+q.2)*r)-(1:Mat)-((1+q.2)*r) • normalFrameRadialFirstModel d.γ d.g₁ q.1 =
      F (q.1,(1+q.2)*r)-F (q.1,0)-((1+q.2)*r) • radialFirstDerivative F (q.1,0)
    rw [hq0,hq1]
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hAffine

end ShrinkingSpheres
