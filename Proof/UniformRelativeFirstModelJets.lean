import Proof.RelativeFirstModelJetBound
import Proof.NormalFrameRelativeGeometry
import Proof.UniformNormalFrameRadialCoefficientHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

theorem uniform_normalFrameRelativeFirstModel_joint_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+3 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (normalFrameRelativeFirstModel d.γ d.g₁) (((y,L),0),z)‖ ≤ C := by
  obtain ⟨ηA,B,hηA,hηA1,hB,hCoeff⟩ := uniform_normalFrameRadialCoefficient_higher_jet_bounds
    hY hΩ (N+1) (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hηD1,hDomains⟩ := uniform_orthonormal_coefficient_smooth_domains (Y:=Y)
    hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  let C0 : ℝ := 2^N*((N.factorial:ℝ)*B)
  let C : ℝ := 1+(N.factorial:ℝ)*C0
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC0 : 0 ≤ C0 := by dsimp only [C0];positivity
  have hC : 1 ≤ C := by
    have hProduct : 0 ≤ (N.factorial:ℝ)*C0 := by positivity
    dsimp only [C]
    linarith only [hProduct]
  refine ⟨min ηA ηD,C,lt_min hηA hηD,(min_le_left _ _).trans hηA1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz n hn
  let p : NormalFrameSpatialParameter := ((y,L),z)
  let F := normalFrameRadialCoefficient d.γ d.g₁ d.expMap
  let first := normalFrameRadialFirstModel d.γ d.g₁
  let G : NormalFrameSpatialParameter × ℝ → Mat := fun q => (1+q.2) • first q.1
  have hRpos := (hd.2.2.2.2.1.2 y hy).1
  have h0 : |(0:ℝ)| ≤ d.radius y := by simpa only [abs_zero] using hRpos.le
  obtain ⟨W,hW,hMem,hA⟩ := hDomains floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd
    y hy L he z hz 0 h0
  let U := normalFrameRadialReorderL ⁻¹' W
  have hU : IsOpen U := hW.preimage normalFrameRadialReorderL.continuous
  have hHere : (p,0) ∈ U := hMem
  have hF : ContDiffOn ℝ ∞ F U :=
    hA.comp normalFrameRadialReorderL.contDiff.contDiffOn (fun q hq => hq)
  have hPositive : (y,(0,L)) ∈ normalFramePositiveDomain Ω :=
    normalFramePositiveDomain_mem_of_orthonormal d.γ (y,(0,L)) (hd.2.1.center_mem hy) he
  obtain ⟨hZero,hFirst⟩ := hd.1.normalFrameRadial_affine_model_germs hY hΩ
    (zero_lt_one.trans_le hK) hd.2.1 p hy hPositive hU hHere hF
  have hFirstSmooth : ContDiffAt ℝ ∞ first p :=
    (contDiffAt_radialFirst_left_slice_of_open F hU hF p 0 hHere).congr_of_eventuallyEq hFirst.symm
  have hG : ContDiffAt ℝ ∞ G (p,0) :=
    (contDiffAt_const.add contDiffAt_snd).smul
      (hFirstSmooth.comp (f:=fun q : NormalFrameSpatialParameter × ℝ => q.1) (p,0) contDiffAt_fst)
  have hRaw (j : ℕ) (hj : j ≤ N+1) : ‖iteratedFDeriv ℝ j F (p,0)‖ ≤ B :=
    hCoeff floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he z hz 0 h0 j hj
  have hOuter (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j G (p,0)‖ ≤ C0 :=
    norm_iteratedFDeriv_relative_first_model_le F first hU hF p hHere hFirst N B hB0 hRaw j hj
  have hh := iteratedFDeriv_comp_common_bound normalFrameRelativeReorderL G (((y,L),0),z)
    normalFrameRelativeReorderL.contDiff.contDiffAt hG N C0 1 hC0 le_rfl hOuter
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one normalFrameRelativeReorderL
      norm_normalFrameRelativeReorderL_le_one _ j hj) n hn
  simp only [one_pow,mul_one] at hh
  exact hh.trans (by dsimp only [C];linarith)

end ShrinkingSpheres
