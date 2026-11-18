import Proof.UniformRelativeRemainderFiniteJets
import Proof.LocalRadialFirstJetBound
import Proof.NormalFrameRelativeJetInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

theorem uniform_normalFrameRelativeRemainder_joint_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ z : X,‖z‖ ≤ Z → ∀ r : ℝ,|r| ≤ d.radius y → ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (fun q : NormalFrameRelativeParameter × X =>
        normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r q-(1:Mat)-
          r • normalFrameRelativeFirstModel d.γ d.g₁ q) (((y,L),0),z)‖ ≤ C*r^2 := by
  obtain ⟨ηA,B,hηA,hηA1,hB,hRaw⟩ := uniform_relative_radius_coefficient_remainder_finite_jets
    hY hΩ N hNm K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηD,hηD,hηD1,hDomains⟩ := uniform_orthonormal_coefficient_smooth_domains (Y:=Y)
    hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  let C : ℝ := 1+(N.factorial:ℝ)*B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC : 1 ≤ C := by
    have hProduct : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [C]
    linarith only [hProduct]
  refine ⟨min ηA ηD,C,lt_min hηA hηD,(min_le_left _ _).trans hηA1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he z hz r hr n hn
  let p : NormalFrameSpatialParameter := ((y,L),z)
  let F := normalFrameRadialCoefficient d.γ d.g₁ d.expMap
  let first := normalFrameRadialFirstModel d.γ d.g₁
  let G : NormalFrameSpatialParameter × ℝ → Mat := fun q =>
    normalFrameRadialRemainder d.γ d.g₁ d.expMap (q.1,(1+q.2)*r)
  have hAt (t : ℝ) (ht : |t| ≤ d.radius y) :
      ∃ U : Set (NormalFrameSpatialParameter × ℝ),IsOpen U ∧ (p,t) ∈ U ∧ ContDiffOn ℝ ∞ F U := by
    obtain ⟨W,hW,hMem,hA⟩ := hDomains floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd
      y hy L he z hz t ht
    exact ⟨normalFrameRadialReorderL ⁻¹' W,hW.preimage normalFrameRadialReorderL.continuous,
      hMem,hA.comp normalFrameRadialReorderL.contDiff.contDiffOn (fun q hq => hq)⟩
  have hRpos := (hd.2.2.2.2.1.2 y hy).1
  have h0 : |(0:ℝ)| ≤ d.radius y := by simpa only [abs_zero] using hRpos.le
  obtain ⟨U0,hU0,hMem0,hF0⟩ := hAt 0 h0
  obtain ⟨Ur,hUr,hMemr,hFr⟩ := hAt r hr
  have hPositive : (y,(0,L)) ∈ normalFramePositiveDomain Ω :=
    normalFramePositiveDomain_mem_of_orthonormal d.γ (y,(0,L)) (hd.2.1.center_mem hy) he
  obtain ⟨hZero,hFirst⟩ := hd.1.normalFrameRadial_affine_model_germs hY hΩ
    (zero_lt_one.trans_le hK) hd.2.1 p hy hPositive hU0 hMem0 hF0
  have hFirstSmooth : ContDiffAt ℝ ∞ first p :=
    (contDiffAt_radialFirst_left_slice_of_open F hU0 hF0 p 0 hMem0).congr_of_eventuallyEq hFirst.symm
  have hInput : ContDiffAt ℝ ∞ (fun q : NormalFrameSpatialParameter × ℝ =>
      (q.1,(1+q.2)*r)) (p,0) :=
    contDiffAt_fst.prodMk ((contDiffAt_const.add contDiffAt_snd).mul contDiffAt_const)
  have hFAt : ContDiffAt ℝ ∞ F (p,r) := hFr.contDiffAt (hUr.mem_nhds hMemr)
  have hFInputAt : ContDiffAt ℝ ∞ F
      ((fun q : NormalFrameSpatialParameter × ℝ => (q.1,(1+q.2)*r)) (p,0)) := by
    simpa only [add_zero,one_mul] using hFAt
  have hFComp : ContDiffAt ℝ ∞ (fun q : NormalFrameSpatialParameter × ℝ => F (q.1,(1+q.2)*r)) (p,0) :=
    hFInputAt.comp (f:=fun q : NormalFrameSpatialParameter × ℝ => (q.1,(1+q.2)*r))
      (g:=F) (p,0) hInput
  have hG : ContDiffAt ℝ ∞ G (p,0) :=
    (hFComp.sub contDiffAt_const).sub
      (((contDiffAt_const.add contDiffAt_snd).mul contDiffAt_const).smul
        (hFirstSmooth.comp (f:=fun q : NormalFrameSpatialParameter × ℝ => q.1) (p,0) contDiffAt_fst))
  have hOuter (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j G (p,0)‖ ≤ B*r^2 :=
    hRaw floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy L he z hz r hr j hj
  have hh := iteratedFDeriv_comp_common_bound normalFrameRelativeReorderL G (((y,L),0),z)
    normalFrameRelativeReorderL.contDiff.contDiffAt hG N (B*r^2) 1 (by positivity) le_rfl hOuter
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one normalFrameRelativeReorderL
      norm_normalFrameRelativeReorderL_le_one _ j hj) n hn
  have hEq : (fun q : NormalFrameRelativeParameter × X =>
      normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r q-(1:Mat)-r • normalFrameRelativeFirstModel d.γ d.g₁ q) =
      G ∘ normalFrameRelativeReorderL := by
    funext q
    exact normalFrameRelativeCoefficient_affine_residual d.γ d.g₁ d.expMap r q
  rw [hEq]
  simp only [one_pow,mul_one] at hh
  exact hh.trans (by
    calc
      _ = ((N.factorial:ℝ)*B)*r^2 := by ring
      _ ≤ C*r^2 := mul_le_mul_of_nonneg_right (by dsimp only [C];linarith) (sq_nonneg r))

end ShrinkingSpheres
