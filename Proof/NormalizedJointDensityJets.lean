import Proof.FirstDensityJetEnvelope
import Proof.UniformJointNormalMetricJets
import Proof.FourthBilinearVelocityBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

def normalizedJointFirstDensityFactor (g g₁ : MetricField) (E : X × X → X) (p : X × X) : ℝ :=
  firstMetricDensityFactor g g₁ (E p)/(firstMetricDensityFactor g g₁ p.1)

def backgroundNormalizedDensityJetBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) : ℝ :=
  288*(firstDensityJetEnvelope K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|)^2*
    (backgroundExpJetEnvelope hm K M)^3

/-- Actual normalized scalar density jets retain the same map and center
    scalar. Their constants depend only on frozen metric budgets. -/
theorem Background.normalized_joint_first_density_jets {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 5 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    (hR : ContinuousOn R Y) {y : X} (hy : y ∈ Y) (v : X)
    (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ContDiffAt ℝ ∞ (normalizedJointFirstDensityFactor g g₁ expMap) (y,v) ∧
    ∀ n,n ≤ 3 → ‖iteratedFDeriv ℝ n (normalizedJointFirstDensityFactor g g₁ expMap) (y,v)‖ ≤
      backgroundNormalizedDensityJetBudget hm K M := by
  let c := firstMetricDensityFactor g g₁
  let C := firstDensityJetEnvelope K |M ⟨1,by omega⟩| |M ⟨2,by omega⟩| |M ⟨3,by omega⟩|
  let V := backgroundExpJetEnvelope hm K M
  let π : (X × X) →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
  have hC : 0 ≤ C := by dsimp [C,firstDensityJetEnvelope,thirdFirstDensityBudget,thirdConformalDepthBudget];positivity
  have hV : 1 ≤ V := backgroundExpJetEnvelope_ge_one hm hK.le M
  have hx : expMap (y,v) ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy v hv.le (show (1:ℝ) ∈ Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv.le⟩))
  have hc := h.firstMetricDensityFactor_smooth hK
  have hci : ContDiffOn ℝ ∞ (fun z => (c z)⁻¹) Ω := hc.inv (fun z _ => (firstMetricDensityFactor_pos g g₁ z).ne')
  have hA : ContDiffAt ℝ ∞ (c ∘ expMap) (y,v) := (hc.contDiffAt (hΩ.mem_nhds hx)).comp (y,v) hE
  have hB : ContDiffAt ℝ ∞ ((fun z => (c z)⁻¹) ∘ π) (y,v) :=
    (hci.contDiffAt (hΩ.mem_nhds (hN.center_mem hy))).comp (y,v) π.contDiff.contDiffAt
  have hAJets := norm_iteratedFDeriv_comp_three_envelope expMap c (y,v) hE
    (hc.contDiffAt (hΩ.mem_nhds hx)) C V hC hV
    (h.firstMetricDensityFactors_jet_envelope hΩ hK (by omega) hx).1
    (fun n hn hn3 => h.normal_exp_jet_envelope hY hΩ hK hm hN hR hy v hv hv1 n hn (by omega))
  have hPi : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_fst_le q
  have hPiJets (n : ℕ) (hn : 1 ≤ n) (hn3 : n ≤ 3) : ‖iteratedFDeriv ℝ n (π : X × X → X) (y,v)‖ ≤ 1 := by
    interval_cases n
    · rw [norm_iteratedFDeriv_one,π.hasFDerivAt.fderiv];exact hPi
    · rw [norm_iteratedFDeriv_linear_higher π (y,v) 0];norm_num
    · rw [norm_iteratedFDeriv_linear_higher π (y,v) 1];norm_num
  have hBJets := norm_iteratedFDeriv_comp_three_envelope (π : X × X → X) (fun z => (c z)⁻¹) (y,v)
    π.contDiff.contDiffAt (hci.contDiffAt (hΩ.mem_nhds (hN.center_mem hy))) C 1 hC (by norm_num)
    (h.firstMetricDensityFactors_jet_envelope hΩ hK (by omega) (hN.center_mem hy)).2 hPiJets
  have hFun : normalizedJointFirstDensityFactor g g₁ expMap =
      fun p => (c ∘ expMap) p*(((fun z => (c z)⁻¹) ∘ π) p) := by funext p;exact div_eq_mul_inv _ _
  rw [hFun]
  refine ⟨hA.mul hB,?_⟩
  intro n hn
  have hb := norm_iteratedFDeriv_mul_envelope_at (c ∘ expMap) ((fun z => (c z)⁻¹) ∘ π) (y,v) n hA hB
    (6*C*V^3) (6*C) (by positivity) (by positivity)
    (fun k hk => hAJets k (hk.trans hn)) (fun k hk => by simpa only [one_pow,mul_one] using hBJets k (hk.trans hn))
  have hPow : (2:ℝ)^n ≤ 8 := (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn).trans_eq (by norm_num)
  exact hb.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPow (by positivity)) (by positivity)).trans_eq
    (by dsimp only [backgroundNormalizedDensityJetBudget,C,V];ring))

end ShrinkingSpheres
