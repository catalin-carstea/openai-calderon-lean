import Proof.NativeFirstCorrectionScaledInputs
import Proof.NativeFirstCorrectionRotationGraph
import Proof.NormalFrameRelativeCoefficientJetFamily
import Proof.ScalarFirstCovectorHigherJets
import Proof.UniformNormalFrameRelativeCoframeJets
import Proof.UniformScaledLogCovectorThreeJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- Uniform native scalar inputs, retained before their bounded operator assembly. -/
theorem uniform_correction_native_scaled_inputs {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Bq Bc Bt : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ Bq ∧ 0 ≤ Bc ∧ 0 ≤ Bt ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ b : X,
      let β := beta d.γ d.radius y
      let Φ := normalFrameRelativeScaledParameter β y
      let p0 : NormalFrameRelativeParameter := ((0,frameVectorLinear d.frame y),0)
      SmoothFiniteJetBound (normalizedFirstCorrectionCovector d.γ d.g₁ ∘ Φ) p0 3 Bq ∧
      (∀ j : I,SmoothFiniteJetBound (normalFrameRelativeCoframeValue d.γ b j ∘ Φ) p0 3 (Bc*‖b‖)) ∧
      SmoothFiniteJetBound (nativePhysicalFirstCorrectionScalar d (d.radius y) b ∘ Φ) p0 3 (Bt*‖b‖) := by
  obtain ⟨η,CQ,hη,hη1,hCQ,hFamily⟩ := uniform_normalFrameRelativeCoefficient_jet_family
    hY hΩ 4 (by omega) K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨BR,hBR,hReciprocal⟩ := exists_relative_inverse_radius_factor_jet_bound 3
  obtain ⟨BC,hBC,hCoframe⟩ := uniform_normalFrameRelativeCoframe_higher_jets hΩ 3 (by omega) K M hK
  obtain ⟨BL,hBL,hLog⟩ := uniform_normalFrame_scaled_log_covector_three_jets
    hY hΩ hSub (by omega) K M Cj hK
  let BQ := 6*(2^3*BR*CQ)
  have hBR0 := zero_le_one.trans hBR
  have hCQ0 := zero_le_one.trans hCQ
  have hBC0 := zero_le_one.trans hBC
  have hBL0 := zero_le_one.trans hBL
  have hBQ : 0 ≤ BQ := by dsimp only [BQ];positivity
  refine ⟨η,BQ,6*BC,8*BL,hη,hη1,hBQ,by positivity,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy b
  let r := d.radius y
  let β := beta d.γ d.radius y
  let L := frameVectorLinear d.frame y
  let p1 : NormalFrameRelativeParameter := ((y,L),0)
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  let Φ := normalFrameRelativeScaledParameter β y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrβ : r*β ≤ 1 := by
    have hSmallR : r*β^2 ≤ ε := (hd.2.2.2.2.2 y hy).2
    have hPower : β ≤ β^2 := by nlinarith only [hβ]
    exact ((mul_le_mul_of_nonneg_left hPower hr.le).trans hSmallR).trans (hSmall.trans hη1)
  have he (i j : I) : metricPair d.γ y (L (axis i)) (L (axis j))=if i=j then 1 else 0 := by
    simpa only [L,frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  obtain ⟨q⟩ := hFamily floor hf ε hε hSmall d hd y hy L he 0 (by simpa using hr.le)
  have hRelative : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁) p1 3 CQ :=
    ⟨hCQ0,q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds q.pointMem),
      fun n hn => q.firstCovectorJets (by norm_num) n hn⟩
  obtain ⟨hRS,hRJ⟩ := hReciprocal y L
  have hR : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor p1 3 BR := ⟨hBR0,hRS,hRJ⟩
  have hp1 : p1 ∈ normalFrameRelativePositiveDomain Ω :=
    normalFramePositiveDomain_mem_of_orthonormal d.γ _ (hSub hy) he
  have hNormalizedSmooth := (hd.1.normalizedFirstCorrectionCovector_smooth hΩ
    (zero_lt_one.trans_le hK)).contDiffAt ((isOpen_normalFrameRelativePositiveDomain hΩ).mem_nhds hp1)
  have hNormalizedRaw := normalizedFirstCorrectionCovector_jet_bound d.γ d.g₁ y L 3 CQ BR
    hRelative hR hNormalizedSmooth
  have hNormalized : SmoothFiniteJetBound (normalizedFirstCorrectionCovector d.γ d.g₁ ∘ Φ) p0 3 BQ :=
    normalFrame_scaled_parameter_three_jet_bound β hβ y L hNormalizedRaw
  have hCoframeScaled (j : I) : SmoothFiniteJetBound (normalFrameRelativeCoframeValue d.γ b j ∘ Φ)
      p0 3 ((6*BC)*‖b‖) := by
    obtain ⟨hS,hJ⟩ := hCoframe d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) L he b j
    have hRaw : SmoothFiniteJetBound (normalFrameRelativeCoframeValue d.γ b j) p1 3 (BC*‖b‖) :=
      ⟨mul_nonneg hBC0 (norm_nonneg _),hS,hJ⟩
    simpa only [mul_assoc] using normalFrame_scaled_parameter_three_jet_bound β hβ y L hRaw
  have hLogBound := hLog d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy L
  have hScalar : SmoothFiniteJetBound (nativePhysicalFirstCorrectionScalar d r b ∘ Φ) p0 3 ((8*BL)*‖b‖) :=
    nativePhysicalFirstCorrectionScalar_scaled_three_jets d r β y b L BL hr.le hβ hrβ hLogBound
  exact ⟨hNormalized,hCoframeScaled,hScalar⟩

end ShrinkingSpheres.ParallelEnergy
