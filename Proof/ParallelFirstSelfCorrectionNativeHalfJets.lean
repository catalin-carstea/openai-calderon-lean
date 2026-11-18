import Proof.ParallelFirstSelfCorrectionNativeHalf
import Proof.ParallelFirstSelfCorrectionNativeInputs
import Proof.UniformNormalFrameScaledHorizontalJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME native strong-half correction has uniform joint three-jets. -/
theorem uniform_correction_native_half_scaled_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ b : X,
      SmoothFiniteJetBound (correctionNativeHalfFamily d (d.radius y) b ∘
        normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
        ((0,frameVectorLinear d.frame y),0) 3 (C*‖b‖) := by
  obtain ⟨η,Bq,Bc,Bt,hη,hη1,hBq,hBc,hBt,hInputs⟩ :=
    uniform_correction_native_scaled_inputs hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let CI := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let RI := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let CB := correctionBoundedJetBudget 3 Bq Bc Bt
  let C := 2^3*‖CI‖*(2^3*CB*‖RI‖)
  have hCB : 0 ≤ CB := by dsimp only [CB,correctionBoundedJetBudget];positivity
  refine ⟨η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy b
  obtain ⟨hq,hc,ht⟩ := hInputs floor hf ε hε hSmall d hd y hy b
  let Φ := normalFrameRelativeScaledParameter (beta d.γ d.radius y) y
  let p0 : NormalFrameRelativeParameter := ((0,frameVectorLinear d.frame y),0)
  have hB := correctionBoundedPacket_jet_bound
    (normalizedFirstCorrectionCovector d.γ d.g₁ ∘ Φ)
    (fun j => normalFrameRelativeCoframeValue d.γ b j ∘ Φ)
    (nativePhysicalFirstCorrectionScalar d (d.radius y) b ∘ Φ) p0 3
    Bq (Bc*‖b‖) (Bt*‖b‖) hq hc ht
  have hBudget : correctionBoundedJetBudget 3 Bq (Bc*‖b‖) (Bt*‖b‖)=CB*‖b‖ := by
    have hsum : (∑ j : I,2^3*(Bc*‖b‖)*‖coordinateMultiplierSobolevL 0 j‖)=
        (∑ j : I,2^3*Bc*‖coordinateMultiplierSobolevL 0 j‖)*‖b‖ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    dsimp only [CB,correctionBoundedJetBudget]
    rw [hsum]
    ring
  rw [hBudget] at hB
  have hHalf := (SmoothFiniteJetBound.constant CI p0 3).comp
    (hB.comp (SmoothFiniteJetBound.constant RI p0 3))
  have hBudgetHalf : 2^3*‖CI‖*(2^3*(CB*‖b‖)*‖RI‖)=C*‖b‖ := by dsimp only [C];ring
  rw [hBudgetHalf] at hHalf
  exact hHalf

/-- Ordered native horizontal jets of the same strong-half family, through
second order, obey the original beta scaling with no frame-derivative budget. -/
theorem uniform_correction_native_half_horizontal_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ b : X,
      let G := correctionNativeHalfFamily d (d.radius y) b
      let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      ‖G p‖ ≤ C*‖b‖ ∧
      (∀ a : X,‖a‖ ≤ 1 →
        ‖fderiv ℝ G p (normalFrameRelativeHorizontalField d.γ d.radius a p)‖ ≤
          C*‖b‖*beta d.γ d.radius y) ∧
      ∀ a c : X,‖a‖ ≤ 1 → ‖c‖ ≤ 1 →
        ‖fderiv ℝ (fun q => fderiv ℝ G q (normalFrameRelativeHorizontalField d.γ d.radius a q)) p
          (normalFrameRelativeHorizontalField d.γ d.radius c p)‖ ≤ C*‖b‖*(beta d.γ d.radius y)^2 := by
  obtain ⟨η,C,hη,hη1,hC,hNative⟩ :=
    uniform_correction_native_half_scaled_three_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CH,hCH,hHorizontal⟩ :=
    uniform_normalFrame_horizontal_from_scaled_three_jets hY hΩ hSub (by omega) K M Cj hK
  refine ⟨η,CH*C,hη,hη1,mul_nonneg (zero_le_one.trans hCH) hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy b
  let G := correctionNativeHalfFamily d (d.radius y) b
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hBound := hNative floor hf ε hε hSmall d hd y hy b
  have hHorizontalG := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) G (C*‖b‖) hBound
  refine ⟨?_,?_,?_⟩
  · have hh := hHorizontalG (fun _ => 0) (fun _ => by simp) 0 (by norm_num)
    simpa only [orderedDirectionalFamily,pow_zero,mul_one,mul_assoc] using hh
  · intro a ha
    have hh := hHorizontalG (fun _ => a) (fun _ => ha) 1 (by norm_num)
    simpa only [orderedDirectionalFamily,pow_one,mul_assoc] using hh
  · intro a c ha hc
    let directions : ℕ → X := fun j => if j=0 then a else c
    have hDirections (j : ℕ) : ‖directions j‖ ≤ 1 := by
      dsimp only [directions]
      split_ifs <;> assumption
    have hh := hHorizontalG directions hDirections 2 (by norm_num)
    simpa [orderedDirectionalFamily,directions,G,p,mul_assoc] using hh

end ShrinkingSpheres.ParallelEnergy
