import Proof.UniformNativeFirstCorrectionThreeJets
import Proof.PhysicalFirstCorrectionNativeCovariant
import Proof.UniformNormalFrameScaledHorizontalJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual bounded geometric correction and one explicitly fixed smooth
first covariant family have genuine second covariant graphs and common
zero/first/second bounds. No derivative budget for the frame is assumed. -/
theorem uniform_physical_first_correction_coarse_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b : X,
      ContDiffOn ℝ ∞ (physicalFirstCorrectionCoarseFamily d b) Y ∧
      ContDiffOn ℝ ∞ (physicalFirstCorrectionCovariantFamily d b) Y ∧
      ∀ y ∈ Y,
        (∀ a : X,CoarseCovariantRotationGraph d y a (physicalFirstCorrectionCoarseFamily d b)
          (physicalFirstCorrectionCovariantFamily d b y a)) ∧
        ‖physicalFirstCorrectionCoarseFamily d b y‖ ≤ C*‖b‖ ∧
        (∀ a : X,‖a‖ ≤ 1 → ‖physicalFirstCorrectionCovariantFamily d b y a‖ ≤ C*‖b‖*beta d.γ d.radius y) ∧
        ∀ a c : X,‖a‖ ≤ 1 → ‖c‖ ≤ 1 →
          ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
            CoarseCovariantRotationGraph d y c (fun x => physicalFirstCorrectionCovariantFamily d b x a) T ∧
            ‖T‖ ≤ C*‖b‖*(beta d.γ d.radius y)^2 := by
  obtain ⟨η,C,hη,hη1,hC,hNative⟩ :=
    uniform_native_first_correction_scaled_three_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CH,hCH,hHorizontal⟩ :=
    uniform_normalFrame_horizontal_from_scaled_three_jets hY hΩ hSub (by omega) K M Cj hK
  refine ⟨η,CH*C,hη,hη1,mul_nonneg (zero_le_one.trans hCH) hC,?_⟩
  intro floor hf ε hε hSmall d hd b
  have hK0 := zero_lt_one.trans_le hK
  have hH : ContDiffOn ℝ ∞ (physicalFirstCorrectionCoarseFamily d b) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK0 0 b).clm_comp contDiffOn_const
  have hS := hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK0 b
  refine ⟨hH,hS.1,?_⟩
  intro y hy
  let F := nativePhysicalFirstCorrectionFamily d (d.radius y) b
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hFields := hNative floor hf ε hε hSmall d hd y hy b
  have hBound := hFields.operator
  have hFam : (fun q => (nativePhysicalFirstCorrectionAngularFields d (d.radius y) b
      (normalFrameRelativeScaledParameter (beta d.γ d.radius y) y q)).operator)=
      F ∘ normalFrameRelativeScaledParameter (beta d.γ d.radius y) y := by
    funext q
    exact nativePhysicalFirstCorrectionAngularFields_operator d (d.radius y) b _
  change SmoothFiniteJetBound (fun q => (nativePhysicalFirstCorrectionAngularFields d (d.radius y) b
    (normalFrameRelativeScaledParameter (beta d.γ d.radius y) y q)).operator) _ 3 _ at hBound
  rw [hFam] at hBound
  have hHorizontalF := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev 1 →L[ℝ] SphereSobolev 0) F (C*‖b‖) hBound
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hEq : physicalFirstCorrectionCoarseFamily d b y=F p := by
    simpa only [normalFrameRelativeActualParameter_point d y hr0] using
      (hd.nativePhysicalFirstCorrectionFamily_actual_germ hY hΩ hSub hK0 (d.radius y) hr0 hy b).eq_of_nhds
  refine ⟨hS.2 y hy,?_,?_,?_⟩
  · rw [hEq]
    have hh := hHorizontalF (fun _ => 0) (fun _ => by simp) 0 (by norm_num)
    simpa only [orderedDirectionalFamily,pow_zero,mul_one,mul_assoc] using hh
  · intro a ha
    rw [hd.physicalFirstCorrectionCovariantFamily_eq_native_horizontal hY hΩ hSub hK0 hy a b]
    have hh := hHorizontalF (fun _ => a) (fun _ => ha) 1 (by norm_num)
    simpa only [orderedDirectionalFamily,pow_one,mul_assoc] using hh
  · intro a c ha hc
    let T := fderiv ℝ (fun q => fderiv ℝ F q (normalFrameRelativeHorizontalField d.γ d.radius a q)) p
      (normalFrameRelativeHorizontalField d.γ d.radius c p)
    refine ⟨T,hd.physicalFirstCorrection_second_covariant_graph hY hΩ hSub hK0 hy a c b,?_⟩
    let directions : ℕ → X := fun j => if j=0 then a else c
    have hDirections (j : ℕ) : ‖directions j‖ ≤ 1 := by
      dsimp only [directions]
      split_ifs <;> assumption
    have hh := hHorizontalF directions hDirections 2 (by norm_num)
    simpa [orderedDirectionalFamily,directions,T,p,mul_assoc] using hh

end ShrinkingSpheres
