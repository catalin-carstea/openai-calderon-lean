import Proof.NormalFrameScaledFiniteJetBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- Scaled jets through any order at most three give true horizontal derivatives,
    with a constant independent of the smooth frame derivatives. -/
theorem uniform_normalFrame_horizontal_from_scaled_finite_jets {Y Ω : Set X}
    (N : ℕ) (hN : N ≤ 3) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 3 ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ CH : ℝ,1 ≤ CH ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ floor c₀,1 ≤ floor → Profile Y d.γ d.frame d.radius floor c₀ Cj → ∀ y ∈ Y,
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E],
      ∀ (F : NormalFrameRelativeParameter → E) (B : ℝ),
      SmoothFiniteJetBound (F ∘ normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
        ((0,frameVectorLinear d.frame y),0) N B →
      ∀ a : ℕ → X,(∀ j,‖a j‖ ≤ 1) → ∀ n : ℕ,n ≤ N →
      ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n
        ((y,frameVectorLinear d.frame y),0)‖ ≤ CH*B*(beta d.γ d.radius y)^n := by
  obtain ⟨CG,Cl,hCG,hCl,hInput⟩ := uniform_normalFrame_scaled_horizontal_input_jets hY hΩ hSub hm K M Cj hK
  let D := 1+4*(CG*K+Cl)
  let CH := (8*D)^3
  have hCG0 := zero_le_one.trans hCG
  have hCl0 := zero_le_one.trans hCl
  have hK0 := zero_le_one.trans hK
  have hD : 1 ≤ D := by dsimp only [D];nlinarith only [mul_nonneg hCG0 hK0,hCl0]
  have hD0 := zero_le_one.trans hD
  have hBase : 1 ≤ (8:ℝ)*D := by linarith only [hD]
  refine ⟨CH,one_le_pow₀ hBase,?_⟩
  intro d hd floor c₀ hf hp y hy E _ _ F B hFs a ha n hn
  let β := beta d.γ d.radius y
  let L := frameVectorLinear d.frame y
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  let V := fun j => normalFrameRelativeScaledHorizontalField d.γ d.radius β y (a j)
  have hβ : 1 ≤ β := hf.trans (hp.2 y hy).2.1
  obtain ⟨hG,hl,hGJets,hlJets⟩ := hInput d hd floor c₀ hf hp y hy L
  have hV : ∀ j,ContDiffAt ℝ ∞ (V j) p0 := fun j =>
    contDiffAt_relativeHorizontalFieldOfFamilies _ _ (a j) p0 hG hl
  have he (i k : I) := hd.2.2.2.2.2.2.2 y (hSub hy) i k
  have hL : ‖L‖ ≤ K := hd.1.norm_frameVectorLinear_le hK (hSub hy) d.frame he
  have hVJets (j : ℕ) (_hj : j < N) (k : ℕ) (hk : k+1 ≤ N) : ‖iteratedFDeriv ℝ k (V j) p0‖ ≤ D := by
    have hh := norm_iteratedFDeriv_relativeHorizontalFieldOfFamilies_le
      (normalFrameScaledConnection d.γ β y) (normalFrameScaledLogCovector d.radius β y) (a j) 0 L
      hG hl 2 CG Cl K hCG0 hCl0 hK hL hGJets hlJets k (by omega)
    have hh' : ‖iteratedFDeriv ℝ k (V j) p0‖ ≤ D*‖a j‖ := by
      simpa only [V,p0,normalFrameRelativeScaledHorizontalField,show (2:ℝ)^2=4 by norm_num,D] using hh
    exact hh'.trans ((mul_le_mul_of_nonneg_left (ha j) hD0).trans_eq (mul_one _))
  have hOrder := ordered_normalFrame_horizontal_bound_of_scaled_finite_jets N d y a D B hD hβ F hFs hV hVJets n hn
  have hPow : (2:ℝ)^N ≤ 8 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN
    norm_num only [show (2:ℝ)^3=8 by norm_num] at hh
    exact hh
  have hND : (2:ℝ)^N*D ≤ 8*D := mul_le_mul_of_nonneg_right hPow hD0
  have hBudget : ((2:ℝ)^N*D)^N ≤ CH := by
    exact (pow_le_pow_left₀ (by positivity) hND N).trans (pow_le_pow_right₀ hBase hN)
  exact hOrder.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hBudget hFs.nonneg) (by positivity))
end ShrinkingSpheres
