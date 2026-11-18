import Proof.NativeFirstAdjointHigherError
import Proof.RelativeFirstAdjointErrorRescaling
import Proof.UniformScaledLogCovectorThreeJets
import Proof.UniformNormalFrameScaledHorizontalJets
import Proof.UniformNativeCenterHigherEndpoints
import Proof.UniformNativeHigherTaylorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both genuine endpoints of the SAME complete first-adjoint error have
    uniform radius-gained actual horizontal three-jets. The log-radius factor
    is estimated after beta rescaling, for every admitted profile and frame. -/
theorem uniform_native_first_adjoint_error_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CE CEH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧ 0 ≤ CEH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ Vt Vc : s.response.SymmetricAdjointDomain,∀ a : X,∀ CB : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CB,
        SmoothFiniteJetBound (s.firstAdjointHalfErrorFamily C ∘
          normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
          ((0,frameVectorLinear d.frame y),0) 3 (CE*‖a‖*d.radius y) ∧
        SmoothFiniteJetBound (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK) ∘
          normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
          ((0,frameVectorLinear d.frame y),0) 3 (CE*‖a‖*d.radius y) ∧
        ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (s.firstAdjointHalfErrorFamily C) n ((y,frameVectorLinear d.frame y),0)‖ ≤
              CEH*‖a‖*d.radius y*(beta d.γ d.radius y)^n ∧
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK)) n
            ((y,frameVectorLinear d.frame y),0)‖ ≤ CEH*‖a‖*d.radius y*(beta d.γ d.radius y)^n := by
  obtain ⟨ηT,BT,BTH,hηT,hηT1,hBT,hBTH,hTaylor⟩ := uniform_native_higher_taylor_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  obtain ⟨ηG,BGL,BGH,BGHH,hηG,hηG1,hBGL,hBGH,hBGHH,hCenter⟩ := uniform_native_center_higher_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW CC hCQ hCI hCW hCC F0 hF0
  obtain ⟨BR,hBR,hReciprocal⟩ := exists_relative_inverse_radius_factor_jet_bound 3
  obtain ⟨BML,hBML,hML⟩ := uniform_relative_coframe_normal_three_jets hΩ (by omega) K M hK (1/2:ℝ)
  obtain ⟨BMH,hBMH,hMH⟩ := uniform_relative_coframe_normal_three_jets hΩ (by omega) K M hK (3/2:ℝ)
  obtain ⟨BL,hBL,hLog⟩ := uniform_normalFrame_scaled_log_covector_three_jets hY hΩ hSub (by omega) K M Cj hK
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_from_scaled_three_jets hY hΩ hSub (by omega) K M Cj hK
  let BP := |lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ|
  let EL := firstAdjointErrorScaledJetBudget BR BP BML BL BGL
  let EH := firstAdjointErrorScaledJetBudget BR BT BMH BL BGH
  let CE := EL+EH
  let CEH := CX*CE
  have hBR0 := zero_le_one.trans hBR
  have hBL0 := zero_le_one.trans hBL
  have hBP : 0 ≤ BP := abs_nonneg _
  have hEL : 0 ≤ EL := firstAdjointErrorScaledJetBudget_nonneg _ _ _ _ _ hBR0 hBP hBML hBL0 hBGL
  have hEH : 0 ≤ EH := firstAdjointErrorScaledJetBudget_nonneg _ _ _ _ _ hBR0 hBT hBMH hBL0 hBGH
  have hCE : 0 ≤ CE := add_nonneg hEL hEH
  have hCEH : 0 ≤ CEH := mul_nonneg (zero_le_one.trans hCX) hCE
  refine ⟨min ηT ηG,CE,CEH,lt_min hηT hηG,(min_le_left _ _).trans hηT1,hCE,hCEH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨Vt,hTF,hTA,hTH⟩ := hTaylor floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CF0 CA0 CM s
  obtain ⟨Vc,hGC⟩ := hCenter floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF0 CA0 CM s
  refine ⟨Vt,Vc,?_⟩
  intro a CB C
  let r := d.radius y
  let β := beta d.γ d.radius y
  let L := frameVectorLinear d.frame y
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  let p1 : NormalFrameRelativeParameter := ((y,L),0)
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 := zero_le_one.trans hβ
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηT1)
  have hrβ : r*β ≤ 1 := by
    have hSmallR : r*β^2 ≤ ε := (hd.2.2.2.2.2 y hy).2
    have hPower : β ≤ β^2 := by nlinarith only [mul_le_mul_of_nonneg_left hβ hβ0]
    exact ((mul_le_mul_of_nonneg_left hPower hr.le).trans hSmallR).trans hε1
  have hrε : r ≤ ε := (radius_bounds r β floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hLow : SmoothFiniteJetBound s.coefficients.halfTaylor p1 3 (BP*r^2) :=
    ⟨by positivity,Vt.contDiffOn_halfTaylor.contDiffAt (Vt.domainOpen.mem_nhds Vt.pointMem),
      s.coefficients.native_half_taylor_higher_jets 3 (by norm_num) hCQ hCW hr.le hr1 F0 hF0 s.point⟩
  have hHalfPa : SmoothFiniteJetBound s.response.adjointHalfTaylor p1 3 (BP*r^2) := hLow.adjoint
  obtain ⟨hGL,hGH,hGHH⟩ := hGC a CB C
  have he (i j : I) : metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0 := by
    simpa only [L,frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have hMLHere := hML d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) L he a
  have hMHHere := hMH d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) L he a
  obtain ⟨hR,hRJ⟩ := hReciprocal (0:X) L
  have hRBound : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor p0 3 BR := ⟨hBR0,hR,hRJ⟩
  have hLogBound := hLog d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy L
  have hHalfRaw := relativeFirstAdjointError_rescaled_composition_three_jets d y a β BR BP BML BL BGL
    hr hβ hrβ hBR0 hBP hBML hBL0 hBGL s.response.adjointHalfTaylor (s.centerGradientHalfFamily C)
    (relativeCoframeNormalSobolevL (1/2:ℝ) d.γ a) hHalfPa hMLHere hGL hRBound hLogBound
  have hHighRaw := relativeFirstAdjointError_rescaled_composition_three_jets d y a β BR BT BMH BL BGH
    hr hβ hrβ hBR0 hBT hBMH hBL0 hBGH (Vt.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
    (s.centerGradientHigherFamily C Vc hd.1.1 (zero_lt_one.trans_le hK))
    (relativeCoframeNormalSobolevL (3/2:ℝ) d.γ a) hTA hMHHere hGH hRBound hLogBound
  have hHalf : SmoothFiniteJetBound (s.firstAdjointHalfErrorFamily C ∘ normalFrameRelativeScaledParameter β y)
      p0 3 (CE*‖a‖*r) := hHalfRaw.weaken (by
    change EL*‖a‖*r ≤ (EL+EH)*‖a‖*r
    gcongr
    linarith only [hEH])
  have hHigh : SmoothFiniteJetBound (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK) ∘
      normalFrameRelativeScaledParameter β y) p0 3 (CE*‖a‖*r) := hHighRaw.weaken (by
    change EH*‖a‖*r ≤ (EL+EH)*‖a‖*r
    gcongr
    linarith only [hEL])
  have hHL := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) _ (CE*‖a‖*r) hHalf
  have hHH := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) _ (CE*‖a‖*r) hHigh
  refine ⟨hHalf,hHigh,?_⟩
  intro b hb n hn
  exact ⟨(hHL b hb n hn).trans_eq (by dsimp only [CEH];ring),
    (hHH b hb n hn).trans_eq (by dsimp only [CEH];ring)⟩
end ShrinkingSpheres
