import Proof.NativeActualCovariantEndpoints
import Proof.UniformNativeFirstAdjointErrorEndpoints
import Proof.UniformActualFirstErrorCovariant
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Every SAME actual coarse covariant error jet has genuine low/high
    endpoints with a common uniform radius-beta bound. The existing selected
    coarse jet is kept; it is identified by its physical covariant graph. -/
theorem uniform_actual_covariant_error_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ _hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 → ∀ S : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) S →
      ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
          Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
          S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        ‖Lo‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧
        ‖Hi‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,CEH,hηE,hηE1,hCE,hCEH,hError⟩ :=
    uniform_native_first_adjoint_error_endpoints hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CEH,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCEH,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy b hb S hS
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
  obtain ⟨Vt,Vc,hEndpoints⟩ := hError floor hf ε hε hSmallE d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hC floor hf ε hε hSmallC d hd y hy a j)
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let v := normalFrameRelativeHorizontalField d.γ d.radius b p
  let Lo := fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v
  let Hi := fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK)) p v
  have hCompat := s.actual_covariant_error_endpoints C Vt Vc hY hΩ hSub hd
    (zero_lt_one.trans_le hK) hy hF0 R A G hAS hGS hR hA hG b S hS
  obtain ⟨hLJ,hHJ,hHor⟩ := hEndpoints a CH C
  have hBounds := hHor (fun _j => b) (fun _j => hb) 1 (by norm_num)
  refine ⟨Lo,Hi,hCompat.1,hCompat.2,?_,?_⟩
  · simpa only [orderedDirectionalFamily,pow_one,Lo,p,v] using hBounds.1
  · simpa only [orderedDirectionalFamily,pow_one,Hi,p,v] using hBounds.2
end ShrinkingSpheres
