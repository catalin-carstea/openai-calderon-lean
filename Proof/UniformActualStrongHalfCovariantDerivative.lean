import Proof.NativeFirstCovariantHalfLift
import Proof.UniformNativeFirstAdjointErrorEndpoints
import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.RelativeCenterErrorCoefficientFamily
import Proof.UniformActualFirstAdjointEndpoints
import Proof.UniformActualFirstErrorCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- The covariant derivative in the physical Green formula has a genuine
H-half to H-minus-half extension with the SAME uniform radius-beta gain.
This is stronger than merely bounding its H-three-halves restriction.
All choices precede tests; arbitrary smooth compatible physical endpoints
are allowed, and frame derivatives cancel in the genuine coarse graph. -/
theorem uniform_actual_first_error_strong_half_covariant_derivative
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ _hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ContDiffOn ℝ ∞ Lo Y →
      (∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
        (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) →
      (∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi x)=
        (actualFirstAdjointErrorFamily d a A G x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 →
      ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        halfOperatorCovariantDerivativeL d Lo Hi y b=
          L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖L‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖L‖ ≤ CE*‖a‖*ε := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE0,CE,hηE,hηE1,hCE0,hCE,hEndpoint⟩ :=
    uniform_native_first_adjoint_error_endpoints hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG Lo Hi hLS hLow hHigh y hy b hb
  obtain ⟨s⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨Vt,Vc,hEnd⟩ := hEndpoint floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a j)
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let v := normalFrameRelativeHorizontalField d.γ d.radius b p
  let S := fderiv ℝ (s.firstAdjointErrorFamily C) p v
  let L := fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v
  have hCompat := s.first_covariant_half_derivative_compatible C Vt hY hΩ hd.1.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1 hF0 v
  have hGraph := s.actual_first_error_covariant_graph C Vt hY hΩ hSub hd
    (zero_lt_one.trans_le hK) hy R A G hAS hGS hR hA hG b
  have hHS := contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS
  have hLowGerm : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
      (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hLow x hx
  have hEq := halfOperatorCovariantDerivativeL_eq_strong_extension
    (actualFirstAdjointErrorFamily d a A G) Lo Hi S L
    ((hHS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hLS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hLowGerm (hHigh y hy) hGraph hCompat
  have hN := ((hEnd a CH C).2.2 (fun _ => b) (fun _ => hb) 1 (by norm_num)).1
  have hLN : ‖L‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y := by
    simpa only [orderedDirectionalFamily,pow_one,p,v,L] using hN
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hRadius := radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hrβ : d.radius y*beta d.γ d.radius y ≤ ε := hRadius.2.1.trans (div_le_self hε hf)
  refine ⟨L,hEq,hLN,hLN.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ (mul_nonneg hCE (norm_nonneg a))

/-- The actual first-error covariant coefficient has a genuine strong
half-domain graph and its sharp uniform radius-beta bound. Both the original
coefficient and its covariant jet retain explicit inclusion witnesses. -/
theorem uniform_actual_first_error_covariant_half_graph
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 →
      ∃ L0 L1 : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ S : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G y)=
          L0.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) S ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
          L1.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖L0‖ ≤ C0*‖a‖*d.radius y ∧
        ‖L1‖ ≤ C1*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖L1‖ ≤ C1*‖a‖*ε := by
  obtain ⟨ηS,C1,hηS,hηS1,hC1,hStrong⟩ :=
    uniform_actual_first_error_strong_half_covariant_derivative hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,C0,hηE,hηE1,hC0,hEndpoint⟩ :=
    uniform_actual_first_adjoint_error_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,hηC,hηC1,hCC,hCov⟩ :=
    uniform_actual_first_error_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηS (min ηE ηC),C0,C1,lt_min hηS (lt_min hηE hηC),
    (min_le_left _ _).trans hηS1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy b hb
  have hSmallS := hSmall.trans (min_le_left _ _)
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Lo,Hi,hLS,hHS,hEnd⟩ := hEndpoint floor hf ε hε hSmallE d hd a R A G hR hA hG
  have hLow (x) (hx : x ∈ Y) := (hEnd x hx).1
  have hHigh (x) (hx : x ∈ Y) := (hEnd x hx).2.1
  obtain ⟨L,hL,hLN,hLE⟩ := hStrong floor hf ε hε hSmallS d hd R A hAS hR hA a G hGS hG
    Lo Hi hLS hLow hHigh y hy b hb
  obtain ⟨S,hS,hSN⟩ := hCov floor hf ε hε hSmallC d hd R A hAS hR hA a G hGS hG y hy b hb
  have hHS := contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS
  have hLowGerm : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
      (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hLow x hx
  have hWeak := halfOperatorCovariantDerivativeL_eq_coarse (actualFirstAdjointErrorFamily d a A G) Lo Hi S
    ((hHS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hLS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hLowGerm (hHigh y hy) hS
  have hCompat := coarse_half_endpoint_of_weak_strong S L (hWeak.symm.trans hL)
  exact ⟨Lo y,L,S,hLow y hy,hS,hCompat,(hEnd y hy).2.2.1,hLN,hLE⟩

end ShrinkingSpheres
