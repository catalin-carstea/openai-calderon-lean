import Proof.NativeActualAngularEndpoints
import Proof.ScaledFrameAngularDerivative
import Proof.UniformNativeFirstAdjointErrorEndpoints
import Proof.FirstMetricNormalDensity
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

/-- Every already chosen physical rotation commutator has genuine low/high
    endpoints with uniform radius gain. No new realization premise is added. -/
theorem uniform_actual_angular_error_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ _hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ y ∈ Y,∀ i j : I,∀ S : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ u : SphereSobolev 2,
        sphereSobolevRotationL 0 i j (actualFirstAdjointErrorFamily d a A G y
          (sphereSobolevInclusionL 2 1 (by norm_num) u))=
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (S (sphereSobolevInclusionL 2 1 (by norm_num) u)+
            actualFirstAdjointErrorFamily d a A G y (sphereSobolevRotationL 2 i j u))) →
      ∃ Lo : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ Hi : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
          Lo.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hi=
          S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        ‖Lo‖ ≤ CE*‖a‖*d.radius y ∧ ‖Hi‖ ≤ CE*‖a‖*d.radius y := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,CEH,hηE,hηE1,hCE,hCEH,hError⟩ :=
    uniform_native_first_adjoint_error_endpoints hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  have hCEK : 0 ≤ 2*CE*K := by positivity
  refine ⟨min ηT (min ηC ηE),2*CE*K,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCEK,?_⟩
  intro floor hf ε hε hSmall d hd R A hR hA a G hG y hy i j S hS
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
  obtain ⟨Vt,Vc,hEndpoints⟩ := hError floor hf ε hε hSmallE d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hC floor hf ε hε hSmallC d hd y hy a j)
  let L := frameVectorLinear d.frame y
  let p : NormalFrameRelativeParameter := ((y,L),0)
  let v := normalFrameRelativeAngularTangent d.γ p i j
  let Lo := fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v
  let Hi := fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK)) p v
  have hCompat := s.actual_angular_error_endpoints C Vt Vc hY hΩ hSub hd
    (zero_lt_one.trans_le hK) hy hF0 R A G hR hA hG i j S hS
  obtain ⟨hLJ,hHJ,hHor⟩ := hEndpoints a CH C
  have he (k l : I) : metricPair d.γ y (L (axis k)) (L (axis l))=if k=l then 1 else 0 := by
    simpa only [L,frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) k l
  have hL : ‖L‖ ≤ K := hd.1.1.norm_frameVectorLinear_le hK (hSub hy) d.frame
    (hd.1.2.2.2.2.2.2.2 y (hSub hy))
  have hβ : beta d.γ d.radius y ≠ 0 :=
    (zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)).ne'
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hFix := normalFrameRelativeNormalization_eq_self d.γ p he
  have hLN := norm_relativeAngularDerivative_of_scaled_jets d.γ (s.firstAdjointHalfErrorFamily C)
    hβ y L he hLJ i j
  have hHN := norm_relativeAngularDerivative_of_scaled_jets d.γ
    (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK)) hβ y L he hHJ i j
  have hBound : 2*(CE*‖a‖*d.radius y)*‖L‖ ≤ (2*CE*K)*‖a‖*d.radius y := by
    exact (mul_le_mul_of_nonneg_left hL (by positivity)).trans_eq (by ring)
  refine ⟨Lo,Hi,hCompat.1,hCompat.2,?_,?_⟩
  · have hLo : ‖Lo‖ ≤ 2*(CE*‖a‖*d.radius y)*‖L‖ := by
      simpa only [normalFrameRelativeAngularDerivative,hFix,Lo,p,v] using hLN
    exact hLo.trans hBound
  · have hHi : ‖Hi‖ ≤ 2*(CE*‖a‖*d.radius y)*‖L‖ := by
      simpa only [normalFrameRelativeAngularDerivative,hFix,Hi,p,v] using hHN
    exact hHi.trans hBound
end ShrinkingSpheres
