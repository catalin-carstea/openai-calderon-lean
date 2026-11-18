import Proof.NativeFirstAdjointErrorRegularity
import Proof.NativeActualFirstErrorCovariant
import Proof.EndpointCompatibleDerivative
import Proof.UniformNativeFirstAdjointErrorEndpoints
import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.RelativeCenterErrorCoefficientFamily

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

lemma NativeRelativeHorizontalTaylorData.first_covariant_higher_derivative_compatible
    {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM CC CH : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain) (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hProfile : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (v : NormalFrameRelativeParameter) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc h hK) p v)=
    (fderiv ℝ (s.firstAdjointErrorFamily C) p v).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  extract_lets p
  have hp := s.centerDegreeDomain_pointMem Vt
  have hOp := (s.firstErrorAngularFields_smoothAt C Vt hY hΩ h hK hProfile p hp).operator
  have hEq : (fun q => (s.firstErrorAngularFields C q).operator)=s.firstAdjointErrorFamily C :=
    funext (fun q => s.firstErrorAngularFields_operator C q)
  rw [hEq] at hOp
  have hHigh := s.contDiffAt_firstAdjointHigherErrorFamily C Vt Vc hY hΩ h hK hProfile p
    Vt.pointMem (s.centerDegreeDomain_pointMem Vc)
  have hGraph : ∀ᶠ q in 𝓝 p,
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (s.firstAdjointHigherErrorFamily C Vt Vc h hK q)=
        (s.firstAdjointErrorFamily C q).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
    filter_upwards [Vt.domainOpen.mem_nhds Vt.pointMem,
      (s.centerDegreeDomain_open Vc).mem_nhds (s.centerDegreeDomain_pointMem Vc)] with q hqt hqc
    exact s.firstAdjointHigherErrorFamily_coarse_compatible C Vt Vc h hK hF0 q hqt hqc
  exact compatible_endpoint_fderiv _ _ _ _ p v (hHigh.differentiableAt (by simp))
    (hOp.differentiableAt (by simp)) hGraph

/-- The actual error and its covariant jet retain genuine higher endpoints
with original radius/radius-beta bounds, for arbitrary actual realizations. -/
theorem uniform_actual_first_error_covariant_higher_graph
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 C1 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧ 0 ≤ C1 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y → (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y → (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 →
      ∃ H0 H1 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ∃ S : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H0=
          (actualFirstAdjointErrorFamily d a A G y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) S ∧
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H1=
          S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
        ‖H0‖ ≤ C0*‖a‖*d.radius y ∧
        ‖H1‖ ≤ C1*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖H1‖ ≤ C1*‖a‖*ε := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,C0,C1,hηE,hηE1,hC0,hC1,hEndpoint⟩ :=
    uniform_native_first_adjoint_error_endpoints hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),C0,C1,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hC0,hC1,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy b hb
  obtain ⟨s⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  obtain ⟨Vt,Vc,hEnd⟩ := hEndpoint floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy CF CA CM s
  let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
    fun j => Classical.choice (hCoeff floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a j)
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let v := normalFrameRelativeHorizontalField d.γ d.radius b p
  let H := s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK)
  let H1 := fderiv ℝ H p v
  let S := fderiv ℝ (s.firstAdjointErrorFamily C) p v
  have hBase := s.firstAdjointHigherErrorFamily_coarse_compatible C Vt Vc hd.1.1
    (zero_lt_one.trans_le hK) hF0 p Vt.pointMem (s.centerDegreeDomain_pointMem Vc)
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hActual : actualFirstAdjointErrorFamily d a A G y=s.firstAdjointErrorFamily C p := by
    have hg := s.actual_first_adjoint_error_germ Vt hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hy hr0 hd.2.2.2.2.1.1 C R A G hR hA hG
    simpa only [normalFrameRelativeActualParameter_point d y hr0] using hg.eq_of_nhds
  have hBaseActual := hBase.trans (congrArg (fun B : SphereSobolev 1 →L[ℝ] SphereSobolev 0 =>
    B.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) hActual.symm)
  have hCompat := s.first_covariant_higher_derivative_compatible C Vt Vc hY hΩ hd.1.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1 hF0 v
  have hGraph := s.actual_first_error_covariant_graph C Vt hY hΩ hSub hd
    (zero_lt_one.trans_le hK) hy R A G hAS hGS hR hA hG b
  have hPoint := (hEnd a CH C).2.1.bound 0 (by omega)
  rw [norm_iteratedFDeriv_zero] at hPoint
  simp only [Function.comp_apply,normalFrameRelativeScaledParameter_point] at hPoint
  have hN := ((hEnd a CH C).2.2 (fun _ => b) (fun _ => hb) 1 (by norm_num)).2
  have hHN : ‖H1‖ ≤ C1*‖a‖*d.radius y*beta d.γ d.radius y := by
    simpa only [orderedDirectionalFamily,pow_one,p,v,H,H1] using hN
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hRadius := radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hrβ : d.radius y*beta d.γ d.radius y ≤ ε := hRadius.2.1.trans (div_le_self hε hf)
  refine ⟨H p,H1,S,hBaseActual,hGraph,hCompat,hPoint,hHN,hHN.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ (mul_nonneg hC1 (norm_nonneg a))

end ShrinkingSpheres
