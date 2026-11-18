import Proof.ActualFirstAdjointErrorGerm
import Proof.NativeFirstAdjointErrorRegularity
import Proof.SmoothUniqueLocalRealization
import Proof.CompatibleEndpointUniqueness
import Proof.UniformNativeFirstAdjointErrorEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The SAME globally chosen physical remainder has smooth genuine half and
    higher endpoints, with common uniform radius gain on the full base. -/
theorem uniform_actual_first_adjoint_error_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ a : X,
      ∀ R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∃ L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        ContDiffOn ℝ ∞ L Y ∧ ContDiffOn ℝ ∞ H Y ∧ ∀ x ∈ Y,
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x) =
            (L x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
          (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (H x) =
            (actualFirstAdjointErrorFamily d a A G x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧
          ‖L x‖ ≤ CE*‖a‖*d.radius x ∧ ‖H x‖ ≤ CE*‖a‖*d.radius x := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hC⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CE,CEH,hηE,hηE1,hCE,hCEH,hError⟩ :=
    uniform_native_first_adjoint_error_endpoints hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd a R A G hR hA hG
  let E := actualFirstAdjointErrorFamily d a A G
  let Low (x : X) (L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) : Prop :=
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (E x) =
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  let High (x : X) (H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) : Prop :=
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H =
      (E x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
  have hSmallT := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallE := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hLocal (y : X) (hy : y ∈ Y) :
      ∃ L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        ContDiffAt ℝ ∞ L y ∧ ContDiffAt ℝ ∞ H y ∧
        (∀ᶠ x in 𝓝 y,Low x (L x) ∧ High x (H x)) ∧
        ‖L y‖ ≤ CE*‖a‖*d.radius y ∧ ‖H y‖ ≤ CE*‖a‖*d.radius y := by
    obtain ⟨s⟩ := hNative floor hf ε hε hSmallT d hd y hy
    obtain ⟨Vt,Vc,hEndpoints⟩ := hError floor hf ε hε hSmallE d hd y hy CF CA CM s
    let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
      fun j => Classical.choice (hC floor hf ε hε hSmallC d hd y hy a j)
    let Ψ := normalFrameRelativeActualParameter d (d.radius y)
    let p1 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
    have hΨ := (contDiffOn_normalFrameRelativeActualParameter d (d.radius y) hd.2.2.2.2.1.1
      (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub)).contDiffAt (hY.mem_nhds hy)
    have hΨ0 : Ψ y = p1 := normalFrameRelativeActualParameter_point d y hr
    have hStayT : ∀ᶠ x in 𝓝 y,Ψ x ∈ s.centerDegreeDomain Vt :=
      hΨ.continuousAt.eventually ((s.centerDegreeDomain_open Vt).mem_nhds
        (by rw [normalFrameRelativeActualParameter_point d y hr];exact s.centerDegreeDomain_pointMem Vt))
    have hStayC : ∀ᶠ x in 𝓝 y,Ψ x ∈ s.centerDegreeDomain Vc :=
      hΨ.continuousAt.eventually ((s.centerDegreeDomain_open Vc).mem_nhds
        (by rw [normalFrameRelativeActualParameter_point d y hr];exact s.centerDegreeDomain_pointMem Vc))
    let L := s.firstAdjointHalfErrorFamily C ∘ Ψ
    let H := s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK) ∘ Ψ
    have hLS : ContDiffAt ℝ ∞ L y := by
      have hh := (s.contDiffOn_firstAdjointHalfErrorFamily C Vt hY hΩ hd.1.1 (zero_lt_one.trans_le hK)
        hd.2.2.2.2.1).contDiffAt ((s.centerDegreeDomain_open Vt).mem_nhds (s.centerDegreeDomain_pointMem Vt))
      change ContDiffAt ℝ ∞ (s.firstAdjointHalfErrorFamily C) p1 at hh
      rw [← hΨ0] at hh
      exact hh.comp y hΨ
    have hHS : ContDiffAt ℝ ∞ H y := by
      have hh := s.contDiffAt_firstAdjointHigherErrorFamily C Vt Vc hY hΩ hd.1.1 (zero_lt_one.trans_le hK)
        hd.2.2.2.2.1 p1 Vt.pointMem (s.centerDegreeDomain_pointMem Vc)
      rw [← hΨ0] at hh
      exact hh.comp y hΨ
    have hGerm := s.actual_first_adjoint_error_germ Vt hY hΩ hSub hd.1 (zero_lt_one.trans_le hK)
      hy hr hd.2.2.2.2.1.1 C R A G hR hA hG
    have hCompat : ∀ᶠ x in 𝓝 y,Low x (L x) ∧ High x (H x) := by
      filter_upwards [hGerm,hStayT,hStayC] with x hx hxt hxc
      constructor
      · change (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (E x) = _
        rw [show E x = s.firstAdjointErrorFamily C (Ψ x) from hx]
        exact s.firstAdjointHalfErrorFamily_coarse_compatible C Vt hF0 (Ψ x) hxt.1
      · change _ = (E x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
        rw [show E x = s.firstAdjointErrorFamily C (Ψ x) from hx]
        exact s.firstAdjointHigherErrorFamily_coarse_compatible C Vt Vc hd.1.1 (zero_lt_one.trans_le hK)
          hF0 (Ψ x) hxt.1 hxc
    obtain ⟨hLJ,hHJ,hHor⟩ := hEndpoints a CH C
    have hLN := hLJ.bound 0 (by omega)
    have hHN := hHJ.bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hLN hHN
    simp only [Function.comp_apply,normalFrameRelativeScaledParameter_point] at hLN hHN
    refine ⟨L,H,hLS,hHS,hCompat,?_,?_⟩
    · change ‖s.firstAdjointHalfErrorFamily C (Ψ y)‖ ≤ _
      rw [hΨ0]
      exact hLN
    · change ‖s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 (zero_lt_one.trans_le hK) (Ψ y)‖ ≤ _
      rw [hΨ0]
      exact hHN
  obtain ⟨L,hLS,hL⟩ := exists_contDiffOn_unique_local_realization hY Low
    (fun x hx U V hU hV => half_endpoint_unique_of_coarse (E x) U V hU hV) (by
      intro y hy
      obtain ⟨L,H,hLS,hHS,hCompat,hLN,hHN⟩ := hLocal y hy
      exact ⟨L,hLS,hCompat.mono (fun x hx => hx.1)⟩)
  obtain ⟨H,hHS,hH⟩ := exists_contDiffOn_unique_local_realization hY High
    (fun x hx U V hU hV => higher_endpoint_unique_of_coarse (E x) U V hU hV) (by
      intro y hy
      obtain ⟨L,H,hLS,hHS,hCompat,hLN,hHN⟩ := hLocal y hy
      exact ⟨H,hHS,hCompat.mono (fun x hx => hx.2)⟩)
  refine ⟨L,H,hLS,hHS,?_⟩
  intro x hx
  obtain ⟨L₀,H₀,hL₀S,hH₀S,hCompat,hL₀N,hH₀N⟩ := hLocal x hx
  have hPoint := hCompat.self_of_nhds
  have hLEq := half_endpoint_unique_of_coarse (E x) (L x) (L₀ x) (hL x hx) hPoint.1
  have hHEq := higher_endpoint_unique_of_coarse (E x) (H x) (H₀ x) (hH x hx) hPoint.2
  exact ⟨hL x hx,hH x hx,(congrArg norm hLEq).trans_le hL₀N,(congrArg norm hHEq).trans_le hH₀N⟩
end ShrinkingSpheres
