import Proof.ParallelScalarFirstNativeHalfTwoJets
import Proof.UniformNativeFirstAdjointErrorEndpoints
import Proof.UniformNativeRelativeHorizontalTaylorData
import Proof.RelativeCenterErrorCoefficientFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Any already fixed strong extension of the actual native error's first
covariant jet is smooth, and its second genuine coarse graph has a strong
half-domain extension with the original radius-beta-squared bound. -/
theorem uniform_actual_first_error_second_strong_half_graph
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ b : X,‖b‖ ≤ 1 →
      ∀ S : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∀ L : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (∀ x ∈ Y,CoarseCovariantRotationGraph d x b (actualFirstAdjointErrorFamily d a A G) (S x)) →
      (∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (S x)=
        (L x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) →
      ContDiffOn ℝ ∞ L Y ∧ ∀ y ∈ Y,∀ c : X,‖c‖ ≤ 1 →
      ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y c S T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ CE*‖a‖*d.radius y*(beta d.γ d.radius y)^2 := by
  classical
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoeff⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,C0,CE,hηE,hηE1,hC0,hCE,hEndpoint⟩ :=
    uniform_native_first_adjoint_error_endpoints hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
      CQ CI CW CC (zero_le_one.trans hCQ) hCI hCW (zero_le_one.trans hCC) F0 hF0
  refine ⟨min ηT (min ηC ηE),CE,lt_min hηT (lt_min hηC hηE),
    (min_le_left _ _).trans hηT1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hR hA a G hG b hb S L hS hL
  have hPoint (y : X) (hy : y ∈ Y) (c : X) (hc : ‖c‖ ≤ 1) :
      ContDiffAt ℝ ∞ L y ∧
      ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y c S T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ CE*‖a‖*d.radius y*(beta d.γ d.radius y)^2 := by
    obtain ⟨s⟩ := hNative floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
    obtain ⟨Vt,Vc,hEnd⟩ := hEndpoint floor hf ε hε
      (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy CF CA CM s
    let C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH :=
      fun j => Classical.choice (hCoeff floor hf ε hε
        (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy a j)
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let B := normalFrameRelativeHorizontalField d.γ d.radius b
    let v := normalFrameRelativeHorizontalField d.γ d.radius c p
    let T := fderiv ℝ (fun q => fderiv ℝ (s.firstAdjointErrorFamily C) q (B q)) p v
    let N := fderiv ℝ (fun q => fderiv ℝ (s.firstAdjointHalfErrorFamily C) q (B q)) p v
    have hGraph := native_first_error_strong_half_two_jet_graph s C Vt hY hΩ hSub hd
      (zero_lt_one.trans_le hK) hy hF0 R A G hR hA hG b c S L hS hL
    refine ⟨hGraph.1,T,N,hGraph.2.1,hGraph.2.2,?_⟩
    let directions : ℕ → X := fun j => if j=0 then b else c
    have hDirections (j : ℕ) : ‖directions j‖ ≤ 1 := by
      dsimp only [directions]
      split_ifs <;> assumption
    have hN := ((hEnd a CH C).2.2 directions hDirections 2 (by norm_num)).1
    simpa [orderedDirectionalFamily,directions,N,p,B,v,mul_assoc] using hN
  refine ⟨?_,?_⟩
  · intro y hy
    exact (hPoint y hy 0 (by simp)).1.contDiffWithinAt
  · intro y hy c hc
    exact (hPoint y hy c hc).2

end ShrinkingSpheres.ParallelEnergy
