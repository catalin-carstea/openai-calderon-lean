import Proof.UniformNativeFirstErrorTrueAdjointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A genuine native horizontal true-adjoint higher jet with the sharp
radius-beta and epsilon bounds. Transport to a selected physical adjoint
covariant derivative is a separate remaining inference. -/
theorem uniform_native_first_error_true_adjoint_horizontal_higher_jet {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ V : s.response.SymmetricAdjointDomain,∀ a : X,∀ CB : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CB,
      ∀ b : X,‖b‖ ≤ 1 →
      let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      let v := normalFrameRelativeHorizontalField d.γ d.radius b p
      ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H=
          (fderiv ℝ (fun q => (s.firstAdjointHalfErrorFamily C q).adjoint) p v).comp
            (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖H‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖H‖ ≤ CE*‖a‖*ε := by
  obtain ⟨η,C0,CE,hη,hη1,hC0,hCE,hProduce⟩ := uniform_native_first_error_true_adjoint_higher_three_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW CC hCQ hCI hCW hCC F0 hF0
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨V,hV⟩ := hProduce floor hf ε hε hSmall d hd y hy CF CA CM s
  refine ⟨V,?_⟩
  intro a CB C b hb
  dsimp only
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let v := normalFrameRelativeHorizontalField d.γ d.radius b p
  let H := fderiv ℝ (s.firstErrorTrueAdjointHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK)) p v
  have hCompat := s.firstErrorTrueAdjointHigherFamily_derivative_compatible C V hY hΩ hd.1.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1 hF0 p v (s.centerDegreeDomain_pointMem V)
  have hN := (hV a CB C).2.2 (fun _ => b) (fun _ => hb) 1 (by norm_num)
  have hHN : ‖H‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y := by
    simpa only [orderedDirectionalFamily,pow_one,p,v,H] using hN
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hRadius := radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2
  have hrβ : d.radius y*beta d.γ d.radius y ≤ ε := hRadius.2.1.trans (div_le_self hε hf)
  refine ⟨H,hCompat,hHN,hHN.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrβ (mul_nonneg hCE (norm_nonneg a))

end ShrinkingSpheres
