import Proof.NativeCenterGradientHalfJets
import Proof.NativeCenterGradientHigherFamily
import Proof.UniformNativeCenterDegreeJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The same physical center-gradient has genuine half and higher endpoints,
    with gained mixed and actual horizontal three-jets and a common response. -/
theorem uniform_native_center_higher_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CL CH CHH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CL ∧ 0 ≤ CH ∧ 0 ≤ CHH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,∀ a : X,∀ CB : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CB,
        SmoothFiniteJetBound (s.centerGradientHalfFamily C)
          ((y,frameVectorLinear d.frame y),0) 3 (CL*‖a‖*d.radius y) ∧
        SmoothFiniteJetBound (s.centerGradientHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK))
          ((y,frameVectorLinear d.frame y),0) 3 (CH*‖a‖*d.radius y) ∧
        ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (s.centerGradientHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK)) n
            ((y,frameVectorLinear d.frame y),0)‖ ≤ CHH*‖a‖*d.radius y*(beta d.γ d.radius y)^n := by
  obtain ⟨η,CG,CGH,hη,hη1,hCG,hCGH,hDegree⟩ := uniform_native_center_gradient_degree_jets
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW CC hCQ hCI hCW hCC F0 hF0
  obtain ⟨CR,hCR,hReciprocal⟩ := exists_relative_inverse_radius_factor_jet_bound 3
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_third_jets hY hΩ hSub (by omega) K M Cj hK
  let BD := |lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ|+firstLowRadialJetConstant*CQ+‖fixedLowRadialL‖
  let CL := 2^3*CR*halfBoundaryGradientJetBudget 3 BD*CC
  let CH := CL+CG
  let CHH := CX*CH
  have hBD : 0 ≤ BD := by
    have hFirst := firstLowRadialJetConstant_nonneg
    dsimp only [BD]
    positivity
  have hGrad := halfBoundaryGradientJetBudget_nonneg 3 hBD
  have hCR0 := zero_le_one.trans hCR
  have hCL : 0 ≤ CL := by dsimp only [CL];positivity
  have hCH : 0 ≤ CH := add_nonneg hCL hCG
  have hCHH : 0 ≤ CHH := mul_nonneg (zero_le_one.trans hCX) hCH
  refine ⟨η,CL,CH,CHH,hη,hη1,hCL,hCH,hCHH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨V,hD⟩ := hDegree floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  refine ⟨V,?_⟩
  intro a CB C
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans hη1)
  have hFull := (s.response.fullHalf_three_jet_bounds V (by norm_num) hCQ hCW hr.le hr1 F0 hF0 s.point).2
  obtain ⟨hR,hRJ⟩ := hReciprocal y (frameVectorLinear d.frame y)
  have hRB : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor p0 3 CR := ⟨hCR0,hR,hRJ⟩
  have hLow := s.centerGradientHalf_three_jet_bound C BD CR hCC hr hFull hRB
  obtain ⟨hSmooth,hJets,hHorizontalDegree⟩ := hD a CB C
  have hDB : SmoothFiniteJetBound (s.centerGradientDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK))
      p0 3 (CG*‖a‖*d.radius y) := ⟨by positivity,hSmooth,hJets⟩
  have hLift := halfDegreeHigherLift_jet_bound hLow hDB
  have hHi : SmoothFiniteJetBound (s.centerGradientHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK))
      p0 3 (CH*‖a‖*d.radius y) := by
    change SmoothFiniteJetBound (fun x => halfDegreeHigherLift (s.centerGradientHalfFamily C x)
      (s.centerGradientDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK) x)) p0 3 (CH*‖a‖*d.radius y)
    simpa only [CH,CL,add_mul] using hLift
  refine ⟨hLow,hHi,?_⟩
  have hJs (n : ℕ) (hn : n ≤ 3) :
      ‖iteratedFDeriv ℝ n (s.centerGradientHigherFamily C V hd.1.1 (zero_lt_one.trans_le hK)) p0‖ ≤
      (CH*‖a‖/(d.radius y))*(d.radius y)^2 := (hHi.bound n hn).trans_eq (by field_simp)
  have hh := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) _ hHi.smooth
    (CH*‖a‖/(d.radius y)) (d.radius y) (by positivity) hJs
  intro b hb n hn
  exact (hh b hb n hn).trans_eq (by dsimp only [CHH];field_simp)
end ShrinkingSpheres
