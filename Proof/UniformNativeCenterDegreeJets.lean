import Proof.NativeCenterDegreeFamily
import Proof.NativeCenterGradientAngularJets
import Proof.UniformNativeFullRadialAngularJets
import Proof.UniformNormalFrameHorizontalThirdJets
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

/-- The SAME physical center-gradient adjoint has an actual degree
    commutator whose ordinary and actual horizontal three-jets gain radius.
    No derivative budget for the admitted frame is assumed. -/
theorem uniform_native_center_gradient_degree_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CG CGH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CG ∧ 0 ≤ CGH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,∀ a : X,∀ CH : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH,
      ContDiffAt ℝ ∞ (s.centerGradientDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK))
        ((y,frameVectorLinear d.frame y),0) ∧
      (∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n
        (s.centerGradientDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK))
        ((y,frameVectorLinear d.frame y),0)‖ ≤ CG*‖a‖*d.radius y) ∧
      ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
        ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
          (s.centerGradientDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK)) n
          ((y,frameVectorLinear d.frame y),0)‖ ≤ CGH*‖a‖*d.radius y*(beta d.γ d.radius y)^n := by
  obtain ⟨η,BD,hη,hη1,hBD,hFull⟩ := uniform_native_full_radial_angular_field_jets hY hΩ hm
    K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  obtain ⟨CR,hCR,hReciprocal⟩ := exists_relative_inverse_radius_factor_jet_bound 3
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_third_jets hY hΩ hSub (by omega) K M Cj hK
  let G := 2^3*CR*boundaryGradientAngularJetBudget 3 BD*CC
  let CG := (12*Real.sqrt 2)*G
  let CGH := CX*CG
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hGrad := boundaryGradientAngularJetBudget_nonneg 3 hBD
  have hG : 0 ≤ G := by dsimp only [G];positivity
  have hCG : 0 ≤ CG := by dsimp only [CG];positivity
  have hCGH : 0 ≤ CGH := by dsimp only [CGH];positivity
  refine ⟨η,CG,CGH,hη,hη1,hCG,hCGH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨V,hD⟩ := hFull floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  refine ⟨V,?_⟩
  intro a CH C
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let H := s.centerGradientDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK)
  have hp0 := s.centerDegreeDomain_pointMem V
  have hSmoothOn := s.contDiffOn_centerGradientDegreeFamily C V hΩ hd.1.1 (zero_lt_one.trans_le hK)
  have hSmooth : ContDiffAt ℝ ∞ H p0 := hSmoothOn.contDiffAt ((s.centerDegreeDomain_open V).mem_nhds hp0)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  obtain ⟨hR,hRJ⟩ := hReciprocal y (frameVectorLinear d.frame y)
  have hRB : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor p0 3 CR := ⟨hCR0,hR,hRJ⟩
  have hFields := s.centerGradientAngularFields_jet_bound C BD CR hCC hr hD hRB
  have hData := hFields.degreeData
  have hJets (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n H p0‖ ≤ CG*‖a‖*d.radius y := by
    have hh := CoarseDegreeCompatibility.norm_iteratedFDeriv_halfFamily_le
      (fun p => (s.centerGradientAngularFields C p).degreeData) (s.centerDegreeDomain V)
      (s.centerDegreeDomain_open V) (s.centerGradientDegree_constraint C V hd.1.1 (zero_lt_one.trans_le hK))
      (s.contDiffOn_centerGradientDegreeData C V hΩ hd.1.1 (zero_lt_one.trans_le hK)) p0 hp0
      (G*‖a‖*d.radius y) (by positivity) n (hData.bound n hn)
    exact hh.trans_eq (by dsimp only [CG];ring)
  refine ⟨hSmooth,hJets,?_⟩
  have hJs (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n H p0‖ ≤
      (CG*‖a‖/(d.radius y))*(d.radius y)^2 := (hJets n hn).trans_eq (by field_simp)
  have hh := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) H hSmooth
    (CG*‖a‖/(d.radius y)) (d.radius y) (by positivity) hJs
  intro b hb n hn
  exact (hh b hb n hn).trans_eq (by dsimp only [CGH];field_simp)
end ShrinkingSpheres
