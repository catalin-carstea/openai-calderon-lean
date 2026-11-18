import Proof.NativeHalfTaylorHigherRegularity
import Proof.UniformNativeRelativeDegreeHigherData
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

/-- Both SAME native Taylor operators have genuine higher half endpoints
    with uniform quadratic mixed and actual horizontal three-jet bounds. -/
theorem uniform_native_higher_taylor_endpoints {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CH CHH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CH ∧ 0 ≤ CHH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,
        SmoothFiniteJetBound (V.forwardHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
          ((y,frameVectorLinear d.frame y),0) 3 (CH*(d.radius y)^2) ∧
        SmoothFiniteJetBound (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
          ((y,frameVectorLinear d.frame y),0) 3 (CH*(d.radius y)^2) ∧
        ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (V.forwardHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)) n
            ((y,frameVectorLinear d.frame y),0)‖ ≤ CHH*(d.radius y)^2*(beta d.γ d.radius y)^n ∧
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)) n
            ((y,frameVectorLinear d.frame y),0)‖ ≤ CHH*(d.radius y)^2*(beta d.γ d.radius y)^n := by
  obtain ⟨η,CF,CA,CD,hη,hη1,hCF,hCA,hCD,hDegree⟩ := uniform_native_relative_degree_higher_data hY hΩ 3
    (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_third_jets hY hΩ hSub (by omega) K M Cj hK
  let CL := |lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ|
  let CH := CL+CD
  let CHH := CX*CH
  have hCL : 0 ≤ CL := abs_nonneg _
  have hCD0 : 0 ≤ CD := zero_le_one.trans hCD
  have hCH : 0 ≤ CH := add_nonneg hCL hCD0
  have hCHH : 0 ≤ CHH := mul_nonneg (zero_le_one.trans hCX) hCH
  refine ⟨η,CH,CHH,hη,hη1,hCH,hCHH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨V,hF,hA,hD⟩ := hDegree floor hf ε hε hSmall d hd y hy CQ CF0 CA0 CM s
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans hη1)
  have hLow : SmoothFiniteJetBound s.coefficients.halfTaylor p0 3 (CL*(d.radius y)^2) :=
    ⟨by positivity,V.contDiffOn_halfTaylor.contDiffAt (V.domainOpen.mem_nhds V.pointMem),
      s.coefficients.native_half_taylor_higher_jets 3 (by norm_num) hCQ hCW hr.le hr1 F0 hF0 s.point⟩
  have hDegreeBound : SmoothFiniteJetBound (V.degreeFamily hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
      p0 3 (CD*(d.radius y)^2) :=
    ⟨by positivity,(V.contDiffOn_degreeFamily hΩ hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)).contDiffAt
      (V.domainOpen.mem_nhds V.pointMem),hD⟩
  obtain ⟨hHi,hHa⟩ := V.higherTaylor_jet_bounds hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)
    p0 3 (CL*(d.radius y)^2) (CD*(d.radius y)^2) hLow hDegreeBound
  have hHi' : SmoothFiniteJetBound (V.forwardHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
      p0 3 (CH*(d.radius y)^2) := by simpa only [CH,add_mul] using hHi
  have hHa' : SmoothFiniteJetBound (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
      p0 3 (CH*(d.radius y)^2) := by simpa only [CH,add_mul] using hHa
  have hHF := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) _ hHi'.smooth CH (d.radius y) hCH hHi'.bound
  have hHA := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) _ hHa'.smooth CH (d.radius y) hCH hHa'.bound
  refine ⟨V,hHi',hHa',?_⟩
  intro b hb n hn
  exact ⟨(hHF b hb n hn).trans_eq (by dsimp only [CHH]),
    (hHA b hb n hn).trans_eq (by dsimp only [CHH])⟩
end ShrinkingSpheres
