import Proof.NativeFirstErrorDegreeFamily
import Proof.NativeFirstErrorAngularScaledJets
import Proof.UniformNativeTaylorAngularJets
import Proof.CoarseDegreeFamilyNaturality
import Proof.UniformNormalFrameRelativeCoframeJets
import Proof.UniformScaledLogCovectorThreeJets
import Proof.UniformNormalFrameScaledHorizontalJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The complete first-adjoint remainder and its genuine degree commutator
    have radius-gained rescaled and actual horizontal three-jets. All choices
    precede the admitted profile, frame and directional coefficient family. -/
theorem uniform_native_first_error_degree_three_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 9 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW CC : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hCC : 0 ≤ CC)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) :
    ∃ η CE CD CDH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧ 0 ≤ CD ∧ 0 ≤ CDH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF0 CA0 CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF0 CA0 CM,
      ∃ V : s.response.SymmetricAdjointDomain,∀ a : X,∀ CH : ℝ,
      ∀ C : (j : I) → RelativeCenterErrorCoefficientFamily d y a j CC CH,
        CoarseAngularFields.JetBound (s.firstErrorAngularFields C ∘
          normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
          ((0,frameVectorLinear d.frame y),0) 3 (CE*‖a‖*d.radius y) ∧
        SmoothFiniteJetBound (s.firstErrorDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK) ∘
          normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
          ((0,frameVectorLinear d.frame y),0) 3 (CD*‖a‖*d.radius y) ∧
        ∀ b : ℕ → X,(∀ j,‖b j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
          ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (b j))
            (s.firstErrorDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK)) n
            ((y,frameVectorLinear d.frame y),0)‖ ≤ CDH*‖a‖*d.radius y*(beta d.γ d.radius y)^n := by
  obtain ⟨η,BT,hη,hη1,hBT,hTaylor⟩ := uniform_native_taylor_angular_field_three_jets
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  obtain ⟨BR,hBR,hReciprocal⟩ := exists_relative_inverse_radius_factor_jet_bound 3
  obtain ⟨BQ,hBQ,hCoframe⟩ := uniform_normalFrameRelativeCoframe_higher_jets hΩ 3 (by omega) K M hK
  obtain ⟨BL,hBL,hLog⟩ := uniform_normalFrame_scaled_log_covector_three_jets hY hΩ hSub (by omega) K M Cj hK
  obtain ⟨CX,hCX,hHorizontal⟩ := uniform_normalFrame_horizontal_from_scaled_three_jets hY hΩ hSub (by omega) K M Cj hK
  let BD := BT+(CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).budget+firstRadialAngularFieldJetBudget*CQ
  let BG := 2^3*BR*boundaryGradientAngularJetBudget 3 BD*CC
  let CE := firstErrorAngularJetBudget BR (6*BT) (6*BQ) BL (6*BG)
  let CD := (12*Real.sqrt 2)*CE
  let CDH := CX*CD
  have hBR0 : 0 ≤ BR := zero_le_one.trans hBR
  have hBQ0 : 0 ≤ BQ := zero_le_one.trans hBQ
  have hBL0 : 0 ≤ BL := zero_le_one.trans hBL
  have hBD : 0 ≤ BD := by
    have hDegree := (CoarseAngularFields.ofPacket degreeCoarseAdjointPacket).budget_nonneg
    have hFirst := firstRadialAngularFieldJetBudget_nonneg
    dsimp only [BD]
    positivity
  have hBG : 0 ≤ BG := by
    have hGrad := boundaryGradientAngularJetBudget_nonneg 3 hBD
    dsimp only [BG]
    positivity
  have hCE : 0 ≤ CE := firstErrorAngularJetBudget_nonneg _ _ _ _ _ hBR0
    (mul_nonneg (by norm_num) hBT) (mul_nonneg (by norm_num) hBQ0) hBL0 (mul_nonneg (by norm_num) hBG)
  have hCD : 0 ≤ CD := by dsimp only [CD];positivity
  have hCDH : 0 ≤ CDH := mul_nonneg (zero_le_one.trans hCX) hCD
  refine ⟨η,CE,CD,CDH,hη,hη1,hCE,hCD,hCDH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  obtain ⟨V,hT⟩ := hTaylor floor hf ε hε hSmall d hd y hy CF0 CA0 CM s
  refine ⟨V,?_⟩
  intro a CH C
  let r := d.radius y
  let β := beta d.γ d.radius y
  let L := frameVectorLinear d.frame y
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  let p1 : NormalFrameRelativeParameter := ((y,L),0)
  let Φ := normalFrameRelativeScaledParameter β y
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ0 := zero_lt_one.trans_le hβ
  have hε1 : ε ≤ 1 := hSmall.trans hη1
  have hrβ : r*β ≤ 1 := by
    have hSmallR : r*β^2 ≤ ε := (hd.2.2.2.2.2 y hy).2
    have hPower : β ≤ β^2 := by nlinarith only [mul_le_mul_of_nonneg_left hβ hβ0.le]
    exact ((mul_le_mul_of_nonneg_left hPower hr.le).trans hSmallR).trans hε1
  have hrε : r ≤ ε := (radius_bounds r β floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hrr : r^2 ≤ 1 := by nlinarith only [hr.le,hr1]
  have hTaylorWeak := hT.weaken ((mul_le_mul_of_nonneg_left hrr hBT).trans_eq (mul_one _))
  have hEll : SmoothFiniteJetBound (normalFrameRelativeFirstCovector d.γ d.g₁) p1 3 CQ :=
    ⟨hCQ,s.coefficients.covectorSmooth.contDiffAt (s.coefficients.domainOpen.mem_nhds s.coefficients.pointMem),
      fun n hn => s.coefficients.firstCovectorJets (by norm_num) n hn⟩
  have hD : CoarseAngularFields.JetBound s.response.fullAdjointAngularFields p1 3 BD :=
    s.response.fullAdjointAngularFields_jet_bound p1 3 BT CQ hTaylorWeak hEll hr.le hr1
  have he (i j : I) : metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0 := by
    simpa only [L,frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have hQ (j : I) : SmoothFiniteJetBound (normalFrameRelativeCoframeValue d.γ a j) p1 3 (BQ*‖a‖) := by
    obtain ⟨hS,hJ⟩ := hCoframe d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) L he a j
    exact ⟨mul_nonneg hBQ0 (norm_nonneg _),hS,hJ⟩
  obtain ⟨hR,hRJ⟩ := hReciprocal y L
  obtain ⟨hRs,hRsJ⟩ := hReciprocal (0:X) L
  have hRB : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor p1 3 BR := ⟨hBR0,hR,hRJ⟩
  have hRsB : SmoothFiniteJetBound normalFrameRelativeInverseRadiusFactor p0 3 BR := ⟨hBR0,hRs,hRsJ⟩
  have hLogBound := hLog d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy L
  have hFields : CoarseAngularFields.JetBound (s.firstErrorAngularFields C ∘ Φ) p0 3 (CE*‖a‖*r) :=
    s.firstErrorAngularFields_scaled_three_jets C β BR BT BQ BL BD hr hβ hrβ hBR0 hBT hBQ0 hBL0 hBD hCC
      hT hD hQ hRB hRsB hLogBound
  have hΦ : ContDiff ℝ ∞ Φ := by
    rw [show Φ = normalFrameRelativeScaledParameter β y from rfl,
      normalFrameRelativeScaledParameter_affine β hβ0.ne' y]
    exact contDiff_const.add (normalFrameParameterScaleEquiv β hβ0.ne').contDiff
  have hp : Φ p0 ∈ s.centerDegreeDomain V := by
    rw [show Φ p0 = p1 from normalFrameRelativeScaledParameter_point β y L]
    exact s.centerDegreeDomain_pointMem V
  have hDegreeRaw := CoarseDegreeCompatibility.halfFamily_composition_jet_bound
    (fun p => (s.firstErrorAngularFields C p).degreeData) (s.centerDegreeDomain V) (s.centerDegreeDomain_open V)
    (s.firstErrorDegree_constraint C V hd.1.1 (zero_lt_one.trans_le hK))
    (s.contDiffOn_firstErrorDegreeData C V hY hΩ hd.1.1 (zero_lt_one.trans_le hK) hd.2.2.2.2.1)
    Φ hΦ hp hFields.degreeData
  have hDegree : SmoothFiniteJetBound (s.firstErrorDegreeFamily C V hd.1.1 (zero_lt_one.trans_le hK) ∘ Φ)
      p0 3 (CD*‖a‖*r) := by
    simpa only [NativeRelativeHorizontalTaylorData.firstErrorDegreeFamily,CD,mul_assoc] using hDegreeRaw
  have hH := hHorizontal d hd.1 floor c₀ hf hd.2.2.2.2.1 y hy
    (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) _ (CD*‖a‖*r) hDegree
  refine ⟨hFields,hDegree,?_⟩
  intro b hb n hn
  exact (hH b hb n hn).trans_eq (by dsimp only [CDH];ring)
end ShrinkingSpheres
