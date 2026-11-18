import Proof.FirstDerivativeScalarData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Closed common full first-base coefficient data. All constants, fixed
cutoffs and budgets precede every admitted profile and physical endpoint
choice. One native packet and generator family work for any selected
PhysicalPrincipalData at the point. -/
theorem uniform_full_first_derivative_scalar_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CA CM CQ CI CW CG CQB CZB : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
    ∃ Q0 : SmoothCoefficientJets 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ CQ ∧ 0 ≤ CI ∧ 0 ≤ CW ∧ 1 ≤ CG ∧ 0 ≤ CQB ∧ 0 ≤ CZB ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1) ∧
      (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,
      ∃ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ T : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      ∀ CDF CDT : ℝ,∀ D : PhysicalPrincipalData Y d CDF CDT,
      Nonempty (FirstDerivativeScalarData T D CQB CZB (ε/beta d.γ d.radius y)) := by
  obtain ⟨ηT,CF,CA,CM,CQ,CI,CW,F0,hηT,hηT1,hCF,hCA,hCM,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_native_relative_horizontal_taylor_data hY hΩ hSub (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CC,CH,hηC,hηC1,hCC,hCH,hCoefficients⟩ :=
    uniform_relative_center_error_coefficient_families hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨Q0,hQ0⟩ := exists_unit_boundary_coefficient
  obtain ⟨ηG,CG,hηG,hηG1,hCG,hGenerator⟩ := uniform_native_taylor_generator_bounds hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ CQ CI CW (zero_le_one.trans hCQ) hCI hCW F0 hF0 Q0 hQ0
  let CQB := fullFirstScalarBudget Q0 K (M 0) CC
  let CZB := fullFirstBoundedBudget Q0 CQ K (M 0) (M ⟨1,by omega⟩) CC
  refine ⟨min ηT (min ηC ηG),CF,CA,CM,CQ,CI,CW,CG,CQB,CZB,F0,Q0,
    lt_min hηT (lt_min hηC hηG),(min_le_left _ _).trans hηT1,hCQ,hCI,hCW,hCG,
    fullFirstScalarBudget_nonneg Q0 K (M 0) CC hK (zero_le_one.trans hCC),
    fullFirstBoundedBudget_nonneg Q0 CQ K (M 0) (M ⟨1,by omega⟩) CC hK (zero_le_one.trans hCC),
    hF0,hQ0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  have hεT := hSmall.trans (min_le_left _ _)
  have hεC := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεG := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s⟩ := hNative floor hf ε hε hεT d hd y hy
  obtain ⟨T⟩ := hGenerator floor hf ε hε hεG d hd y hy CF CA CM s
  let C : (a j : I) → RelativeCenterErrorCoefficientFamily d y (axis a) j CC CH :=
    fun a j => Classical.choice (hCoefficients floor hf ε hε hεC d hd y hy (axis a) j)
  refine ⟨s,T,?_⟩
  intro CDF CDT D
  exact T.full_first_derivative_scalar_data (by omega) hd hY hΩ hSub hK hf hε (hεT.trans hηT1)
    (zero_le_one.trans hCQ) hy hF0 Q0 hQ0 D (zero_le_one.trans hCC) C
end ShrinkingSpheres
