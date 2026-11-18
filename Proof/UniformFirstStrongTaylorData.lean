import Proof.UniformFirstCoefficientTaylor
import Proof.FirstDensityEllipticity
import Proof.AffineCoefficientJets
import Proof.UniformActualStrongInverse
import Proof.FlatCoefficientEllipticity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

/-- Actual compact coefficient jets for the scalar affine first radial model,
    with common strong inverse bounds and quadratic local C1 error. -/
theorem uniform_first_strong_taylor_data {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C P Q : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ 0 ≤ C ∧ 0 ≤ P ∧ 0 ≤ Q ∧
      (∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let a := principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y))
      let c := firstMetricDensityFactor d.γ d.g₁ y
      let r := d.radius y
      let ℓ := firstDensityCenterLinearL d y
      ∃ F F1 : SmoothCoefficientMatrix 2,
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j)) ∧
        (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => ℓ z*(1:Mat) i j)) ∧
        (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖ ≤ C ∧
        (strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).IsInvertible ∧
        ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ C ∧
        (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F1 i j) x| ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) ∧
        (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ Q*r^2) ∧
        (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ Q*r^2) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨F0,hF0,δ,CF,hδ,hCF,hFlat⟩ := exists_uniform_strongC1_neighborhood K⁻¹ K (inv_pos.mpr hKpos)
  obtain ⟨ηT,Q,hηT,hQ,hTaylor⟩ := uniform_first_coefficient_taylor
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨ηI,CI,hηI,hCI,hInverse⟩ := uniform_actual_strong_dirichlet_inverse
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,hηE,hE⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ 3 (by norm_num)
  let P := K^3*|M ⟨1,by omega⟩|
  have hP : 0 ≤ P := by dsimp [P];positivity
  refine ⟨min ηT (min ηI ηE),CI+CF,P,Q,F0,lt_min hηT (lt_min hηI hηE),
    add_nonneg hCI hCF,hP,hQ,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  dsimp only
  let H := framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ℓ := firstDensityCenterLinearL d y
  have hCenter := hd.2.1.center_mem hy
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hcBounds : c ∈ Icc K⁻¹ K := hd.1.firstMetricDensityFactor_mem_Icc hKpos hCenter
  obtain ⟨F,hRep,hInvNorm⟩ := hInverse floor hf ε hε
    (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy
  obtain ⟨F1,hRep1⟩ := exists_linear_scalar_coefficient ℓ 2
  have hEll : Elliptic (Metric.closedBall (0:X) 3) (4*K^2) H :=
    hE floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))) d hd y hy d.g₁ (by simp)
  have hKP : 1 ≤ 4*K^2 := by nlinarith only [hK,sq_nonneg (K-1)]
  have hBall3 : (ballOpens : Set X) ⊆ Metric.closedBall (0:X) 3 :=
    unitBall_subset_closedBall_two.trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hUE := ((hEll.principalCoefficient_tau hKP).mono_set hBall3).congr
    (show ∀ x ∈ (ballOpens:Set X),coefficientMatrixField 2 F x = principalCoefficient H x by
      intro x hx
      ext i j
      exact (hRep x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds)
  have hInv := strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 F hUE
  have hUE0 : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set X) (coefficientMatrixField 2 (c • F0)) c c :=
    uniformlyEllipticOn_flat_coefficientMatrix F0 c hc (fun x hx => hF0 x (unitBall_subset_closedBall_two hx))
  have hInv0 := strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity 0 (c • F0) hUE0
  have hNorm0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 (c • F0)).inverse‖ ≤ CF := by
    apply hFlat c hcBounds (c • F0) c c hUE0
    · intro i j x hx
      simp only [sub_self]
      change |(0:ℝ)| ≤ δ
      simpa using hδ.le
    · intro i j x hx
      simp only [sub_self]
      change ‖fderiv ℝ (fun _ : X => (0:ℝ)) x‖ ≤ δ
      simpa using hδ.le
  have hLn : ‖ℓ‖ ≤ P := by
    have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
    have hEn := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
    have hD := (hd.1.firstMetricDensityFactor_jet_bounds hΩ hKpos (by omega) hCenter).1
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hD hEn (norm_nonneg _) (by positivity)).trans_eq (by dsimp [P];ring))
  obtain ⟨hVal1,hDeriv1⟩ := linear_scalar_coefficient_local_bounds F1 ℓ P hP hLn hRep1
  have hEllOpen : Elliptic (Metric.ball (0:X) 3) (4*K^2) H :=
    ⟨fun i j => (hEll.1 i j).mono Metric.ball_subset_closedBall,
      fun x hx => hEll.2 x (Metric.ball_subset_closedBall hx)⟩
  have hAD (i j : I) (x : X) (hx : x ∈ (ballOpens : Set X)) :
      DifferentiableAt ℝ (fun z => principalCoefficient H z i j) x := by
    have hx3 : x ∈ Metric.ball (0:X) 3 := by
      have hh := unitBall_subset_closedBall_two hx
      change dist x 0 < 3
      change dist x 0 ≤ 2 at hh
      linarith
    exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (hEllOpen.contDiffOn_principalCoefficient (by positivity)) i) j).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx3)).differentiableAt (by simp)
  have hT (x : X) (hx : x ∈ (ballOpens : Set X)) (i j : I) :=
    hTaylor floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy x (unitBall_subset_closedBall_two hx) i j
  obtain ⟨hValR,hDerivR⟩ := coefficient_affine_remainder_local_bounds F F0 F1 c (d.radius y) Q ℓ
    hRep hF0 hRep1 hAD hT
  exact ⟨F,F1,hRep,hRep1,hInv,hInvNorm.trans (le_add_of_nonneg_right hCF),hInv0,
    hNorm0.trans (le_add_of_nonneg_left hCI),hVal1,hDeriv1,hValR,hDerivR⟩

end ShrinkingSpheres
