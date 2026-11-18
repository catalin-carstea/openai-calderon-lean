import Proof.UniformPhysicalFirstCoordinateData
import Proof.FullFirstBalancedEndpoints
import Proof.EffectiveFirstScalarDriftCommutator
import Proof.UniformPhysicalFirstCovariantCoordinateTwoJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The literal complete effective first higher coefficient has the
original uniform epsilon/beta norm. Genuine inclusion injectivity
identifies it with the already controlled smooth endpoint family. -/
theorem uniform_effective_first_higher_endpoint_data
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ b : I,
        ContDiffOn ℝ ∞ (P.firstCovariantCoordinateHigherL b) Y ∧
        ∀ y ∈ Y,‖P.firstCovariantCoordinateHigherL b y‖ ≤ CE*ε/beta d.γ d.radius y := by
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hData⟩ := uniform_physical_first_coordinate_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hηB1,hBalanced⟩ := uniform_full_first_derivative_balanced_endpoints
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  refine ⟨min ηD ηB,CD+CW,lt_min hηD hηB,(min_le_left _ _).trans hηD1,add_nonneg hCD hCW,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 := hSmall.trans ((min_le_left _ _).trans hηD1)
  obtain ⟨H,hH⟩ := hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  have hW := hWeight floor hf ε hε hε1 d hd
  have hSame (b : I) (y : X) (hy : y ∈ Y) : P.firstDerivativeCoordinateHigherL y b=H b y := by
    apply ContinuousLinearMap.ext
    intro u
    apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
    have hActual := DFunLike.congr_fun
      (P.firstDerivativeCoordinate_balanced y
        (hBalanced floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy) b) u
    have hChosen := DFunLike.congr_fun ((hH b).2.2 y hy).1 u
    exact hActual.trans hChosen.symm
  intro b
  have hHigh : ContDiffOn ℝ ∞ (fun y => P.firstDerivativeCoordinateHigherL y b) Y :=
    (hH b).2.1.congr (fun y hy => hSame b y hy)
  refine ⟨hHigh.sub ((hW b).1.smul contDiffOn_const),?_⟩
  intro y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hBase : ‖P.firstDerivativeCoordinateHigherL y b‖ ≤ CD*ε/beta d.γ d.radius y := by
    rw [hSame b y hy]
    exact ((hH b).2.2 y hy).2.2.1
  have hScalar : ‖scalarPrincipalConnectionWeight d b y •
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)‖ ≤ CW*ε/beta d.γ d.radius y := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ |scalarPrincipalConnectionWeight d b y| * 1 := mul_le_mul_of_nonneg_left
        (norm_sphereSobolevInclusionL_le _ _ _) (abs_nonneg _)
      _ = |scalarPrincipalConnectionWeight d b y| := mul_one _
      _ ≤ CW*ε/(beta d.γ d.radius y)^2 := ((hW b).2 y hy 0 0).1
      _ ≤ CW*ε/beta d.γ d.radius y := div_le_div_of_nonneg_left
        (mul_nonneg hCW hε) (zero_lt_one.trans_le hβ) (by nlinarith only [hβ])
  exact ((norm_sub_le _ _).trans (add_le_add hBase hScalar)).trans_eq (by ring)

end ShrinkingSpheres
