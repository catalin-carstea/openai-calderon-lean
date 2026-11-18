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

/-- The literal complete effective first low coefficient retains the
original uniform epsilon/beta bound and actual smoothness. -/
theorem uniform_effective_first_low_endpoint_data
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ b : I,
        ContDiffOn ℝ ∞ (P.firstCovariantCoordinateHalfL b) Y ∧
        ∀ y ∈ Y,‖P.firstCovariantCoordinateHalfL b y‖ ≤ CE*ε/beta d.γ d.radius y := by
  obtain ⟨ηD,CD,hηD,hηD1,hCD,hData⟩ := uniform_physical_first_coordinate_data
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  refine ⟨ηD,CD+CW,hηD,hηD1,add_nonneg hCD hCW,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P
  have hε1 := hSmall.trans hηD1
  obtain ⟨H,hH⟩ := hData floor hf ε hε hSmall d hd CF CT P
  have hW := hWeight floor hf ε hε hε1 d hd
  intro b
  refine ⟨(hH b).1.sub ((hW b).1.smul contDiffOn_const),?_⟩
  intro y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hBase : ‖P.firstDerivativeCoordinateHalfL y b‖ ≤ CD*ε/beta d.γ d.radius y :=
    ((hH b).2.2 y hy).2.1
  have hScalar : ‖scalarPrincipalConnectionWeight d b y •
      sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)‖ ≤ CW*ε/beta d.γ d.radius y := by
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
