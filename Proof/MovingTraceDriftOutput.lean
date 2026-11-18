import Proof.MovingTraceDriftDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Both parts of the split trace have genuine physical output realizations,
    with the test's original compact center support. -/
theorem Admissible.exists_principal_drift_outputs {Y Ω : Set X} (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {φ : Field} (hφ : Test Y d.γ d.frame φ) :
    ∃ PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ),
      Nonempty (PhysicalOutputRealization Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ)) := by
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have h₂ : Elliptic Y K d.g₂ := ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun y hy => hd.1.2.2.1.2 y (hSub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hDensity := (h.contDiffOn_density hK).continuousOn
  obtain ⟨S,hS,hSY,hZero⟩ := hφ.2.1
  have hPrincipal := smoothNear_principalMovingTrace hY h h₂ hK hd.2.2.2.2.1.1 hd.2.2.2.1 hφ.1
  have hDrift := smoothNear_movingTraceDrift hY h h₂ hK hd.2.2.2.2.1.1 hd.2.2.2.1 hφ.1
  obtain ⟨PP⟩ := exists_physicalOutputRealization hY d.frame he hFrame hDensity hPrincipal
    ⟨S,hS,hSY,fun y hy w hw => principalMovingTrace_zero_of_support hY h hK d.frame he hFrame
      hd.2.2.2.1 hd.2.2.1 hφ.1 S hS.isClosed hZero hy w hw⟩
  obtain ⟨PD⟩ := exists_physicalOutputRealization hY d.frame he hFrame hDensity hDrift
    ⟨S,hS,hSY,fun y hy w hw => movingTraceDrift_zero_of_support hY h hK d.frame he hFrame
      hd.2.2.2.1 hd.2.2.1 hφ.1 S hS.isClosed hZero hy w hw⟩
  exact ⟨PP,⟨PD⟩⟩

theorem movingTraceDrift_output_bound_of_density {Y : Set X} (hY : IsOpen Y) {K : ℝ} {d : Data}
    (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun y => d.frame y i) Y)
    (hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hf : 1 ≤ floor) {φ : Field} (hφ : Test Y d.γ d.frame φ) (CD : ℝ) (hCD : 0 ≤ CD)
    (hBound : ∀ y ∈ Y,floor^2*(metricDensity d.γ y*
      fiberSq d.frame y (fun w => movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ (y,w))) ≤
        CD^2*physicalEnergyDensity d.γ d.frame d.radius φ y)
    (PD : PhysicalOutputRealization Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ)) :
    ‖PD.output‖ ≤ CD/floor*energyNorm Y d φ := by
  have hIntegrable := (hp.integrableOn_physicalEnergyDensity hY h hK d.frame he hFrame hf hφ).const_mul (CD^2)
  have hInt : (∫ y in Y,floor^2*(metricDensity d.γ y*
      fiberSq d.frame y (fun w => movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ (y,w)))) ≤
      ∫ y in Y,CD^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall (fun y => mul_nonneg (sq_nonneg floor)
        (mul_nonneg (Real.sqrt_nonneg _) (fiberSq_nonneg _ _ _)))) hIntegrable
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact hBound y hy
  rw [integral_const_mul,integral_const_mul,← energySq_eq_integral_density] at hInt
  change floor^2*outputSq Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ) ≤
    CD^2*energySq Y d.γ d.frame d.radius φ at hInt
  rw [← PD.normSq hY (h.contDiffOn_density hK).continuousOn,← energyNorm_sq] at hInt
  have hfpos : 0 < floor := zero_lt_one.trans_le hf
  have hSq : (floor*‖PD.output‖)^2 ≤ (CD*energyNorm Y d φ)^2 := by nlinarith only [hInt]
  have hNorm := (sq_le_sq₀ (mul_nonneg hfpos.le (norm_nonneg _)) (mul_nonneg hCD (Real.sqrt_nonneg _))).mp hSq
  exact ((le_div_iff₀ hfpos).mpr (show ‖PD.output‖*floor ≤ CD*energyNorm Y d φ by simpa only [mul_comm,energyNorm] using hNorm)).trans_eq (by ring)

/-- The drift is a uniformly absorbable energy remainder using only its
    admitted zeroth-order bound; its derivatives never enter the constant. -/
theorem uniform_movingTraceDrift_output_bound {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CD : ℝ,0 < η ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,Test Y d.γ d.frame φ →
      ∀ PD : PhysicalOutputRealization Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ),
        ‖PD.output‖ ≤ CD/floor*energyNorm Y d φ := by
  have hTheorem := uniform_movingTraceDrift_density_bound hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η,CD,hη,hCD,hProduce⟩ := hTheorem
  refine ⟨η,CD,hη,hCD,?_⟩
  intro floor hf ε hε hSmall d hd φ hφ PD
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have h : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0 :=
    fun y hy => hd.1.2.2.2.2.2.2.2 y (hSub hy)
  exact movingTraceDrift_output_bound_of_density hY h (zero_lt_one.trans_le hK) he hFrame hd.2.2.2.2.1 hf hφ CD hCD
    (fun y hy => hProduce floor hf ε hε hSmall d hd y hy φ hφ.1) PD

end ShrinkingSpheres
