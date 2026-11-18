import Proof.ParallelNormAssemblyReservedModelCoreSplit
import Proof.HalfCovariantEnergyControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma model_potential_zero_density_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    |modelPotentialZeroCoreDensity P W U y| ≤
      (48*G^2*CK*(49*potentialWordEntryBudget K))*ε*beta d.γ d.radius y*metricDensity d.γ y*
        ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖^2 := by
  have hh := model_zero_potential_mixed_point_bound P hd hK hf hε hε1 hy hCG hCK (W y hy) (U y)
  have hμ : 0 ≤ 4*metricDensity d.γ y := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  simp only [modelPotentialZeroCoreDensity,dite_eq_left hy,abs_mul,abs_of_nonneg hμ]
  exact (mul_le_mul_of_nonneg_left hh hμ).trans_eq (by ring)

/-- The complete angular model-zero pair is controlled by the mass part
of the SAME original physical energy, with both complex components. -/
theorem model_potential_zero_complex_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    {y : X} (hy : y ∈ Y) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    let C := 48*G^2*CK*(49*potentialWordEntryBudget K)
    |modelPotentialZeroCoreDensity P W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
      modelPotentialZeroCoreDensity P W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y| ≤
      C*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let C := 48*G^2*CK*(49*potentialWordEntryBudget K)
  have hC : 0 ≤ C := by dsimp only [C,potentialWordEntryBudget];positivity
  have hFrame (x : X) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  let nr := ‖D.realErrorMass y‖
  let ni := ‖D.imagErrorMass y‖
  have hNR : ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num) y)‖=nr := by
    rw [E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)]
    exact E.norm_realSobolevSection _ _ y
  have hNI : ‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num) y)‖=ni := by
    rw [E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num)]
    exact E.norm_imagSobolevSection _ _ y
  have hMass : μ*(β*nr^2+β*ni^2) ≤ physicalEnergyDensity d.γ d.frame d.radius φ y := by
    have hL : β*nr^2+β*ni^2 ≤ errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y) := by
      simp only [errorEnergy]
      have hβ : 0 ≤ β⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hR := mul_nonneg hβ (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => sq_nonneg ‖D.realErrorHorizontal y i‖))
      have hI := mul_nonneg hβ (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => sq_nonneg ‖D.imagErrorHorizontal y i‖))
      dsimp only [nr,ni]
      linarith only [hR,hI]
    exact (mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)).trans (D.errorEnergy_components_le hFrame hy)
  have hr := model_potential_zero_density_point_bound P hd hK hf hε hε1 hCG hCK W
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) hy
  have hi := model_potential_zero_density_point_bound P hd hK hf hε hε1 hCG hCK W
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) hy
  rw [hNR] at hr
  rw [hNI] at hi
  calc
    _ ≤ |modelPotentialZeroCoreDensity P W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y|+
        |modelPotentialZeroCoreDensity P W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y| := abs_add_le _ _
    _ ≤ C*ε*β*μ*nr^2+C*ε*β*μ*ni^2 := add_le_add hr hi
    _ = (C*ε)*(μ*(β*nr^2+β*ni^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hMass (mul_nonneg hC hε)

end ShrinkingSpheres.ParallelEnergy
