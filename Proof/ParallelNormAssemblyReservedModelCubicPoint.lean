import Proof.ParallelNormAssemblyReservedModelLeadingWeak
import Proof.ParallelNormAssemblyReservedCubicAdjointBound
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

lemma model_potential_cubic_density_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    let CB := 2*G*CK*(49*potentialWordEntryBudget K)
    let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
    |modelPotentialCubicCoreDensity P W U y| ≤ CB*ε*metricDensity d.γ y*
      ∑ i : I,halfCovariantDirectionEnergy d U3 y (beta d.γ d.radius y) (d.frame y i) := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CB := 2*G*CK*(49*potentialWordEntryBudget K)
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  have hEach (i : I) := actual_potential_cubic_transposed_pair_point_bound P hd hK hf hε hε1 hy hCG hCK
    (W y hy) i (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i)) (U3 y)
  have hE (i : I) : |sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i)))
      (cubicWordAdjointCommutatorValue P (W y hy) (.inr (.inl i))
        (PhysicalPrincipalData.potentialWordCoefficient d y) (U3 y))| ≤
      CB*ε*halfCovariantDirectionEnergy d U3 y (beta d.γ d.radius y) (d.frame y i) := by
    have hh := hEach i
    rw [cubic_word_commutator_dual_adjoint P hy (W y hy),five_half_covariant_derivative_to_half d U y (d.frame y i) hU] at hh
    simpa only [five_half_covariant_derivative_to_half d U y (d.frame y i) hU,halfCovariantDirectionEnergy,U3,CB,G] using hh
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  simp only [modelPotentialCubicCoreDensity,dite_eq_left hy,abs_mul,abs_of_nonneg hμ]
  calc
    _ ≤ metricDensity d.γ y*(∑ i : I,|sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y (d.frame y i)))
        (cubicWordAdjointCommutatorValue P (W y hy) (.inr (.inl i))
          (PhysicalPrincipalData.potentialWordCoefficient d y) (U3 y))|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hμ
    _ ≤ metricDensity d.γ y*(∑ i : I,CB*ε*halfCovariantDirectionEnergy d U3 y (beta d.γ d.radius y) (d.frame y i)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hE i)) hμ
    _ = _ := by rw [←Finset.mul_sum];ring

/-- Both complex cubic remainders are bounded with the original H1/2
horizontal and H3/2 mass weights, without a frame derivative norm. -/
theorem model_potential_cubic_complex_point_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CG CK : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) :
    let G := max (physicalPotentialGeneratorBudget CF) CG
    |modelPotentialCubicCoreDensity P W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
      modelPotentialCubicCoreDensity P W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y| ≤
      (6*G*CK*(49*potentialWordEntryBudget K))*ε*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CB := 2*G*CK*(49*potentialWordEntryBudget K)
  have hCB : 0 ≤ CB := by have hG := hCG.trans (le_max_right (physicalPotentialGeneratorBudget CF) CG);dsimp only [CB,potentialWordEntryBudget];positivity
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let U3r := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let U3i := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  let β := beta d.γ d.radius y
  let μ := metricDensity d.γ y
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame (x : X) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hR (i : I) : ‖halfSectionCovariantDerivativeL d U3r y (d.frame y i)‖=‖D.realErrorHorizontal y i‖ := by
    simpa only [U3r,HarmonicTestExpansion.realSobolevSection,Complex.reCLM_apply,AngularModelData.realErrorHorizontal]
      using D.realComponent.norm_half_covariant_section hY hg (zero_lt_one.trans_le hK) he hFrame hφ hy i
  have hI (i : I) : ‖halfSectionCovariantDerivativeL d U3i y (d.frame y i)‖=‖D.imagErrorHorizontal y i‖ := by
    simpa only [U3i,HarmonicTestExpansion.imagSobolevSection,Complex.imCLM_apply,AngularModelData.imagErrorHorizontal]
      using D.imagComponent.norm_half_covariant_section hY hg (zero_lt_one.trans_le hK) he hFrame hφ hy i
  have hMR : ‖U3r y‖=‖D.realErrorMass y‖ := E.norm_realSobolevSection _ _ y
  have hMI : ‖U3i y‖=‖D.imagErrorMass y‖ := E.norm_imagSobolevSection _ _ y
  have hUR : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ur x))=U3r :=
    funext (E.realHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hUI : (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (Ui x))=U3i :=
    funext (E.imagHigherSobolevSection_inclusion _ _ _ (by norm_num) (by norm_num))
  have hr := model_potential_cubic_density_point_bound P hd hK hf hε hε1 hCG hCK W Ur hy
    ((E.contDiff_realHigherSobolevSection _ _).differentiable (by simp) y)
  have hi := model_potential_cubic_density_point_bound P hd hK hf hε hε1 hCG hCK W Ui hy
    ((E.contDiff_imagHigherSobolevSection _ _).differentiable (by simp) y)
  rw [hUR] at hr
  rw [hUI] at hi
  let Er := ∑ i : I,halfCovariantDirectionEnergy d U3r y β (d.frame y i)
  let Ei := ∑ i : I,halfCovariantDirectionEnergy d U3i y β (d.frame y i)
  have hEn : μ*(Er+Ei) ≤ 3*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    have hB : Er+Ei ≤ 3*(errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y)) := by
      simp only [Er,Ei,halfCovariantDirectionEnergy,hR,hI,hMR,hMI,Finset.sum_add_distrib,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,errorEnergy]
      have hβ : 0 ≤ β⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      have hXR := mul_nonneg hβ (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => sq_nonneg ‖D.realErrorHorizontal y i‖))
      have hXI := mul_nonneg hβ (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset I)) => sq_nonneg ‖D.imagErrorHorizontal y i‖))
      nlinarith only [hXR,hXI]
    have hh : 3*(μ*(errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y))) ≤
        3*physicalEnergyDensity d.γ d.frame d.radius φ y :=
      mul_le_mul_of_nonneg_left (D.errorEnergy_components_le hFrame hy) (by norm_num : (0:ℝ) ≤ 3)
    have hμ : 0 ≤ μ := Real.sqrt_nonneg _
    exact (mul_le_mul_of_nonneg_left hB hμ).trans ((le_of_eq (by ring)).trans hh)
  calc
    _ ≤ |modelPotentialCubicCoreDensity P W Ur y|+|modelPotentialCubicCoreDensity P W Ui y| := abs_add_le _ _
    _ ≤ CB*ε*μ*Er+CB*ε*μ*Ei := add_le_add hr hi
    _ = (CB*ε)*(μ*(Er+Ei)) := by ring
    _ ≤ (CB*ε)*(3*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEn (mul_nonneg hCB hε)
    _ = _ := by dsimp only [CB];ring

end ShrinkingSpheres.ParallelEnergy
