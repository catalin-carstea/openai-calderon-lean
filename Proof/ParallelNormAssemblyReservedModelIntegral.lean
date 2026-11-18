import Proof.ParallelNormAssemblyReservedModelCoreIntegrable
import Proof.ParallelNormAssemblyReservedModelZeroPoint
import Proof.ParallelNormAssemblyReservedModelCubicPoint
import Proof.ParallelNormAssemblyReservedParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Complete literal corrected model/potential sector, with all angular
words and both leading orientations cancelled before norms. Constants
precede profiles; the SAME arbitrary P/WF/W precede tests. -/
theorem uniform_corrected_model_potential_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    UniformCorrectedModelSectorEstimate Y Ω K ρ c₀ M Cj CF CT 2 := by
  obtain ⟨η,CL,hη,hη1,hCL,hLeading⟩ := uniform_actual_model_potential_paired_leading_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  intro CB CS CG CK hCB hCS hCG hCK
  let G := max (physicalPotentialGeneratorBudget CF) CG
  let CZ := 48*G^2*CK*(49*potentialWordEntryBudget K)
  let CC := 6*G*CK*(49*potentialWordEntryBudget K)
  have hG : 0 ≤ G := hCG.trans (le_max_right _ _)
  have hCZ : 0 ≤ CZ := by dsimp only [CZ,potentialWordEntryBudget];positivity
  have hCC : 0 ≤ CC := by dsimp only [CC,potentialWordEntryBudget];positivity
  refine ⟨1,η,36*CL+4*CC+CZ,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hε1 := hSmall.trans hη1
  have hKp := zero_lt_one.trans_le hK
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let T := correctedModelSectorComplexDensity P WF W E D 2
  let Z := fun y => modelPotentialZeroCoreDensity P W Ur y+modelPotentialZeroCoreDensity P W Ui y
  let C := fun y => modelPotentialCubicCoreDensity P W Ur y+modelPotentialCubicCoreDensity P W Ui y
  let L := fun y => ∑ k : I,∑ c : I,modelPotentialPairedLeadingComplexDensity P E k c y
  have hIT : IntegrableOn T Y := corrected_model_potential_sector_integrable P hY hSub hd hKp WF hCG hCK W E D hφ.1
  have hIZ : IntegrableOn Z Y :=
    (model_potential_zero_density_integrable P hY hSub hd hKp hCG hCK W Q hQ Ur
      (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
      (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)).add
    (model_potential_zero_density_integrable P hY hSub hd hKp hCG hCK W Q hQ Ui
      (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
      (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx))
  have hLP (k c : I) := hLeading floor hf ε hε hSmall d hd CT CG CK P W k c φ E D hφ
  have hIL : IntegrableOn L Y :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun c _ => (hLP k c).1))
  have hFrame (y : X) (hy : y ∈ Y) := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hPoint (y : X) (hy : y ∈ Y) : T y=4*(L y-C y)+Z y := by
    have hr := component_corrected_model_potential_eq hY hSub hd hKp P WF W Q hQ E Complex.reCLM D.realComponent hφ.1 hy
    have hi := component_corrected_model_potential_eq hY hSub hd hKp P WF W Q hQ E Complex.imCLM D.imagComponent hφ.1 hy
    have hPhys : T y=modelPotentialCorrectedCoreDensity P W Ur y+modelPotentialCorrectedCoreDensity P W Ui y :=
      congrArg₂ (fun x z : ℝ => x+z) hr hi
    rw [hPhys,model_potential_corrected_core_split P W Q hQ Ur hy,
      model_potential_corrected_core_split P W Q hQ Ui hy,
      model_potential_leading_core_weak_identity P W Q hQ Ur hy
        ((E.contDiff_realHigherSobolevSection _ _).differentiable (by simp) y) (hFrame y hy),
      model_potential_leading_core_weak_identity P W Q hQ Ui hy
        ((E.contDiff_imagHigherSobolevSection _ _).differentiable (by simp) y) (hFrame y hy)]
    simp only [L,C,Z,modelPotentialPairedLeadingComplexDensity,Finset.sum_add_distrib]
    dsimp only [Ur,Ui]
    ring
  have hCEq : (fun y => L y-(T y-Z y)/4)=ᵐ[volume.restrict Y] C := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hh := hPoint y hy
    linarith only [hh]
  have hIC : IntegrableOn C Y := (hIL.sub ((hIT.sub hIZ).div_const 4)).congr hCEq
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hEnergy := hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg hKp d.frame he hFrame hf hφ
  have hZBound : |∫ y in Y,Z y| ≤ CZ*ε*energySq Y d.γ d.frame d.radius φ := by
    have hDom := hEnergy.const_mul (CZ*ε)
    have hB : ∀ᵐ y ∂volume.restrict Y,‖Z y‖ ≤ (CZ*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
      rw [Real.norm_eq_abs]
      exact model_potential_zero_complex_point_bound P hd hK hf hε hε1 hCG hCK W E D hy
    have hh := norm_integral_le_of_norm_le hDom hB
    simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density,mul_assoc] using hh
  have hCBound : |∫ y in Y,C y| ≤ CC*ε*energySq Y d.γ d.frame d.radius φ := by
    have hDom := hEnergy.const_mul (CC*ε)
    have hB : ∀ᵐ y ∂volume.restrict Y,‖C y‖ ≤ (CC*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
      filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
      rw [Real.norm_eq_abs]
      exact model_potential_cubic_complex_point_bound P hY hSub hd hK hf hε hε1 hCG hCK W E D hφ.1 hy
    have hh := norm_integral_le_of_norm_le hDom hB
    simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density,mul_assoc] using hh
  have hLInt : (∫ y in Y,L y)=∑ k : I,∑ c : I,∫ y in Y,modelPotentialPairedLeadingComplexDensity P E k c y := by
    rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun c _ => (hLP k c).1))]
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finsetSum _ (fun c _ => (hLP k c).1)
  have hLBound : |∫ y in Y,L y| ≤ 9*CL*ε*energySq Y d.γ d.frame d.radius φ := by
    rw [hLInt]
    calc
      _ ≤ ∑ k : I,∑ c : I,|∫ y in Y,modelPotentialPairedLeadingComplexDensity P E k c y| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ _k : I,∑ _c : I,CL*ε*energySq Y d.γ d.frame d.radius φ :=
        Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun c _ => (hLP k c).2))
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  have hInt : (∫ y in Y,T y)=4*((∫ y in Y,L y)-(∫ y in Y,C y))+(∫ y in Y,Z y) := by
    calc
      _ = ∫ y in Y,4*(L y-C y)+Z y := integral_congr_ae (by
        filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
        exact hPoint y hy)
      _ = _ := by
        have hAdd := integral_add ((hIL.sub hIC).const_mul 4) hIZ
        simp only [Pi.sub_apply] at hAdd
        rw [hAdd,integral_const_mul,integral_sub hIL hIC]
  refine ⟨hIT,?_⟩
  change |∫ y in Y,T y| ≤ _
  rw [hInt]
  let iL := ∫ y in Y,L y
  let iC := ∫ y in Y,C y
  let iZ := ∫ y in Y,Z y
  change |4*(iL-iC)+iZ| ≤ _
  calc
    _ ≤ |4*(iL-iC)|+|iZ| := abs_add_le _ _
    _ = 4*|iL-iC|+|iZ| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)]
    _ ≤ 4*(|iL|+|iC|)+|iZ| := add_le_add (mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)) (le_refl _)
    _ ≤ 4*(9*CL*ε*energySq Y d.γ d.frame d.radius φ+CC*ε*energySq Y d.γ d.frame d.radius φ)+
        CZ*ε*energySq Y d.γ d.frame d.radius φ :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add hLBound hCBound) (by norm_num)) hZBound
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
