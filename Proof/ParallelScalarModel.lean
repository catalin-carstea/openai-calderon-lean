import Proof.ParallelScalarModelEstimatePackets
import Proof.ParallelScalarModelIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

lemma scalar_model_three_sector_triangle (l z f BL BZ BF : ℝ)
    (hL : |4*l| ≤ BL) (hZ : |z| ≤ BZ) (hF : |f| ≤ BF) :
    |4*(l+z-f)| ≤ BL+4*BZ+4*BF := by
  calc
    _ = |(4*l+4*z)-4*f| := congrArg abs (by ring)
    _ ≤ |4*l+4*z|+|4*f| := abs_sub _ _
    _ ≤ |4*l|+|4*z|+|4*f| := add_le_add (abs_add_le _ _) (le_refl |4*f|)
    _ = |4*l|+4*|z|+4*|f| := by simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤4)]
    _ ≤ _ := add_le_add (add_le_add hL (mul_le_mul_of_nonneg_left hZ (by norm_num)))
      (mul_le_mul_of_nonneg_left hF (by norm_num))

/-- The complete literal corrected model/scalar cross term, including
factor four, the SAME defect source, arbitrary fixed coherent packets,
and both actual test components, has the original uniform energy bound. -/
theorem uniform_corrected_model_scalar_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    ∀ CB CS CG CK : ℝ,0 ≤ CB → 0 ≤ CS → 0 ≤ CG → 0 ≤ CK →
    ∃ B η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,Test Y d.γ d.frame φ →
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
        IntegrableOn (correctedModelScalarComplexDensity P WF W E D) Y ∧
        |∫ y in Y,correctedModelScalarComplexDensity P WF W E D y| ≤
          C*ε*energySq Y d.γ d.frame d.radius φ := by
  intro CB CS CG CK hCB hCS hCG hCK
  let RB := Classical.choice (scalar_model_raising_budget_exists hY hΩ (by omega) K ρ c₀ M Cj hK)
  let ZB := Classical.choice (scalar_model_zero_weight_budget_exists hY hΩ hSub (by omega) K ρ c₀ M Cj hK)
  let LE := Classical.choice (scalar_model_leading_estimate_exists hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)
  let ZE := Classical.choice (scalar_model_degree_estimate_exists hY hΩ hSub hm K ρ c₀ M Cj hK hρ RB ZB)
  let FE := Classical.choice (scalar_model_defect_estimate_exists hY hΩ hSub hm K ρ c₀ M Cj hK hρ RB)
  let AV := Classical.choice (scalar_model_adjoint_higher_availability_exists hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF CT)
  let eta := min LE.eta AV.eta
  let C := LE.C+4*ZE.C+4*FE.C
  have hEta : 0 < eta := lt_min LE.eta_pos AV.eta_pos
  have hEta1 : eta ≤ 1 := (min_le_left _ _).trans LE.eta_le_one
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (add_nonneg LE.C_nonneg (mul_nonneg (by norm_num) ZE.C_nonneg))
      (mul_nonneg (by norm_num) FE.C_nonneg)
  refine ⟨1,eta,C,hEta,hEta1,hC,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  by_cases hEmpty : Y=∅
  · subst Y
    have hNonneg : 0 ≤ C*ε*energySq ∅ d.γ d.frame d.radius φ :=
      mul_nonneg (mul_nonneg hC hε) (energySq_nonneg _ _ _ _ _)
    simpa using hNonneg
  obtain ⟨y0,hy0⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hε1 := hSmall.trans hEta1
  obtain ⟨A,hA⟩ := AV.actual floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd P
  have hAG := fun j : I => hA y0 hy0 j
  have hL := LE.actual floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd P φ E D hφ
  have hZ := ZE.actual floor hf ε hε hε1 d hd A hAG φ E D hφ
  have hF := FE.actual floor hf ε hε hε1 d hd φ E D hφ
  simp only [one_mul] at hZ hF
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let L := fun y => scalarModelLeadingDensity d Ur y+scalarModelLeadingDensity d Ui y
  let Z := fun y => scalarModelDegreeDensity d Ur y+scalarModelDegreeDensity d Ui y
  let F := fun y => scalarModelDefectPairDensity d Ur y+scalarModelDefectPairDensity d Ui y
  change IntegrableOn L Y ∧ |4*(∫ y in Y,L y)| ≤ LE.C*ε*energySq Y d.γ d.frame d.radius φ at hL
  change IntegrableOn Z Y ∧ |∫ y in Y,Z y| ≤ ZE.C*ε*energySq Y d.γ d.frame d.radius φ at hZ
  change IntegrableOn F Y ∧ |∫ y in Y,F y| ≤ FE.C*ε*energySq Y d.γ d.frame d.radius φ at hF
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hEq : correctedModelScalarComplexDensity P WF W E D =ᵐ[volume.restrict Y]
      (fun y => 4*(L y+Z y-F y)) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hLiteral := correctedModelScalarComplexDensity_eq hY hSub hd (zero_lt_one.trans_le hK) P WF W E D hφ.1 hy
    change correctedModelScalarComplexDensity P WF W E D y=
      scalarModelCorrectedDensity d Ur y+scalarModelCorrectedDensity d Ui y at hLiteral
    have hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0 :=
      hd.1.2.2.2.2.2.2.2 y (hSub hy)
    have hR := (scalarModelCorrectedDensity_half_eq hY hSub hd (zero_lt_one.trans_le hK) Q hQ Ur
      (E.contDiff_realHigherSobolevSection _ _) hy).trans (scalarModelHalfCorrectedDensity_split d Ur y hFrame)
    have hI := (scalarModelCorrectedDensity_half_eq hY hSub hd (zero_lt_one.trans_le hK) Q hQ Ui
      (E.contDiff_imagHigherSobolevSection _ _) hy).trans (scalarModelHalfCorrectedDensity_split d Ui y hFrame)
    calc
      _ = scalarModelCorrectedDensity d Ur y+scalarModelCorrectedDensity d Ui y := hLiteral
      _ = 4*(scalarModelLeadingDensity d Ur y+scalarModelDegreeDensity d Ur y-scalarModelDefectPairDensity d Ur y)+
          4*(scalarModelLeadingDensity d Ui y+scalarModelDegreeDensity d Ui y-scalarModelDefectPairDensity d Ui y) :=
        congrArg₂ (fun a b : ℝ => a+b) hR hI
      _ = _ := by dsimp only [L,Z,F];ring
  have hInt := correctedModelScalarComplexDensity_integrableOn hY hSub hd (zero_lt_one.trans_le hK) P WF W E D hφ.1
  have hIntegral : (∫ y in Y,correctedModelScalarComplexDensity P WF W E D y)=
      4*((∫ y in Y,L y)+(∫ y in Y,Z y)-(∫ y in Y,F y)) := by
    rw [integral_congr_ae hEq,integral_const_mul]
    have hLZ : IntegrableOn (fun y => L y+Z y) Y := hL.1.add hZ.1
    rw [integral_sub hLZ hF.1,integral_add hL.1 hZ.1]
  refine ⟨hInt,?_⟩
  rw [hIntegral]
  exact (scalar_model_three_sector_triangle _ _ _ _ _ _ hL.2 hZ.2 hF.2).trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres.ParallelEnergy
