import Proof.ParallelModelFirstLeadingBound
import Proof.ParallelModelFirstZeroBound
import Proof.ParallelModelFirstDefectIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma model_first_three_sector_triangle (l z f BL BZ BF : ℝ)
    (hL : |l| ≤ BL) (hZ : |z| ≤ BZ) (hF : |f| ≤ BF) :
    |4*(l+z-f)| ≤ 4*(BL+BZ+BF) := by
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ |l+z|+|f| := abs_sub _ _
    _ ≤ |l|+|z|+|f| := add_le_add (abs_add_le l z) (le_refl |f|)
    _ ≤ _ := add_le_add (add_le_add hL hZ) hF

/-- Complete literal corrected model/first cross term, with factor four,
SAME model defect, full effective B and its actual physical true adjoint,
ANY compatible fixed WF/W, and the original frozen physical energy. -/
theorem uniform_corrected_model_first_integral_bound {Y Ω : Set X}
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
        IntegrableOn (correctedModelFirstComplexDensity P WF W E D) Y ∧
        |∫ y in Y,correctedModelFirstComplexDensity P WF W E D y| ≤
          C*ε*energySq Y d.γ d.frame d.radius φ := by
  intro CB CS CG CK hCB hCS hCG hCK
  obtain ⟨ηL,CL,hηL,hηL1,hCL,hLeading⟩ := uniform_model_first_leading_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB
  obtain ⟨ηZ,CZ,hηZ,hηZ1,hCZ,hZero⟩ := uniform_model_first_zero_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB CG CK CF hCB hCG hCK
  obtain ⟨ηF,CFd,hηF,hηF1,hCFd,hDefect⟩ := uniform_model_first_defect_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB CG CK hCB hCG hCK
  let FB := Classical.choice (first_self_leading_forward_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ)
  let eta := min (min ηL ηZ) (min ηF FB.eta)
  let C := 4*(CL+CZ+CFd)
  have hEta : 0 < eta := lt_min (lt_min hηL hηZ) (lt_min hηF FB.eta_pos)
  have hEta1 : eta ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans hηL1)
  have hC : 0 ≤ C := by dsimp only [C];positivity
  refine ⟨1,eta,C,hEta,hEta1,hC,?_⟩
  intro floor hf ε hε hSmall d hd P WF W φ hφ E D
  have hSL : ε ≤ ηL := hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hSZ : ε ≤ ηZ := hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hSF : ε ≤ ηF := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSP : ε ≤ FB.eta := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL := hLeading floor hf ε hε hSL d hd CF CT CS CG CK P WF W φ E D hφ
  have hZ := hZero floor hf ε hε hSZ d hd CT CS P WF W φ E D hφ
  have hF := hDefect floor hf ε hε hSF d hd CF CT CS P WF W φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let L := fun y => modelFirstLeadingDensity P WF Ur y+modelFirstLeadingDensity P WF Ui y
  let Z := fun y => modelFirstZeroDensity P WF Ur y+modelFirstZeroDensity P WF Ui y
  let F := fun y => modelFirstDefectDensity P WF W Ur y+modelFirstDefectDensity P WF W Ui y
  change IntegrableOn L Y ∧ |∫ y in Y,L y| ≤ CL*ε*energySq Y d.γ d.frame d.radius φ at hL
  change IntegrableOn Z Y ∧ |∫ y in Y,Z y| ≤ CZ*ε*energySq Y d.γ d.frame d.radius φ at hZ
  change IntegrableOn F Y ∧ |∫ y in Y,F y| ≤ CFd*ε*energySq Y d.γ d.frame d.radius φ at hF
  have hP (b : I) (y : X) (hy : y ∈ Y) := P.firstCovariantCoordinateHigherL_balanced b y
    (FB.raw floor hf ε hε hSP d hd CF CT P y hy b)
  have hEq : correctedModelFirstComplexDensity P WF W E D =ᵐ[volume.restrict Y]
      (fun y => 4*(L y+Z y-F y)) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    have hLiteral := correctedModelFirstComplexDensity_eq hY hSub hd (zero_lt_one.trans_le hK) P WF W E D hφ.1 hy
    change correctedModelFirstComplexDensity P WF W E D y=
      modelFirstCorrectedDensity P WF W Ur y+modelFirstCorrectedDensity P WF W Ui y at hLiteral
    have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
    have hR := modelFirstCorrectedDensity_split hY hd P WF W Ur hy
      ((E.contDiff_realHigherSobolevSection _ _).differentiable (by simp) y) hFrame (fun b => hP b y hy)
    have hI := modelFirstCorrectedDensity_split hY hd P WF W Ui hy
      ((E.contDiff_imagHigherSobolevSection _ _).differentiable (by simp) y) hFrame (fun b => hP b y hy)
    rw [hLiteral,hR,hI]
    dsimp only [L,Z,F]
    ring
  have hLZ : IntegrableOn (fun y => L y+Z y) Y := hL.1.add hZ.1
  have hR : IntegrableOn (fun y => 4*(L y+Z y-F y)) Y := (hLZ.sub hF.1).const_mul 4
  have hIntegral : (∫ y in Y,correctedModelFirstComplexDensity P WF W E D y)=
      4*((∫ y in Y,L y)+(∫ y in Y,Z y)-(∫ y in Y,F y)) := by
    rw [integral_congr_ae hEq,integral_const_mul,integral_sub hLZ hF.1,integral_add hL.1 hZ.1]
  refine ⟨hR.congr hEq.symm,?_⟩
  rw [hIntegral]
  exact (model_first_three_sector_triangle _ _ _ _ _ _ hL.2 hZ.2 hF.2).trans_eq (by dsimp only [C];ring)

end ShrinkingSpheres.ParallelEnergy
