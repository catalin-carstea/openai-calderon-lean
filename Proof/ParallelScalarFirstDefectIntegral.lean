import Proof.ParallelScalarFirstDefectCross
import Proof.ParallelScalarFirstWeakSquare

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Complete scalar-adjoint-defect / physical first-adjoint cross term,
including both real components and factor two, in the original energy.
The first-adjoint weak norm contribution is imported from first-self's
checked frozen contribution, with its authorship retained. -/
theorem uniform_scalar_first_defect_cross_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CB CS CG CK : ℝ,
      0 ≤ CG → 0 ≤ CK → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → IntegrableOn (scalarFirstDefectComplexDensity P WF W E) Y ∧
        |∫ y in Y,scalarFirstDefectComplexDensity P WF W E y| ≤
          C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨CS,hCS,hScalar⟩ := uniform_scalar_fiveHalf_defect_square_point_bound
    hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  obtain ⟨η,CA,hη,hη1,hCA,hAdjoint⟩ := uniform_first_weak_square_point_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CS+CA,hη,hη1,add_nonneg hCS hCA,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CB CS0 CG CK hCG hCK P WF W φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUr := E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUi := E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hIR := scalarFirstDefectDensity_integrableOn hY hΩ hSub hd (zero_lt_one.trans_le hK)
    P WF W hCG hCK Ur hUr E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hII := scalarFirstDefectDensity_integrableOn hY hΩ hSub hd (zero_lt_one.trans_le hK)
    P WF W hCG hCK Ui hUi E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hInt : IntegrableOn (scalarFirstDefectComplexDensity P WF W E) Y := hIR.add hII
  have hPoint (y : X) (hy : y ∈ Y) : |scalarFirstDefectComplexDensity P WF W E y| ≤
      (CS+CA)*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    have hr := abs_scalarFirstDefectDensity_le hY hΩ hSub hd (zero_lt_one.trans_le hK)
      P WF W Ur hUr.contDiffOn hy
    have hi := abs_scalarFirstDefectDensity_le hY hΩ hSub hd (zero_lt_one.trans_le hK)
      P WF W Ui hUi.contDiffOn hy
    have hs := hScalar floor hf ε hε (hSmall.trans hη1) d hd φ E D hφ y hy
    have ha := hAdjoint floor hf ε hε hSmall d hd CF CT CB CS0 CG CK P WF W φ E D hφ y hy
    calc
      _ ≤ |scalarFirstDefectDensity P WF W Ur y|+|scalarFirstDefectDensity P WF W Ui y| := abs_add_le _ _
      _ ≤ metricDensity d.γ y*(
          ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) Ur y‖^2+
          ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.firstFormalAdjointCore WF W Ur y)‖^2)+
        metricDensity d.γ y*(
          ‖scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) Ui y‖^2+
          ‖sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (P.firstFormalAdjointCore WF W Ui y)‖^2) := add_le_add hr hi
      _ = scalarFiveHalfDefectSquareDensity d E y+firstWeakSquareDensity P WF W E y := by
        unfold scalarFiveHalfDefectSquareDensity firstWeakSquareDensity
        ring
      _ ≤ CS*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y+
        CA*ε^2*physicalEnergyDensity d.γ d.frame d.radius φ y := add_le_add hs ha
      _ = _ := by ring
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul ((CS+CA)*ε^2)
  have hBound : ∀ᵐ y ∂volume.restrict Y,‖scalarFirstDefectComplexDensity P WF W E y‖ ≤
      ((CS+CA)*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint y hy
  refine ⟨hInt,?_⟩
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral

end ShrinkingSpheres.ParallelEnergy
