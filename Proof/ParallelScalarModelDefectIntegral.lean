import Proof.ParallelScalarModelDefectPoint
import Proof.ParallelScalarModelDefectIntegrability

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

/-- Integrated complete model-adjoint/scalar-transpose-defect estimate,
including the SAME real and imaginary source components. -/
theorem uniform_scalar_model_defect_pair_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let T := fun y => scalarModelDefectPairDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelDefectPairDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      IntegrableOn T Y ∧ |∫ y in Y,T y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C,hC,hPoint⟩ := uniform_scalar_model_defect_pair_point_bound hY hΩ hSub hm K ρ c₀ M Cj hK RB
  refine ⟨C,hC,?_⟩
  intro floor hf ε hε hε1 d hd φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hr := scalarModelDefectPairDensity_integrableOn hY hSub hd (zero_lt_one.trans_le hK)
    Ur (E.contDiff_realHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hi := scalarModelDefectPairDensity_integrableOn hY hSub hd (zero_lt_one.trans_le hK)
    Ui (E.contDiff_imagHigherSobolevSection _ _) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero _ _ (by norm_num) hx)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0 :=
    fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hDom := (hd.2.2.2.2.1.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hf hφ).const_mul (C*ε)
  have hBound : ∀ᵐ y ∂volume.restrict Y,
      ‖scalarModelDefectPairDensity d Ur y+scalarModelDefectPairDensity d Ui y‖ ≤
        (C*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact hPoint floor hf ε hε hε1 d hd φ E D hφ y hy
  have hIntegral := norm_integral_le_of_norm_le hDom hBound
  refine ⟨hr.add hi,?_⟩
  simpa only [Real.norm_eq_abs,integral_const_mul,←energySq_eq_integral_density] using hIntegral

end ShrinkingSpheres.ParallelEnergy
