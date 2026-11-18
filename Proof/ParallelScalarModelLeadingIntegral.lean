import Proof.ParallelScalarModelLeadingJets
import Proof.ParallelScalarModelLeadingBound
import Proof.UniformFlatRaisingConstantAdjointHigher

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

/-- One exact coordinate contraction of the corrected model/scalar
leading term is bounded at linear epsilon scale, including factor four. -/
theorem uniform_scalar_model_leading_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C0 ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ a b k c : I,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
        let C := scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d a b k c) c
        let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
        let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
        let T := fun y => halfCovariantThirdDensity d (metricDensity d.γ) C
          (fiveHalfCovariantDerivative d Ur) (axis a) (axis b) (axis k) y+
          halfCovariantThirdDensity d (metricDensity d.γ) C
          (fiveHalfCovariantDerivative d Ui) (axis a) (axis b) (axis k) y
        IntegrableOn T Y ∧ |4*(∫ y in Y,T y)| ≤ C0*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,CR,hη,hη1,hCR,hAdj⟩ := uniform_flat_raising_constant_adjoint_higher hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  let WB := Classical.choice (scalar_model_leading_weight_budget_exists hY hΩ hSub (by omega) K ρ c₀ M Cj hK)
  let RB := Classical.choice (scalar_model_raising_budget_exists hY hΩ (by omega) K ρ c₀ M Cj hK)
  obtain ⟨Q,hQ,hJets⟩ := uniform_scalar_model_symmetric_half_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK WB RB
  obtain ⟨C0,hC0,hBound⟩ := uniform_scalar_model_symmetric_third_integral_bound hY hΩ hSub (by omega) K ρ c₀ M Cj hK Q hQ
  refine ⟨η,2*C0,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P a b k c φ E D hφ
  by_cases hEmpty : Y=∅
  · subst Y
    have hNonneg : 0 ≤ 2*C0*ε*energySq ∅ d.γ d.frame d.radius φ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hε) (energySq_nonneg _ _ _ _ _)
    simpa using hNonneg
  obtain ⟨y0,hy0⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨A,hA⟩ := hAdj floor hf ε hε hSmall d hd CF CT P
  have hAG := fun j : I => (hA y0 hy0 j).1
  have hJ := hJets floor hf ε hε (hSmall.trans hη1) d hd A hAG a b k c
  have hB := hBound floor hf ε hε d hd
    (scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d a b k c) c)
    (scalarModelSymmetricHigher A d (scalarModelLeadingWeight d a b k c) c)
    hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2 a b k φ E D hφ
  refine ⟨hB.1,?_⟩
  calc
    _ = 2*|2*(∫ y in Y,
      halfCovariantThirdDensity d (metricDensity d.γ)
        (scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d a b k c) c)
        (fiveHalfCovariantDerivative d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)))
        (axis a) (axis b) (axis k) y+
      halfCovariantThirdDensity d (metricDensity d.γ)
        (scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d a b k c) c)
        (fiveHalfCovariantDerivative d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)))
        (axis a) (axis b) (axis k) y)| := by
      have hFour (t : ℝ) : |4*t|=2*|2*t| := by
        calc
          _ = |(2:ℝ)*(2*t)| := congrArg abs (by ring)
          _ = |(2:ℝ)| * |2*t| := abs_mul _ _
          _ = _ := by norm_num
      exact hFour _
    _ ≤ 2*(C0*ε*energySq Y d.γ d.frame d.radius φ) := mul_le_mul_of_nonneg_left hB.2 (by norm_num)
    _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy
