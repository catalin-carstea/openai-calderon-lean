import Proof.ParallelScalarModelLeadingIntegral
import Proof.ParallelScalarModelNormalForm
import Proof.ParallelScalarModelFiniteSum

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

theorem uniform_scalar_model_leading_sum_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ φ : Field,
      ∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let T := fun y => scalarModelLeadingDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelLeadingDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      IntegrableOn T Y ∧ |4*(∫ y in Y,T y)| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,C0,hη,hη1,hC0,hBase⟩ := uniform_scalar_model_leading_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,81*C0,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let F := fun (p : I×I×I×I) y =>
    halfCovariantThirdDensity d (metricDensity d.γ)
      (scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d p.1 p.2.1 p.2.2.1 p.2.2.2) p.2.2.2)
      (fiveHalfCovariantDerivative d Ur) (axis p.1) (axis p.2.1) (axis p.2.2.1) y+
    halfCovariantThirdDensity d (metricDensity d.γ)
      (scalarModelSymmetricCoefficient d (scalarModelLeadingWeight d p.1 p.2.1 p.2.2.1 p.2.2.2) p.2.2.2)
      (fiveHalfCovariantDerivative d Ui) (axis p.1) (axis p.2.1) (axis p.2.2.1) y
  have hSingle (p : I×I×I×I) := hBase floor hf ε hε hSmall d hd CF CT P p.1 p.2.1 p.2.2.1 p.2.2.2 φ E D hφ
  have hSum := scalar_model_finite_integral_sum_bound Y 4 (C0*ε*energySq Y d.γ d.frame d.radius φ) F
    (fun p => (hSingle p).1) (fun p => (hSingle p).2)
  have hEq : (fun y => scalarModelLeadingDensity d Ur y+scalarModelLeadingDensity d Ui y)=
      (fun y => ∑ p : I×I×I×I,F p y) := by
    funext y
    simp only [scalarModelLeadingDensity,F,Fintype.sum_prod_type,Finset.sum_add_distrib]
  rw [hEq]
  refine ⟨hSum.1,?_⟩
  have hCard : (Fintype.card (I×I×I×I):ℝ)=81 := by norm_num
  simpa only [hCard,mul_assoc] using hSum.2

end ShrinkingSpheres.ParallelEnergy
