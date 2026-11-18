import Proof.ParallelScalarModelLeadingSum
import Proof.ParallelScalarModelZeroSum
import Proof.ParallelScalarModelDefectIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

structure ScalarModelLeadingEstimate (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) where
  eta : ℝ
  C : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  C_nonneg : 0 ≤ C
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ eta → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let T := fun y => scalarModelLeadingDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelLeadingDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      MeasureTheory.IntegrableOn T Y ∧ |4*(∫ y in Y,T y)| ≤ C*ε*energySq Y d.γ d.frame d.radius φ

theorem scalar_model_leading_estimate_exists {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    Nonempty (ScalarModelLeadingEstimate Y Ω m K ρ c₀ M Cj CF CT) := by
  obtain ⟨eta,C,hEta,hEta1,hC,hActual⟩ := uniform_scalar_model_leading_sum_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨⟨eta,C,hEta,hEta1,hC,?_⟩⟩
  intro floor hf ε hε hSmall d hd P φ E D hφ
  exact hActual floor hf ε hε hSmall d hd CF CT P φ E D hφ

structure ScalarModelDegreeEstimate (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d →
    ∀ A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
    ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let T := fun y => scalarModelDegreeDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelDegreeDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      MeasureTheory.IntegrableOn T Y ∧ |1*(∫ y in Y,T y)| ≤ C*ε*energySq Y d.γ d.frame d.radius φ

theorem scalar_model_degree_estimate_exists {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj)
    (ZB : ScalarModelZeroWeightBudget Y Ω m K ρ c₀ M Cj) :
    Nonempty (ScalarModelDegreeEstimate Y Ω m K ρ c₀ M Cj) := by
  obtain ⟨C,hC,hActual⟩ := uniform_scalar_model_degree_sum_integral_bound hY hΩ hSub K ρ c₀ M Cj hK RB ZB
  refine ⟨⟨C,hC,?_⟩⟩
  intro floor hf ε hε hε1 d hd A hA φ E D hφ
  simpa only [one_mul] using hActual floor hf ε hε hε1 d hd A hA φ E D hφ

structure ScalarModelDefectEstimate (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let T := fun y => scalarModelDefectPairDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelDefectPairDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      MeasureTheory.IntegrableOn T Y ∧ |1*(∫ y in Y,T y)| ≤ C*ε*energySq Y d.γ d.frame d.radius φ

theorem scalar_model_defect_estimate_exists {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj) :
    Nonempty (ScalarModelDefectEstimate Y Ω m K ρ c₀ M Cj) := by
  obtain ⟨C,hC,hActual⟩ := uniform_scalar_model_defect_pair_integral_bound hY hΩ hSub (by omega) K ρ c₀ M Cj hK RB
  refine ⟨⟨C,hC,?_⟩⟩
  intro floor hf ε hε hε1 d hd φ E D hφ
  simpa only [one_mul] using hActual floor hf ε hε hε1 d hd φ E D hφ

structure ScalarModelAdjointHigherAvailability (Y Ω : Set X) (m : ℕ) (K ρ c₀ : ℝ)
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) where
  eta : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ eta → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
    ∃ A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),∀ y ∈ Y,∀ j : I,
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
        (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

theorem scalar_model_adjoint_higher_availability_exists {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) (CF CT : ℝ) :
    Nonempty (ScalarModelAdjointHigherAvailability Y Ω m K ρ c₀ M Cj CF CT) := by
  obtain ⟨eta,C,hEta,hEta1,hC,hActual⟩ := uniform_flat_raising_constant_adjoint_higher hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨⟨eta,hEta,hEta1,?_⟩⟩
  intro floor hf ε hε hSmall d hd P
  obtain ⟨A,hA⟩ := hActual floor hf ε hε hSmall d hd CF CT P
  exact ⟨A,fun y hy j => (hA y hy j).1⟩

end ShrinkingSpheres.ParallelEnergy
