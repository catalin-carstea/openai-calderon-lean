import Proof.ParallelScalarModelZeroBudgets
import Proof.ParallelScalarModelZeroIntegral
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

theorem uniform_scalar_model_degree_sum_integral_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K)
    (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj)
    (ZB : ScalarModelZeroWeightBudget Y Ω m K ρ c₀ M Cj) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (∀ j : I,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
        (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ →
      let T := fun y => scalarModelDegreeDensity d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
        scalarModelDegreeDensity d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y
      IntegrableOn T Y ∧ |∫ y in Y,T y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨C0,hC0,hBase⟩ := uniform_scalar_model_degree_pair_integral_bound hY hΩ hSub K ρ c₀ M Cj hK
    RB ZB.zeroBound ZB.firstBound ZB.zero_nonneg ZB.first_nonneg
  refine ⟨9*C0,by positivity,?_⟩
  intro floor hf ε hε hε1 d hd A hA φ E D hφ
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let F := fun (p : I×I) y => scalarModelDegreePairDensity d
    (fun a b => scalarModelZeroDensityWeight d a b p.1 p.2) p.2 Ur y+
    scalarModelDegreePairDensity d (fun a b => scalarModelZeroDensityWeight d a b p.1 p.2) p.2 Ui y
  have hSingle (p : I×I) := hBase floor hf ε hε d hd A hA
    (fun a b => scalarModelZeroDensityWeight d a b p.1 p.2)
    (fun a b => (ZB.actual floor hf ε hε hε1 d hd a b p.1 p.2).1)
    (fun y hy a b => scalarModelZeroDensityWeight_symmetric hSub hd (zero_lt_one.trans_le hK) hy a b p.1 p.2)
    (fun a b y hy i => (ZB.actual floor hf ε hε hε1 d hd a b p.1 p.2).2 y hy i) p.2 φ E D hφ
  have hSum := scalar_model_finite_integral_sum_bound Y 1 (C0*ε*energySq Y d.γ d.frame d.radius φ) F
    (fun p => (hSingle p).1) (fun p => by simpa only [one_mul] using (hSingle p).2)
  have hEq : (fun y => scalarModelDegreeDensity d Ur y+scalarModelDegreeDensity d Ui y)=
      (fun y => ∑ p : I×I,F p y) := by
    funext y
    simp only [scalarModelDegreeDensity,F,Fintype.sum_prod_type,Finset.sum_add_distrib]
  rw [hEq]
  refine ⟨hSum.1,?_⟩
  have hCard : (Fintype.card (I×I):ℝ)=9 := by norm_num
  simpa only [one_mul,hCard,mul_assoc] using hSum.2

end ShrinkingSpheres.ParallelEnergy
