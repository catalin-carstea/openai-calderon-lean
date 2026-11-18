import Proof.ParallelScalarFirstLeadingIntegral
import Proof.PhysicalScalarSelfIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def scalarFirstLeadingTermComplexDensity {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (a b k : I) (y : X) : ℝ :=
  let w := fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b
  let C := scalarFirstSymmetricCoefficient P w k
  halfCovariantThirdDensity d (metricDensity d.γ) C
      (fiveHalfCovariantDerivative d (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))) (axis a) (axis b) (axis k) y+
    halfCovariantThirdDensity d (metricDensity d.γ) C
      (fiveHalfCovariantDerivative d (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))) (axis a) (axis b) (axis k) y

def scalarFirstLeadingComplexDensity {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  2*(∑ a : I,∑ b : I,∑ k : I,scalarFirstLeadingTermComplexDensity P E a b k y)

/-- The complete leading symmetric scalar/first complex contribution,
all coordinate contractions and factor two, has a uniform original-energy
bound. This is one of the three terms in the exact paired expansion. -/
theorem uniform_scalar_first_leading_cross_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CB CS : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,∀ D : AngularModelData E d.radius,
      Test Y d.γ d.frame φ → IntegrableOn (scalarFirstLeadingComplexDensity P E) Y ∧
        |∫ y in Y,scalarFirstLeadingComplexDensity P E y| ≤ C*ε^2*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,C,hη,hη1,hC,hData⟩ := uniform_scalar_first_symmetric_third_integral_bound
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,27*C,hη,hη1,mul_nonneg (by norm_num) hC,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CB CS P WF φ E D hφ
  let F := scalarFirstLeadingTermComplexDensity P E
  have hSingle (a b k : I) : IntegrableOn (F a b k) Y ∧
      |2*(∫ y in Y,F a b k y)| ≤ C*ε^2*energySq Y d.γ d.frame d.radius φ :=
    hData floor hf ε hε hSmall d hd CF CT CB CS P WF a b k φ E D hφ
  have hInt (a b k : I) : IntegrableOn (F a b k) Y := (hSingle a b k).1
  have hSumI : IntegrableOn (fun y => ∑ a : I,∑ b : I,∑ k : I,F a b k y) Y :=
    integrable_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ (fun b _ =>
      integrable_finsetSum Finset.univ (fun k _ => hInt a b k)))
  have hIntegral : (∫ y in Y,scalarFirstLeadingComplexDensity P E y)=
      ∑ a : I,∑ b : I,∑ k : I,2*(∫ y in Y,F a b k y) := by
    change (∫ y in Y,2*(∑ a : I,∑ b : I,∑ k : I,F a b k y))=_
    rw [integral_const_mul,integral_finsetSum (f:=fun a y => ∑ b : I,∑ k : I,F a b k y) Finset.univ
      (fun a _ => integrable_finsetSum Finset.univ (fun b _ =>
        integrable_finsetSum Finset.univ (fun k _ => hInt a b k)))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [integral_finsetSum Finset.univ (fun b _ => integrable_finsetSum Finset.univ (fun k _ => hInt a b k)),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [integral_finsetSum Finset.univ (fun k _ => hInt a b k),Finset.mul_sum]
  refine ⟨hSumI.const_mul 2,?_⟩
  rw [hIntegral]
  have hh := abs_fin_three_sum_le (fun a => ∑ b : I,∑ k : I,2*(∫ y in Y,F a b k y))
    (3*(3*(C*ε^2*energySq Y d.γ d.frame d.radius φ))) (fun a =>
      abs_fin_three_sum_le _ (3*(C*ε^2*energySq Y d.γ d.frame d.radius φ)) (fun b =>
        abs_fin_three_sum_le _ (C*ε^2*energySq Y d.γ d.frame d.radius φ) (fun k => (hSingle a b k).2)))
  exact hh.trans_eq (by ring)

end ShrinkingSpheres.ParallelEnergy
