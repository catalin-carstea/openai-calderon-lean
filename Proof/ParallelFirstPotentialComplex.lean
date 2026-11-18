import Proof.ParallelFirstPotentialDensitySplit
import Proof.ParallelFirstPotentialPairedIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstPotentialPairedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstPotentialPairedDensity P (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstPotentialPairedDensity P (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstPotentialBoundedComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstPotentialBoundedDensity P W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstPotentialBoundedDensity P W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstPotentialCubicComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstPotentialCubicDensity P W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstPotentialCubicDensity P W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

theorem firstPotentialComplexDensity_exact_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    firstPotentialComplexDensity P WF W E y=firstPotentialPairedComplexDensity P E y+
      firstPotentialBoundedComplexDensity P W E y-firstPotentialCubicComplexDensity P W E y-
      firstPotentialDefectComplexDensity P WF W E y := by
  have hR := firstPotentialDensity_exact_split hY hd P WF W _ hy
    ((E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)).differentiable (by simp)).differentiableAt hRaw
  have hI := firstPotentialDensity_exact_split hY hd P WF W _ hy
    ((E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)).differentiable (by simp)).differentiableAt hRaw
  unfold firstPotentialComplexDensity firstPotentialPairedComplexDensity firstPotentialBoundedComplexDensity
    firstPotentialCubicComplexDensity firstPotentialDefectComplexDensity
  rw [hR,hI]
  ring

/-- Finite assembly of all21 coordinate/normalized-generator Green pairs,
with literal factor2 already inside their common scalar density weight. -/
theorem uniform_first_potential_paired_integral_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CF : ℝ) :
    ∃ η CP : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CP ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ φ : Field,∀ E : HarmonicTestExpansion Y d.γ d.frame φ,
      ∀ D : AngularModelData E d.radius,Test Y d.γ d.frame φ →
      IntegrableOn (firstPotentialPairedComplexDensity P E) Y ∧
        |∫ y in Y,firstPotentialPairedComplexDensity P E y| ≤ CP*ε*energySq Y d.γ d.frame d.radius φ := by
  obtain ⟨η,C,hη,hη1,hC,hWord⟩ := uniform_first_potential_paired_word_integral_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CF
  refine ⟨η,21*C,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CT CG CK P W φ E D hφ
  let F := fun (b : I) (a : PhysicalPotentialGeneratorIndex) (y : X) =>
    quadraticHigherPairDensity d (firstPotentialGreenWeight d b a)
      (fun x => normalizedPotentialGeneratorHigh P x a) P.potentialQuadraticHalfL
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (axis b) y+
    quadraticHigherPairDensity d (firstPotentialGreenWeight d b a)
      (fun x => normalizedPotentialGeneratorHigh P x a) P.potentialQuadraticHalfL
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (axis b) y
  have hEach (b : I) (a : PhysicalPotentialGeneratorIndex) :
      IntegrableOn (F b a) Y ∧ |∫ y in Y,F b a y| ≤ C*ε*energySq Y d.γ d.frame d.radius φ :=
    hWord floor hf ε hε hSmall d hd CT CG CK P W b a φ E D hφ
  have hSumI (b : I) : IntegrableOn (fun y => ∑ a : PhysicalPotentialGeneratorIndex,F b a y) Y :=
    integrable_finset_sum _ (fun a _ => (hEach b a).1)
  have hEq : firstPotentialPairedComplexDensity P E=(fun y => ∑ b : I,∑ a : PhysicalPotentialGeneratorIndex,F b a y) := by
    funext y
    simp only [firstPotentialPairedComplexDensity,firstPotentialPairedDensity,F,Finset.sum_add_distrib]
  rw [hEq]
  refine ⟨integrable_finset_sum _ (fun b _ => hSumI b),?_⟩
  rw [integral_finset_sum _ (fun b _ => hSumI b)]
  simp_rw [integral_finset_sum _ (fun a _ => (hEach _ a).1)]
  calc
    _ ≤ ∑ b : I,|∑ a : PhysicalPotentialGeneratorIndex,∫ y in Y,F b a y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : I,∑ a : PhysicalPotentialGeneratorIndex,|∫ y in Y,F b a y| :=
      Finset.sum_le_sum (fun b _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _b : I,∑ _a : PhysicalPotentialGeneratorIndex,C*ε*energySq Y d.γ d.frame d.radius φ :=
      Finset.sum_le_sum (fun b _ => Finset.sum_le_sum (fun a _ => (hEach b a).2))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,PhysicalPotentialGeneratorIndex,
        Fintype.card_sum,Fintype.card_unique,nsmul_eq_mul];ring

end ShrinkingSpheres.ParallelEnergy
