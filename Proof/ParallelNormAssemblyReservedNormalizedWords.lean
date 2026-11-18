import Proof.ParallelNormAssemblyReservedCoordinateOperators
import Proof.FramedRaisingHalfCovariantData
import Proof.PhysicalPotentialGeneratorBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT : ℝ}

def normalizedPotentialGeneratorLow (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (a : PhysicalPotentialGeneratorIndex) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (potentialGeneratorWeight (d.radius y) a)⁻¹ • potentialCoordinateGeneratorLow P y a

def normalizedPotentialGeneratorHigh (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (a : PhysicalPotentialGeneratorIndex) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (potentialGeneratorWeight (d.radius y) a)⁻¹ • potentialCoordinateGeneratorHigh P y a

def normalizedPotentialWordCoefficient (d : Data) (y : X)
    (a b : PhysicalPotentialGeneratorIndex) : ℝ :=
  potentialCoordinateWordCoefficient d y a b*potentialGeneratorWeight (d.radius y) a*
    potentialGeneratorWeight (d.radius y) b

/-- Radius normalization is an exact identity of the complete actual
potential through the same successive Sobolev levels, before estimates. -/
theorem potential_quadratic_normalized_coordinate_words (P : PhysicalPrincipalData Y d CF CT)
    (y : X) (hr : 0 < d.radius y)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    P.potentialQuadraticHalfL y=
      ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        normalizedPotentialWordCoefficient d y a b •
          (normalizedPotentialGeneratorLow P y a).comp (normalizedPotentialGeneratorHigh P y b) := by
  rw [potential_quadratic_coordinate_words P y he]
  have hw (a : PhysicalPotentialGeneratorIndex) : potentialGeneratorWeight (d.radius y) a ≠ 0 := by
    rcases a with u | (i | i) <;> simp only [potentialGeneratorWeight]
    · norm_num
    · norm_num
    · exact hr.ne'
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [normalizedPotentialWordCoefficient,normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_smul]
  congr 1
  field_simp [hw a,hw b]

/-- Every normalized coordinate angular generator has common low/HIGH
bounds. Only frame VALUES and the genuine selected first-error endpoints
are used. All constants precede profiles and tests. -/
theorem uniform_normalized_potential_generator_bounds {Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 1 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (CF : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ floor ε d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CT : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,∀ a : PhysicalPotentialGeneratorIndex,
      ‖normalizedPotentialGeneratorLow P y a‖ ≤ C ∧
      ‖normalizedPotentialGeneratorHigh P y a‖ ≤ C := by
  let Q := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
  let E := 3*K*|CF|
  let C := 2+Q+E
  have hK0 := zero_le_one.trans hK
  have hQ : 0 ≤ Q := framedRaisingHalfBudget_nonneg _ _ _ hK0
  have hE : 0 ≤ E := by dsimp only [E];positivity
  have h2C : 2 ≤ C := by dsimp only [C];linarith only [hQ,hE]
  have hQC : Q ≤ C := by dsimp only [C];linarith only [hE]
  have hEC : E ≤ C := by dsimp only [C];linarith only [hQ]
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  intro floor ε d hd CT P y hy a
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have he := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hc (j b : I) : |frameCoordinateLinear d.γ d.frame y j (axis b)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hSub hy) he b j
  have hLo (j : I) : ‖P.first.low j y‖ ≤ |CF| *d.radius y :=
    (P.first.low_bound j y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self CF) hr.le)
  have hHi (j : I) : ‖P.first.high j y‖ ≤ |CF| *d.radius y :=
    (P.first.high_bound j y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self CF) hr.le)
  rcases a with u | (b | b)
  · simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight,
      potentialCoordinateGeneratorLow,potentialCoordinateGeneratorHigh,inv_one,one_smul] using
      And.intro ((norm_sphereSobolevShiftedDegreeL_le_two _).trans h2C)
        ((norm_sphereSobolevShiftedDegreeL_le_two _).trans h2C)
  · have hR := hd.framedRaisingHalf_covariant_data hY hΩ hm hK b y hy
    simpa only [normalizedPotentialGeneratorLow,normalizedPotentialGeneratorHigh,potentialGeneratorWeight,
      potentialCoordinateGeneratorLow,potentialCoordinateGeneratorHigh,inv_one,one_smul] using
      And.intro (hR.1.trans hQC) (hR.2.1.trans hQC)
  · have hL := norm_weighted_sum_three_le
      (fun j => frameCoordinateLinear d.γ d.frame y j (axis b)) (fun j => P.first.low j y)
      K (|CF| *d.radius y) hK0 (fun j => hc j b) hLo
    have hH := norm_weighted_sum_three_le
      (fun j => frameCoordinateLinear d.γ d.frame y j (axis b)) (fun j => P.first.high j y)
      K (|CF| *d.radius y) hK0 (fun j => hc j b) hHi
    have hLN : ‖potentialCoordinateGeneratorLow P y (.inr (.inr b))‖ ≤ E*d.radius y := hL.trans_eq (by dsimp only [E];ring)
    have hHN : ‖potentialCoordinateGeneratorHigh P y (.inr (.inr b))‖ ≤ E*d.radius y := hH.trans_eq (by dsimp only [E];ring)
    constructor
    · simp only [normalizedPotentialGeneratorLow,potentialGeneratorWeight,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
      exact ((mul_le_mul_of_nonneg_left hLN (inv_nonneg.mpr hr.le)).trans_eq (by field_simp)).trans hEC
    · simp only [normalizedPotentialGeneratorHigh,potentialGeneratorWeight,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
      exact ((mul_le_mul_of_nonneg_left hHN (inv_nonneg.mpr hr.le)).trans_eq (by field_simp)).trans hEC

end ShrinkingSpheres.ParallelEnergy
