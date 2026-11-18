import Proof.ParallelNormAssemblyReservedCoordinates
import Proof.FramedRaisingHalfEndpoints

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

private lemma frame_coordinate_combination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (F : I → E) (i : I) :
    (∑ a : I,d.frame y i a • (∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) • F j))=F i := by
  have hDual (j : I) : (∑ a : I,d.frame y i a*frameCoordinateLinear d.γ d.frame y j (axis a))=
      if j=i then 1 else 0 := by
    rw [← linear_axis_expansion,frameCoordinateLinear_apply,he]
    simp only [eq_comm]
  have hEq : (∑ a : I,d.frame y i a • (∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) • F j))=
      ∑ j : I,(∑ a : I,d.frame y i a*frameCoordinateLinear d.γ d.frame y j (axis a)) • F j := by
    simp only [Fin.sum_univ_three,smul_add,smul_smul,add_smul]
    module
  rw [hEq]
  simp [hDual]

/-- Fixed-coordinate coframe raising/error generators; these are the SAME
actual angular operators, with an exact inverse frame transformation. -/
def potentialCoordinateGeneratorLow {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    PhysicalPotentialGeneratorIndex → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  | .inl _ => sphereSobolevShiftedDegreeL (1/2:ℝ)
  | .inr (.inl a) => framedRaisingHalfL d y (axis a)
  | .inr (.inr a) => ∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) • P.first.low j y

def potentialCoordinateGeneratorHigh {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    PhysicalPotentialGeneratorIndex → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  | .inl _ => sphereSobolevShiftedDegreeL (3/2:ℝ)
  | .inr (.inl a) => framedRaisingHigherL d y (axis a)
  | .inr (.inr a) => ∑ j : I,frameCoordinateLinear d.γ d.frame y j (axis a) • P.first.high j y

lemma potential_generator_low_coordinate {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (i : PhysicalPotentialGeneratorIndex) :
    P.potentialGeneratorLow y i=∑ a : PhysicalPotentialGeneratorIndex,
      potentialFrameToCoordinate d y i a • potentialCoordinateGeneratorLow P y a := by
  rcases i with u | (i | i)
  · simp [PhysicalPrincipalData.potentialGeneratorLow,potentialFrameToCoordinate,
      potentialCoordinateGeneratorLow,Fintype.sum_sum_type]
  · symm
    simpa only [PhysicalPrincipalData.potentialGeneratorLow,potentialFrameToCoordinate,
      potentialCoordinateGeneratorLow,Fintype.sum_sum_type,Fintype.sum_unique,
      zero_smul,zero_add,add_zero,Finset.sum_const_zero,framedRaisingHalfL] using
      frame_coordinate_combination d y he (fun j => flatHalfRaisingL j) i
  · symm
    simpa only [PhysicalPrincipalData.potentialGeneratorLow,potentialFrameToCoordinate,
      potentialCoordinateGeneratorLow,Fintype.sum_sum_type,Fintype.sum_unique,
      zero_smul,zero_add,add_zero,Finset.sum_const_zero] using
      frame_coordinate_combination d y he (fun j => P.first.low j y) i

lemma potential_generator_high_coordinate {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (i : PhysicalPotentialGeneratorIndex) :
    P.potentialGeneratorHigh y i=∑ a : PhysicalPotentialGeneratorIndex,
      potentialFrameToCoordinate d y i a • potentialCoordinateGeneratorHigh P y a := by
  rcases i with u | (i | i)
  · simp [PhysicalPrincipalData.potentialGeneratorHigh,potentialFrameToCoordinate,
      potentialCoordinateGeneratorHigh,Fintype.sum_sum_type]
  · symm
    simpa only [PhysicalPrincipalData.potentialGeneratorHigh,potentialFrameToCoordinate,
      potentialCoordinateGeneratorHigh,Fintype.sum_sum_type,Fintype.sum_unique,
      zero_smul,zero_add,add_zero,Finset.sum_const_zero,framedRaisingHigherL] using
      frame_coordinate_combination d y he (fun j => flatThreeHalfRaisingL j) i
  · symm
    simpa only [PhysicalPrincipalData.potentialGeneratorHigh,potentialFrameToCoordinate,
      potentialCoordinateGeneratorHigh,Fintype.sum_sum_type,Fintype.sum_unique,
      zero_smul,zero_add,add_zero,Finset.sum_const_zero] using
      frame_coordinate_combination d y he (fun j => P.first.high j y) i

private lemma four_sum_reorder {ι κ E : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid E]
    (f : ι → ι → κ → κ → E) :
    (∑ i,∑ j,∑ a,∑ b,f i j a b)=∑ a,∑ b,∑ i,∑ j,f i j a b := by
  calc
    _ = ∑ i,∑ a,∑ j,∑ b,f i j a b := Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ a,∑ i,∑ j,∑ b,f i j a b := Finset.sum_comm
    _ = ∑ a,∑ i,∑ b,∑ j,f i j a b := Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = _ := Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

/-- Change the actual successive Sobolev levels through a finite REAL
coefficient matrix; no bounded endomorphism identification is used. -/
lemma quadratic_word_matrix_coordinate_change {Hi Mid Lo ι κ : Type*}
    [NormedAddCommGroup Hi] [NormedSpace ℝ Hi] [NormedAddCommGroup Mid] [NormedSpace ℝ Mid]
    [NormedAddCommGroup Lo] [NormedSpace ℝ Lo] [Fintype ι] [Fintype κ]
    (p : ι → ι → ℝ) (M : ι → κ → ℝ) (L : ι → Mid →L[ℝ] Lo) (H : ι → Hi →L[ℝ] Mid)
    (Lc : κ → Mid →L[ℝ] Lo) (Hc : κ → Hi →L[ℝ] Mid)
    (hL : ∀ i,L i=∑ a,M i a • Lc a) (hH : ∀ i,H i=∑ a,M i a • Hc a) :
    (∑ i,∑ j,p i j • (L i).comp (H j))=
      ∑ a,∑ b,(∑ i,∑ j,p i j*M i a*M j b) • (Lc a).comp (Hc b) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [hL,hH,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,
    map_sum,map_smul,Finset.smul_sum,Finset.sum_smul,smul_smul]
  calc
    _ = ∑ i,∑ j,∑ a,∑ b,(p i j*M i a*M j b) • Lc a (Hc b u) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ring
    _ = _ := by
      simpa only [mul_assoc] using (four_sum_reorder
        (fun i j a b => (p i j*M i a*M j b) • Lc a (Hc b u)))

/-- The complete SAME quadratic potential has a fixed-coordinate/coframe
word matrix with the coefficient bodies proved frame-independent above. -/
theorem potential_quadratic_coordinate_words {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    P.potentialQuadraticHalfL y=
      ∑ a : PhysicalPotentialGeneratorIndex,∑ b : PhysicalPotentialGeneratorIndex,
        potentialCoordinateWordCoefficient d y a b •
          (potentialCoordinateGeneratorLow P y a).comp (potentialCoordinateGeneratorHigh P y b) := by
  rw [P.potentialQuadraticHalfL_eq_word_matrix]
  have hh := quadratic_word_matrix_coordinate_change
    (PhysicalPrincipalData.potentialWordCoefficient d y) (potentialFrameToCoordinate d y)
    (P.potentialGeneratorLow y) (P.potentialGeneratorHigh y)
    (potentialCoordinateGeneratorLow P y) (potentialCoordinateGeneratorHigh P y)
    (potential_generator_low_coordinate P y he) (potential_generator_high_coordinate P y he)
  simpa only [PhysicalPrincipalData.potentialWordMatrixL,potential_coordinate_coefficients_exact d y he] using hh

end ShrinkingSpheres.ParallelEnergy
