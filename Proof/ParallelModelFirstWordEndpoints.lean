import Proof.ParallelModelFirstZeroCubic
import Proof.ParallelModelFirstBoundedHigher

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

lemma modelFirstNormalizedAdjointHigh_graph
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y)
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelFirstNormalizedAdjointHigh P W a)=
      (normalizedPotentialGeneratorLow P y a).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hW (e : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (W.adjoint_compatible e) u
  simp only [ContinuousLinearMap.comp_apply] at hW
  rw [normalized_generator_low_old_words]
  simp only [modelFirstNormalizedAdjointHigh,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,
    map_sum,map_smul,hW]

def modelFirstBoundedForwardHigh (d : Data) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma modelFirstBoundedForwardHigh_graph (d : Data) (b : I) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelFirstBoundedForwardHigh d b y)=
      (effectiveFirstBoundedRemainderHalfL d b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  rw [modelFirstBoundedForwardHigh,←ContinuousLinearMap.comp_assoc,effective_first_bounded_half_actual d b y hFrame]

/-- The actual forward HIGH has exactly the complete normalized angular
word sum and genuine order-zero remainder. Its original graph is retained. -/
theorem model_first_forward_high_word_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) (b : I)
    (hP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    P.firstCovariantCoordinateHigherL b y=
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a • normalizedPotentialGeneratorHigh P y a)+
        modelFirstBoundedForwardHigh d b y := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hActual := DFunLike.congr_fun hP u
  have hEach (a : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (normalized_generator_balanced P hy a) u
  have hBound := DFunLike.congr_fun (modelFirstBoundedForwardHigh_graph d b y hFrame) u
  have hLow := DFunLike.congr_fun (effective_first_normalized_word_split P hY hd hy b)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply] at hActual hEach hBound
  rw [hActual]
  simp only [_root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,hEach,hBound] at hLow ⊢
  exact hLow

/-- The arbitrary fixed WF true-adjoint HIGH has the SAME angular word
sum plus the genuine reflected bounded adjoint. No new WF is selected. -/
theorem model_first_adjoint_high_word_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b : I) :
    WF.covariantCoordinateAdjointHigher b y=
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a • modelFirstNormalizedAdjointHigh P W a)+
        effectiveFirstBoundedAdjointHigherL d b y := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hActual := DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hy) u
  have hEach (a : PhysicalPotentialGeneratorIndex) := DFunLike.congr_fun (modelFirstNormalizedAdjointHigh_graph P hy W a) u
  have hBound := DFunLike.congr_fun (effective_first_bounded_adjoint_higher_graph d b y hFrame) u
  have hLow := congrArg (fun A : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A.adjoint)
    (effective_first_normalized_word_split P hY hd hy b)
  simp only [map_add,map_sum,map_smul] at hLow
  have hLowu := DFunLike.congr_fun hLow (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply] at hActual hEach hBound
  rw [hActual]
  simp only [_root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,hEach,hBound] at hLowu ⊢
  exact hLowu

end ShrinkingSpheres.ParallelEnergy
