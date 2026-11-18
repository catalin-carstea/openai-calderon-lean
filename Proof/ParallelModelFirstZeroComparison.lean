import Proof.ParallelModelFirstZeroBounded
import Proof.ParallelModelFirstZeroCubicBound
import Proof.ParallelModelFirstZeroGreen
import Proof.ParallelModelFirstNormalForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma weighted_difference_with_remainder {ι : Type*} [Fintype ι]
    (w f g k : ι → ℝ) (r s : ℝ) (h : ∀ a,f a-g a=k a) :
    ((∑ a,w a*f a)+r)-((∑ a,w a*g a)+s)=(∑ a,w a*k a)+(r-s) := by
  calc
    _ = (∑ a,w a*(f a-g a))+(r-s) := by simp only [mul_sub,Finset.sum_sub_distrib];ring
    _ = _ := by simp only [h]

/-- Exact complete B/actual-WF adjoint comparison for one zero-model
row: all angular words are commuted together, and the complete bounded
geometric/scalar remainder stays explicit. -/
theorem model_first_zero_complete_word_pair_identity
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b c : I)
    (u5 : SphereSobolev (5/2:ℝ)) (h : SphereSobolev (3/2:ℝ))
    (hP : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
    let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5;
    ⟪Z (framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0)),Z (P.firstCovariantCoordinateHigherL b y h)⟫_ℝ-
      sphereSobolevDualPairing (1/2:ℝ) (WF.covariantCoordinateAdjointHigher b y u) (modelFirstZeroAdjointWeakL d c y h)=
      sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
        (modelFirstZeroWordResidualValue P W b c u)+modelFirstZeroBoundedResidual d b c y u5 h := by
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5
  let M := framedRaisingHigherL d y (axis c) (scalarModelDegreeSection (fun _ : X => u5) 0)
  have hEach (a : PhysicalPotentialGeneratorIndex) := model_first_zero_normalized_word_pair_identity P hy W c a u5 h
  have hSum := weighted_difference_with_remainder (effectiveFirstWordCoefficient d b y)
    (fun a => ⟪Z M,Z (normalizedPotentialGeneratorHigh P y a h)⟫_ℝ)
    (fun a => sphereSobolevDualPairing (1/2:ℝ) (modelFirstNormalizedAdjointHigh P W a u) (modelFirstZeroAdjointWeakL d c y h))
    (fun a => sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) h)
      (modelFirstNormalizedZeroCommutatorValue P W c a u))
    ⟪Z M,Z (modelFirstBoundedForwardHigh d b y h)⟫_ℝ
    (sphereSobolevDualPairing (1/2:ℝ) (effectiveFirstBoundedAdjointHigherL d b y u) (modelFirstZeroAdjointWeakL d c y h)) hEach
  rw [model_first_forward_high_word_split hY hd P hy b hP,model_first_adjoint_high_word_split hY hd P WF hy W b]
  simp only [modelFirstZeroWordResidualValue,modelFirstZeroBoundedResidual,_root_.add_apply,_root_.sum_apply,_root_.smul_apply,
    map_add,map_sum,map_smul,sphereSobolevDualPairing,inner_add_right,inner_add_left,inner_sum,sum_inner,
    real_inner_smul_right,real_inner_smul_left]
  simpa only [sphereSobolevDualPairing,Z,u,M] using hSum

lemma model_first_zero_adjoint_physical_pair
    (d : Data) (c : I) (y : X) (u5 : SphereSobolev (5/2:ℝ)) (z : SphereSobolev (1/2:ℝ)) :
    ⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y (scalarModelShiftedDegreeSection (fun _ : X => u5) 0)),
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) z⟫_ℝ=
    sphereSobolevDualPairing (1/2:ℝ) z (modelFirstZeroAdjointWeakL d c y
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u5)) := by
  let M := scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y
    (scalarModelShiftedDegreeSection (fun _ : X => u5) 0)
  have hM := DFunLike.congr_fun (scalarModelRaisingAdjointHigher_balanced modelFirstFlatAdjointHigher d c y modelFirstFlatAdjointHigher_graph)
    (scalarModelShiftedDegreeSection (fun _ : X => u5) 0)
  simp only [ContinuousLinearMap.comp_apply,modelFirstShiftedDegree_lift] at hM
  have hPair := half_dual_pairing_inclusion z M
  rw [hM] at hPair
  exact (real_inner_comm _ _).trans hPair.symm

def modelFirstZeroResidualDensity {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  modelFirstZeroDensity P WF U y-modelFirstZeroPairedDensity P WF U y

/-- The actual paired zero-model residual has only genuine order-dropped
angular commutators and bounded order-zero products. This identity precedes
all absolute values and retains the SAME actual W and source. -/
theorem modelFirstZeroResidualDensity_eq
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ))
    (hP : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
      (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    modelFirstZeroResidualDensity P WF U y=
      ∑ k : I,∑ c : I,∑ b : I,modelFirstZeroWeight d k c y*(
        sphereSobolevDualPairing (1/2:ℝ)
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfCovariantDerivative d U (axis b) y))
          (modelFirstZeroWordResidualValue P W b c (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))+
        modelFirstZeroBoundedResidual d b c y (U y) (fiveHalfCovariantDerivative d U (axis b) y)) := by
  have hRow (k c b : I) := model_first_zero_complete_word_pair_identity hY hd P WF hy W b c (U y)
    (fiveHalfCovariantDerivative d U (axis b) y) (hP b)
  have hAdj (c b : I) := model_first_zero_adjoint_physical_pair d c y (U y)
    (WF.covariantCoordinateAdjointHigher b y (fiveHalfCovariantDerivative d U (axis b) y))
  simp only [scalarModelDegreeSection,scalarModelShiftedDegreeSection] at hAdj hRow
  unfold modelFirstZeroResidualDensity modelFirstZeroDensity modelFirstZeroPairedDensity quadraticHigherPairDensity
  dsimp only
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  simp only [scalarModelDegreeSection,scalarModelShiftedDegreeSection]
  rw [hAdj c b]
  have hh := congrArg (fun t : ℝ => modelFirstZeroWeight d k c y*t) (hRow k c b)
  simp only [modelFirstZeroWeight,modelFirstLeadingWeight,scalarModelDegreeSection,scalarModelShiftedDegreeSection,
    ←graded_covariant_derivative_five_half,fiveHalfCovariantDerivative,sphereSobolevDualPairing,mul_sub,mul_add,mul_assoc] at hh ⊢
  linarith only [hh]

end ShrinkingSpheres.ParallelEnergy
