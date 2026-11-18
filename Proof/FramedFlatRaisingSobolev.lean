import Proof.FlatRaisingHigherAlgebra
import Proof.FirstCorrectionCrossRemainder
import Proof.BoundaryCoefficientNorms
import Proof.FlatFrameAdjointIdentification
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-- The physical coframe combination of the genuine graded raising maps. -/
def framedFlatRaisingSobolevL (s : ℝ) (g : MetricField) (e : Frame) (y a : X) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  ∑ j : I,frameCoordinateLinear g e y j a • flatRaisingSobolevL s j

lemma framedFlatRaisingSobolevL_axis_expansion (s : ℝ) (g : MetricField) (e : Frame) (y a : X) :
    framedFlatRaisingSobolevL s g e y a=
      ∑ k : I,a k • framedFlatRaisingSobolevL s g e y (axis k) := by
  let T : X →L[ℝ] (SphereSobolev s →L[ℝ] SphereSobolev (s-1)) :=
    ∑ j : I,(frameCoordinateLinear g e y j).smulRight (flatRaisingSobolevL s j)
  have hh := congrArg T (axis_expansion a)
  simpa only [T,map_sum,map_smul,_root_.sum_apply,ContinuousLinearMap.smulRight_apply,
    framedFlatRaisingSobolevL] using hh.symm

lemma framedFlatRaisingSobolevL_inclusion (s t : ℝ) (hts : t ≤ s)
    (g : MetricField) (e : Frame) (y a : X) :
    (framedFlatRaisingSobolevL t g e y a).comp (sphereSobolevInclusionL s t hts)=
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (framedFlatRaisingSobolevL s g e y a) := by
  apply DFunLike.ext
  intro u
  simp only [framedFlatRaisingSobolevL,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun v => frameCoordinateLinear g e y j a • v)
    (DFunLike.congr_fun (flatRaisingSobolevL_inclusion s t hts j) u)

lemma framedFlatRaisingSobolevL_one (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (g : MetricField) (e : Frame) (y a : X) :
    framedFlatRaisingSobolevL 1 g e y a=
      boundaryGradientAdjointL (fixedCenterCoefficient Q g e y a) sphereSobolevDegreeL := by
  rw [fixedCenterBoundaryAdjointL_eq_sum Q hQ]
  simp only [framedFlatRaisingSobolevL,flatRaisingSobolevL_one Q hQ]

lemma framedFlatRaisingSobolevL_frame (s : ℝ) (g : MetricField) (e : Frame) (y : X)
    (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0) (i : I) :
    framedFlatRaisingSobolevL s g e y (e y i)=flatRaisingSobolevL s i := by
  simp only [framedFlatRaisingSobolevL,frameCoordinateLinear_apply,he,ite_smul,one_smul,zero_smul]
  simp

lemma norm_flatRaisingSobolevL_one_le_two (i : I) : ‖flatRaisingSobolevL 1 i‖ ≤ 2 := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  rw [flatRaisingSobolevL_one Q hQ]
  exact norm_coordinateBoundaryGradientAdjointL_le_two Q hQ i

lemma norm_flatRaisingSobolevL_two_le_forty (i : I) : ‖flatRaisingSobolevL 2 i‖ ≤ 40 := by
  have hh := norm_flatRaisingSobolevL_le 2 i
  norm_num [radialDriftSobolevBound] at hh
  exact hh

lemma norm_framedFlatRaisingSobolevL_le (s : ℝ) (g : MetricField) (e : Frame) (y a : X)
    (C A : ℝ) (hC : 0 ≤ C) (hA : ∀ j,‖flatRaisingSobolevL s j‖ ≤ A)
    (hL : ∀ j,‖frameCoordinateLinear g e y j‖ ≤ C) :
    ‖framedFlatRaisingSobolevL s g e y a‖ ≤ 3*C*A*‖a‖ := by
  have hCoeff (j : I) : |frameCoordinateLinear g e y j a| ≤ C*‖a‖ :=
    ((frameCoordinateLinear g e y j).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hL j) (norm_nonneg a))
  calc
    _ ≤ ∑ j : I,‖frameCoordinateLinear g e y j a • flatRaisingSobolevL s j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : I,(C*‖a‖)*A := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul (hCoeff j) (hA j) (norm_nonneg _) (mul_nonneg hC (norm_nonneg a))
    _ = _ := by simp only [Fin.sum_univ_three];ring

lemma Admissible.framedFlatRaisingSobolevL_norms {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) {y : X} (hy : y ∈ Y) (a : X) :
    ‖framedFlatRaisingSobolevL 1 d.γ d.frame y a‖ ≤ 6*(9*|M 0| *K)*‖a‖ ∧
    ‖framedFlatRaisingSobolevL 2 d.γ d.frame y a‖ ≤ 120*(9*|M 0| *K)*‖a‖ := by
  let C := 9*|M 0| *K
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hL (j : I) : ‖frameCoordinateLinear d.γ d.frame y j‖ ≤ C :=
    hd.1.1.norm_frameCoordinateLinear_le hK hCenter d.frame hFrame |M 0| (abs_nonneg _)
      (fun i l => (hd.1.reference_entry_bound hCenter i l).trans (le_abs_self _)) j
  constructor
  · exact (norm_framedFlatRaisingSobolevL_le 1 d.γ d.frame y a C 2 hC norm_flatRaisingSobolevL_one_le_two hL).trans_eq (by dsimp only [C];ring)
  · exact (norm_framedFlatRaisingSobolevL_le 2 d.γ d.frame y a C 40 hC norm_flatRaisingSobolevL_two_le_forty hL).trans_eq (by dsimp only [C];ring)
end ShrinkingSpheres
