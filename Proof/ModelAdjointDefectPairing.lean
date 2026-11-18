import Proof.ModelAdjointDefectCoefficient
import Proof.CanonicalCoarseTripleEnergy
import Proof.Archive.NativeHarmonicHalfCoarseDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

def modelAdjointDefectRaisingSobolevL (s : ℝ) (d : Data) (y : X) :
    SphereSobolev s →L[ℝ] SphereSobolev (s-1) :=
  ∑ i : I,modelLogRadiusCoefficient d i y • flatRaisingSobolevL s i

lemma modelAdjointDefectRaisingSobolevL_inclusion (s t : ℝ) (hst : t ≤ s) (d : Data) (y : X) :
    (modelAdjointDefectRaisingSobolevL t d y).comp (sphereSobolevInclusionL s t hst)=
      (sphereSobolevInclusionL (s-1) (t-1) (by linarith)).comp (modelAdjointDefectRaisingSobolevL s d y) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [modelAdjointDefectRaisingSobolevL,ContinuousLinearMap.comp_apply,_root_.sum_apply,
    _root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => modelLogRadiusCoefficient d i y • z)
    (DFunLike.congr_fun (flatRaisingSobolevL_inclusion s t hst i) u)

lemma norm_modelAdjointDefectRaisingSobolevL_le (s : ℝ) (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    ‖modelAdjointDefectRaisingSobolevL s d y‖ ≤
      (∑ i : I,‖flatRaisingSobolevL s i‖)*beta d.γ d.radius y := by
  calc
    _ ≤ ∑ i : I,‖modelLogRadiusCoefficient d i y • flatRaisingSobolevL s i‖ := norm_sum_le _ _
    _ ≤ ∑ i : I,beta d.γ d.radius y*‖flatRaisingSobolevL s i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (frame_logRadius_component_bound d.γ d.frame d.radius y hFrame i) (norm_nonneg _)
    _ = _ := by rw [←Finset.mul_sum];ring

lemma modelAdjointDefectCoarseL_inner_right (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X) (u v : SphereSobolev 1) :
    ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,modelAdjointDefectCoarseL d y v⟫_ℝ=
      ⟪modelAdjointDefectRaisingSobolevL 1 d y u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ := by
  simp only [modelAdjointDefectCoarseL,modelAdjointDefectRaisingSobolevL,_root_.sum_apply,_root_.smul_apply,
    inner_sum,sum_inner,real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun r : ℝ => modelLogRadiusCoefficient d i y*r) (flat_raising_lowering_inner Q hQ i u v).symm

lemma modelAdjointDefectCoarseL_half_graph (d : Data) (y : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (modelAdjointDefectCoarseL d y)=
      (modelAdjointDefectSobolevL (1/2:ℝ) d y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  have hI : sphereSobolevInclusionL ((1:ℝ)-1) ((1/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) := by congr 1 <;> norm_num
  have hh := modelAdjointDefectSobolevL_inclusion 1 (1/2:ℝ) (by norm_num) d y
  rw [hI] at hh
  exact hh.symm

/-- Genuine balanced angular first-order form for the SAME model defect. -/
lemma abs_modelAdjointDefectCoarseL_form_le_half (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (u v : SphereSobolev 1) :
    |⟪sphereSobolevInclusionL 1 0 (by norm_num) u,modelAdjointDefectCoarseL d y v⟫_ℝ| ≤
      (∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖)*beta d.γ d.radius y*
        ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u‖*
        ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v‖ := by
  let J := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
  let Z := modelAdjointDefectSobolevL (1/2:ℝ) d y
  have hG := DFunLike.congr_fun (modelAdjointDefectCoarseL_half_graph d y) v
  simp only [ContinuousLinearMap.comp_apply] at hG
  have hPair : ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,modelAdjointDefectCoarseL d y v⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) (J u) (Z (J v)) := by
    calc
      _ = sphereSobolevDualPairing (1/2:ℝ) (J u)
          (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) (modelAdjointDefectCoarseL d y v)) := by
        have hh := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) (J u) (modelAdjointDefectCoarseL d y v)
        simpa only [J,sphereSobolevInclusionL_trans_apply] using hh.symm
      _ = _ := congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) (J u) z) hG
  have hN := norm_modelAdjointDefectSobolevL_le (1/2:ℝ) d y hFrame
  rw [hPair]
  calc
    _ ≤ ‖J u‖*‖Z (J v)‖ := abs_sphereSobolevDualPairing_le (1/2:ℝ) (J u) (Z (J v))
    _ ≤ ‖J u‖*(‖Z‖*‖J v‖) := mul_le_mul_of_nonneg_left (Z.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖J u‖*(((∑ i : I,‖flatLoweringSobolevL (1/2:ℝ) i‖)*beta d.γ d.radius y)*‖J v‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- Genuine mass/first form, using the actual higher raising adjoint.
The source is H3/2 and the horizontal section is H1/2. -/
lemma abs_modelAdjointDefectCoarseL_mass_first_bound (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev 1) :
    |⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,modelAdjointDefectCoarseL d y v⟫_ℝ| ≤
      (∑ i : I,‖flatRaisingSobolevL (3/2:ℝ) i‖)*beta d.γ d.radius y*‖u‖*
        ‖sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v‖ := by
  let J := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  let V := sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) v
  let H := modelAdjointDefectRaisingSobolevL (3/2:ℝ) d y u
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  have hh := modelAdjointDefectRaisingSobolevL_inclusion (3/2:ℝ) 1 (by norm_num) d y
  rw [hI] at hh
  have hLift := DFunLike.congr_fun hh u
  simp only [ContinuousLinearMap.comp_apply] at hLift
  have hPair : ⟪sphereSobolevInclusionL (3/2:ℝ) 0 (by norm_num) u,modelAdjointDefectCoarseL d y v⟫_ℝ=
      ⟪J H,J V⟫_ℝ := by
    calc
      _ = ⟪sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u),
          modelAdjointDefectCoarseL d y v⟫_ℝ := by rw [sphereSobolevInclusionL_trans_apply]
      _ = ⟪modelAdjointDefectRaisingSobolevL 1 d y (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u),
          sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ := modelAdjointDefectCoarseL_inner_right Q hQ d y _ _
      _ = _ := by rw [hLift];simp only [J,H,V,sphereSobolevInclusionL_trans_apply]
  have hHN : ‖H‖ ≤ ((∑ i : I,‖flatRaisingSobolevL (3/2:ℝ) i‖)*beta d.γ d.radius y)*‖u‖ :=
    ((modelAdjointDefectRaisingSobolevL (3/2:ℝ) d y).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_modelAdjointDefectRaisingSobolevL_le (3/2:ℝ) d y hFrame) (norm_nonneg _))
  rw [hPair]
  calc
    _ ≤ ‖J H‖*‖J V‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖H‖*‖V‖ := mul_le_mul (norm_sphereSobolevInclusionL_apply_le (1/2:ℝ) 0 (by norm_num) H)
      (norm_sphereSobolevInclusionL_apply_le (1/2:ℝ) 0 (by norm_num) V) (norm_nonneg _) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right hHN (norm_nonneg _)

end ShrinkingSpheres
