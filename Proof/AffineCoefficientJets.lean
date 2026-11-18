import Proof.LocalCoefficientRepresentation
import Proof.FullCoefficientEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

theorem hasFDerivAt_scalar_affine_entry (L : X →L[ℝ] ℝ) (c r δ : ℝ) (x : X) :
    HasFDerivAt (fun z => (c+r*L z)*δ) ((r*δ) • L) x := by
  have h := ((hasFDerivAt_const (𝕜:=ℝ) c x).add (L.hasFDerivAt.const_mul r)).mul_const δ
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.smul_apply,zero_add,smul_eq_mul]
  ring

/-- The actual coefficient representatives retain the affine Taylor error as
    a genuine smooth germ, independently of their exterior extensions. -/
theorem coefficient_affine_remainder_germ {a : MetricField}
    (F F0 F1 : SmoothCoefficientMatrix 2) (c r : ℝ) (L : X →L[ℝ] ℝ)
    (hRep : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j))
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => L z*(1:Mat) i j))
    {x : X} (hx : x ∈ (ballOpens : Set X)) (i j : I) :
    coefficientValue 2 ((F-c • F0-r • F1) i j) =ᶠ[𝓝 x]
      (fun z => a z i j-(c+r*L z)*(1:Mat) i j) := by
  have hG := coefficient_difference_germ F F0 c hRep hF0 hx i j
  filter_upwards [hG,hF1 x (unitBall_subset_closedBall_two hx) i j] with z hz hz1
  change coefficientValue 2 ((F-c • F0) i j-r • F1 i j) z = _
  rw [coefficientValue_sub_local,coefficientValue_smul]
  change coefficientValue 2 ((F-c • F0) i j) z-r*coefficientValue 2 (F1 i j) z = _
  rw [hz,hz1]
  ring

/-- Only the covector norm is needed to control the compact affine model in
    the local C1 operator norm. -/
theorem linear_scalar_coefficient_local_bounds (F1 : SmoothCoefficientMatrix 2)
    (L : X →L[ℝ] ℝ) (P : ℝ) (hP : 0 ≤ P) (hLn : ‖L‖ ≤ P)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => L z*(1:Mat) i j)) :
    (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F1 i j) x| ≤ P) ∧
    (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) x‖ ≤ P) := by
  have hδ (i j : I) : |(1:Mat) i j| ≤ 1 := by simp only [Matrix.one_apply];split_ifs <;> norm_num
  constructor
  · intro i j x hx
    rw [(hF1 x (unitBall_subset_closedBall_two hx) i j).eq_of_nhds,abs_mul]
    have hx1 : ‖x‖ ≤ 1 := by
      have hx' : ‖x‖ < 1 := by simpa only [coe_ballOpens,OAI.AnisotropicCalderon.B,Metric.mem_ball,dist_zero_right] using hx
      exact hx'.le
    have hLx : |L x| ≤ P := (L.le_opNorm x).trans
      ((mul_le_mul hLn hx1 (norm_nonneg _) hP).trans_eq (mul_one _))
    exact (mul_le_mul hLx (hδ i j) (abs_nonneg _) hP).trans_eq (mul_one _)
  · intro i j x hx
    have hLin : HasFDerivAt (fun z => L z*(1:Mat) i j) ((1:Mat) i j • L) x := by
      simpa only [zero_add,one_mul,one_smul] using hasFDerivAt_scalar_affine_entry L 0 1 ((1:Mat) i j) x
    rw [(hF1 x (unitBall_subset_closedBall_two hx) i j).fderiv_eq,hLin.fderiv,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul (hδ i j) hLn (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Transfer value and derivative Taylor estimates to the actual compact jets. -/
theorem coefficient_affine_remainder_local_bounds {a : MetricField}
    (F F0 F1 : SmoothCoefficientMatrix 2) (c r Q : ℝ) (L : X →L[ℝ] ℝ)
    (hRep : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F i j) =ᶠ[𝓝 x] (fun z => a z i j))
    (hF0 : ∀ x ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 x = 1)
    (hF1 : ∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,
      coefficientValue 2 (F1 i j) =ᶠ[𝓝 x] (fun z => L z*(1:Mat) i j))
    (ha : ∀ i j,∀ x ∈ (ballOpens : Set X),DifferentiableAt ℝ (fun z => a z i j) x)
    (hTaylor : ∀ x ∈ (ballOpens : Set X),∀ i j,
      |a x i j-(c+r*L x)*(1:Mat) i j| ≤ Q*r^2 ∧
      ‖fderiv ℝ (fun z => a z i j) x-(r*(1:Mat) i j) • L‖ ≤ Q*r^2) :
    (∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 ((F-c • F0-r • F1) i j) x| ≤ Q*r^2) ∧
    (∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 ((F-c • F0-r • F1) i j)) x‖ ≤ Q*r^2) := by
  constructor
  · intro i j x hx
    rw [(coefficient_affine_remainder_germ F F0 F1 c r L hRep hF0 hF1 hx i j).eq_of_nhds]
    exact (hTaylor x hx i j).1
  · intro i j x hx
    have hAff := hasFDerivAt_scalar_affine_entry L c r ((1:Mat) i j) x
    have hErr : HasFDerivAt (fun z => a z i j-(c+r*L z)*(1:Mat) i j)
        (fderiv ℝ (fun z => a z i j) x-(r*(1:Mat) i j) • L) x := (ha i j x hx).hasFDerivAt.sub hAff
    rw [(coefficient_affine_remainder_germ F F0 F1 c r L hRep hF0 hF1 hx i j).fderiv_eq,hErr.fderiv]
    exact (hTaylor x hx i j).2

end ShrinkingSpheres
