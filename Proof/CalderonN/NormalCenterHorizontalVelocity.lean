module

public import Proof.CalderonN.NormalParallelPosition
public import Proof.CalderonN.NormalVelocitySecondTaylor
public import Proof.CalderonN.NormalCenterBoundaryChainRule

import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalCenterHorizontalVelocity.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The joint variation's position is the actual endpoint derivative. -/
theorem NormalCoordinates.joint_variation_position_eq {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v a b : (X dim)) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    (normalJointVariation expMap y v a b t).1 = fderiv ℝ expMap (y,t • v) (a,t • b) := by
  have hPhase := hN.contDiffAt_jointPhase hy v t hv
  have hd := (hPhase.differentiableAt (by simp)).hasFDerivAt.fst
  have hFst := congrArg (fun L : (((X dim) × (X dim)) × ℝ) →L[ℝ] (X dim) => L ((a,b),0)) hd.fderiv
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,t • v)) (y,t • v) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp)).hasFDerivAt
  have hP : HasFDerivAt (fun p : ((X dim) × (X dim)) × ℝ => p.1) (ContinuousLinearMap.fst ℝ ((X dim) × (X dim)) ℝ) ((y,v),t) := hasFDerivAt_fst
  have hA := (hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,v))).comp ((y,v),t) hP
  have hV := (hasFDerivAt_snd (𝕜:=ℝ) (p:=(y,v))).comp ((y,v),t) hP
  have hT : HasFDerivAt (fun p : ((X dim) × (X dim)) × ℝ => p.2) (ContinuousLinearMap.snd ℝ ((X dim) × (X dim)) ℝ) ((y,v),t) := hasFDerivAt_snd
  have hInput := hA.prodMk (hT.smul hV)
  have he := congrArg (fun L : (((X dim) × (X dim)) × ℝ) →L[ℝ] (X dim) => L ((a,b),0)) (hE.comp ((y,v),t) hInput).fderiv
  change fderiv ℝ (fun p : ((X dim) × (X dim)) × ℝ => expMap (p.1.1,p.2 • p.1.2)) ((y,v),t) ((a,b),0) =
    fderiv ℝ expMap (y,t • v) (a,t • b+(0:ℝ) • v) at he
  have hEq := hFst.symm.trans he
  simpa only [zero_smul,add_zero,normalJointVariation,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst'] using hEq

/-- Parallel-center and vertical endpoint derivatives have the same linear term.
    Torsion-freeness cancels it, leaving a uniform quadratic difference. -/
theorem NormalCoordinates.parallel_center_sub_vertical_bound {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : (X dim)) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1) :
    ‖normalParallelCenterJacobian g expMap y v-normalVerticalJacobian expMap y v‖ ≤
      (parallelAccelerationBudget K C D+normalVelocitySecondErrorBudget K C D)*‖v‖^2 := by
  have hBudget : 0 ≤ parallelAccelerationBudget K C D+normalVelocitySecondErrorBudget K C D := by
    dsimp [parallelAccelerationBudget,parallelVelocityBudget,parallelVariationBudget,
      normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hBudget (sq_nonneg _))
  intro a
  have ht : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hvd := mem_interior_disk_of_metricPair_lt g y v (R y) hv
  have hvd0 : v ∈ disk g y (R y) := hv.le
  have hvT : (1:ℝ) • v ∈ disk g y (R y) := by simpa only [one_smul] using hvd0
  have hP := hN.parallel_position_affine_error hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v a hv hv1 ht
  have hV := hN.position_variation_second_error hΩ hg hK hC hD hΓ0 hΓ1 hy v a hvd hv1 ht
  have hPIdent := hN.joint_variation_position_eq hy v a (-connection g y a v) 1 hvT
  have hVIdent := hN.variation_position_eq hy v a 1 hvT
  simp only [one_smul,one_pow,mul_one] at hPIdent hVIdent hP hV
  have hPIdent' : (normalParallelVariation g expMap y v a 1).1 = normalParallelCenterJacobian g expMap y v a :=
    hPIdent.trans (normalParallelCenterJacobian_apply g expMap y v a).symm
  rw [hPIdent'] at hP
  rw [hVIdent] at hV
  have hSym := connection_symmetric hΩ hg (hN.center_mem hy) a v
  rw [hSym] at hP
  have hEq : normalParallelCenterJacobian g expMap y v a-normalVerticalJacobian expMap y v a =
      (normalParallelCenterJacobian g expMap y v a-a-(-connection g y v a))-
      (normalVerticalJacobian expMap y v a-a+connection g y v a) := by abel
  change ‖normalParallelCenterJacobian g expMap y v a-normalVerticalJacobian expMap y v a‖ ≤ _
  rw [hEq]
  exact (norm_sub_le _ _).trans ((add_le_add hP hV).trans_eq (by ring))

end CalderonN
