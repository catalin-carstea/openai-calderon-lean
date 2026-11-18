import Proof.ParallelCenterDerivative
import Proof.UniformNormalCenterVelocity
import Proof.ImplicitOperatorDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalizedCenterDerivativeBudget (K C D E : ℝ) : ℝ :=
  2*(parallelCenterDerivativeErrorBudget K C D E+secondVelocityPrincipalErrorBudget K C D E+
    2*(C+secondVelocityPrincipalErrorBudget K C D E)*
      (parallelAccelerationBudget K C D+normalVelocitySecondErrorBudget K C D))

lemma NormalCoordinates.contDiffAt_normalizedParallelCenterJacobian {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) :
    ContDiffAt ℝ ∞ (normalizedParallelCenterJacobian g expMap y) v := by
  have hJ := hN.contDiffAt_normalVerticalJacobian hy v hv
  have hInv := (hN.normalVerticalJacobian_isInvertible hy v hv).contDiffAt_map_inverse (n:=∞)
  exact (hInv.comp v hJ).clm_comp (hN.contDiffAt_parallelCenterJacobian hy v hv)

/-- The normalized parallel-center error has a speed-linear velocity derivative.
    The estimate follows from the actual identity J(G-Id)=C-J, so no uncontrolled
    derivative of a chosen inverse or frame enters its constant. -/
theorem NormalCoordinates.normalizedParallelCenterJacobian_derivative_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {K C D E : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (hR : ContinuousAt R y) (v : X) (hv : metricPair g y v v < (R y)^2) (hv1 : ‖v‖ ≤ 1)
    (hInvNorm : ‖(normalVerticalJacobian expMap y v).inverse‖ ≤ 2) :
    ‖fderiv ℝ (normalizedParallelCenterJacobian g expMap y) v‖ ≤
      normalizedCenterDerivativeBudget K C D E*‖v‖ := by
  let J := normalVerticalJacobian expMap y
  let Cn := normalParallelCenterJacobian g expMap y
  let G := normalizedParallelCenterJacobian g expMap y
  let H : X → X →L[ℝ] X := fun w => G w-ContinuousLinearMap.id ℝ X
  let Rn : X → X →L[ℝ] X := fun w => Cn w-J w
  let B := parallelAccelerationBudget K C D+normalVelocitySecondErrorBudget K C D
  let S := secondVelocityPrincipalErrorBudget K C D E
  let DB := parallelCenterDerivativeErrorBudget K C D E+S
  have hB : 0 ≤ B := by
    dsimp [B,parallelAccelerationBudget,parallelVelocityBudget,parallelVariationBudget,
      normalVelocitySecondErrorBudget,normalVariationErrorBudget];positivity
  have hS : 0 ≤ S := by
    dsimp [S,secondVelocityPrincipalErrorBudget,secondNormalVariationBudget,normalVariationErrorBudget];positivity
  have hMix : 0 ≤ mixedParallelVariationBudget K C D E := by
    unfold mixedParallelVariationBudget mixedParallelForceBudget parallelVelocityBudget parallelVariationBudget
    dsimp only
    positivity
  have hDB : 0 ≤ DB := by
    dsimp only [DB,parallelCenterDerivativeErrorBudget]
    have hErr : 0 ≤ normalVariationErrorBudget K C D := by unfold normalVariationErrorBudget;positivity
    positivity
  have hvd := mem_interior_disk_of_metricPair_lt g y v (R y) hv
  have hJ : DifferentiableAt ℝ J v := (hN.contDiffAt_normalVerticalJacobian hy v hv.le).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G v := (hN.contDiffAt_normalizedParallelCenterJacobian hy v hv.le).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ H v := hG.sub (differentiableAt_const _)
  have hIdentity : (fun w => (J w).comp (H w)) =ᶠ[𝓝 v] Rn := by
    filter_upwards [isOpen_interior.mem_nhds hvd] with w hw
    have hInv := hN.normalVerticalJacobian_isInvertible hy w (interior_subset hw)
    apply ContinuousLinearMap.ext
    intro a
    change J w ((J w).inverse (Cn w a)-a) = Cn w a-J w a
    rw [map_sub,hInv.self_apply_inverse]
  have hNJ : ‖fderiv ℝ J v‖ ≤ C+S := by
    have hErr := hN.normalVerticalJacobian_derivative_error hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v hvd hv1
    have hTri : ‖fderiv ℝ J v‖ ≤ ‖fderiv ℝ J v+connectionBilinear g y‖+‖connectionBilinear g y‖ := by
      calc
        _ = ‖(fderiv ℝ J v+connectionBilinear g y)-connectionBilinear g y‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    have hb := hTri.trans (add_le_add hErr (hΓ0 y (hN.center_mem hy)))
    have hSmall := mul_le_mul_of_nonneg_left hv1 hS
    change ‖fderiv ℝ J v‖ ≤ C+S
    change _ ≤ S*‖v‖+C at hb
    linarith
  have hNH : ‖H v‖ ≤ 2*B*‖v‖^2 := by
    have hDiff := hN.parallel_center_sub_vertical_bound hY hΩ hg hK hC hD hΓ0 hΓ1 hy hR v hv hv1
    exact (norm_inverse_comp_sub_id_le (J v) (Cn v)
      (hN.normalVerticalJacobian_isInvertible hy v hv.le) 2 (B*‖v‖^2)
      (by norm_num) hInvNorm hDiff).trans_eq (by ring)
  have hNR : ‖fderiv ℝ Rn v‖ ≤ DB*‖v‖ :=
    hN.parallel_center_sub_vertical_derivative_bound hY hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy hR v hv hv1
  have hb := norm_operator_derivative_of_left_identity J H Rn v hJ hH hIdentity
    (hN.normalVerticalJacobian_isInvertible hy v hv.le) 2 (C+S) (2*B*‖v‖^2) (DB*‖v‖)
    (by norm_num) (by positivity) (by positivity) (by positivity) hInvNorm hNJ hNH hNR
  have hShift : fderiv ℝ H v = fderiv ℝ G v := by
    have hD : HasFDerivAt H (fderiv ℝ G v-0) v := hG.hasFDerivAt.sub (hasFDerivAt_const _ v)
    exact hD.fderiv.trans (sub_zero _)
  rw [hShift] at hb
  have hvSq : ‖v‖^2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
  have hSmall := mul_le_mul_of_nonneg_left hvSq (show 0 ≤ (C+S)*(2*B) by positivity)
  change ‖fderiv ℝ G v‖ ≤ _
  calc
    _ ≤ 2*(DB*‖v‖+(C+S)*(2*B*‖v‖^2)) := hb
    _ ≤ 2*(DB*‖v‖+(C+S)*(2*B)*‖v‖) := by nlinarith only [hSmall]
    _ = _ := by dsimp only [normalizedCenterDerivativeBudget,DB,S,B];ring

end ShrinkingSpheres
