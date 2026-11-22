module

public import Proof.CalderonN.NormalThirdVariationBounds
public import Proof.CalderonN.NormalJacobianSecondDerivative

import Proof.CalderonN.LocalFlowVariation
import Mathlib.Tactic

/-! The third initial-velocity variation controls the second spatial
derivative of the Jacobian in the actual normal chart. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 20

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem NormalCoordinates.third_variation_position_eq {Y Ω : Set (X dim)} {g : MetricField dim}
    {E : X dim × X dim → X dim} {R : X dim → ℝ}
    (hN : NormalCoordinates Y Ω g E R) {y : X dim} (hy : y ∈ Y)
    (v u k l : X dim) (hv : v ∈ interior (disk g y (R y))) :
    (thirdParameterVariation (normalGeodesicPhase E y) u k l (v,1)).1 =
      fderiv ℝ (fderiv ℝ (normalVerticalJacobian E y)) v l k u := by
  let P := normalGeodesicPhase E y
  let S := secondParameterVariation P u k
  let J := normalVerticalJacobian E y
  have hP := hN.contDiffAt_phase hy (v,1) (by simpa only [one_smul] using interior_subset hv)
  have hS : ContDiffAt ℝ ∞ S (v,1) := contDiffAt_secondParameterVariation P u k (v,1) hP
  have hJ : ContDiffAt ℝ ∞ J v := hN.contDiffAt_normalVerticalJacobian hy v (interior_subset hv)
  have hSlice : DifferentiableAt ℝ (fun x => S (x,1)) v :=
    (hS.comp v (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hSliceDeriv := hSlice.hasFDerivAt.fst
  have hEq : (fun x => (S (x,1)).1) =ᶠ[𝓝 v] fun x => fderiv ℝ J x k u := by
    filter_upwards [isOpen_interior.mem_nhds hv] with x hx
    exact hN.second_variation_position_eq hy x u k hx
  have hDJ := ((hJ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hD := (hDJ.clm_apply (hasFDerivAt_const k v)).clm_apply (hasFDerivAt_const u v)
  calc
    _ = (fderiv ℝ (fun x => S (x,1)) v l).1 := by
      rw [fderiv_base_slice_of_contDiffAt S v l 1 hS]
      rfl
    _ = fderiv ℝ (fun x => (S (x,1)).1) v l := by rw [hSliceDeriv.fderiv]; rfl
    _ = fderiv ℝ (fun x => fderiv ℝ J x k u) v l :=
      congrArg (fun T : X dim →L[ℝ] X dim => T l) hEq.fderiv_eq
    _ = _ := by
      rw [hD.fderiv]
      simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
        zero_apply,map_zero,zero_add]
      rfl

theorem NormalCoordinates.normalVerticalJacobian_second_derivative_bound
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {K C D E F : ℝ} {g : MetricField dim}
    (hg : Elliptic Ω K g) (hK : 0 < K) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hΓ₀ : ∀ x ∈ Ω, ‖connectionBilinear g x‖ ≤ C)
    (hΓ₁ : ∀ x ∈ Ω, ‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ₂ : ∀ x ∈ Ω, ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    (hΓ₃ : ∀ x ∈ Ω, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) x‖ ≤ F)
    {expMap : X dim × X dim → X dim} {R : X dim → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X dim} (hy : y ∈ Y)
    (v : X dim) (hv : v ∈ interior (disk g y (R y))) (hv₁ : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (fderiv ℝ (normalVerticalJacobian expMap y)) v‖ ≤
      thirdNormalVariationBudget K C D E F := by
  have hB : 0 ≤ thirdNormalVariationBudget K C D E F := by
    dsimp [thirdNormalVariationBudget,secondNormalVariationBudget]
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro l
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro k
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [← hN.third_variation_position_eq hy v u k l hv]
  have h := hN.third_velocity_variation_bound hΩ hg hK hC hD hE hF hΓ₀ hΓ₁ hΓ₂ hΓ₃
    hy v u k l hv hv₁ (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by exact ⟨zero_le_one,le_rfl⟩)
  exact (norm_fst_le _).trans (h.trans_eq (by ring))

end CalderonN
