module

import Proof.CalderonN.NormalMapDerivativeTaylor
public import Proof.CalderonN.NormalSecondVariationBounds
public import Proof.CalderonN.NormalVerticalJacobian

import Mathlib.Tactic

/-! Adapted from `NormalJacobianSecondDerivative` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.contDiffAt_normalVerticalJacobian {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) :
    ContDiffAt ℝ ∞ (normalVerticalJacobian expMap y) v := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : ContDiffAt ℝ ∞ expMap (y,v) := hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))
  have hD := hE.fderiv_right (m:=∞) (by simp)
  have hInput : ContDiffAt ℝ ∞ (fun x : (X dim) => (y,x)) v := contDiffAt_const.prodMk contDiffAt_id
  exact (hD.comp v hInput).clm_comp contDiffAt_const

/-- The endpoint second vertical derivative is the position component of the
    actual second initial-velocity variation at time one. -/
lemma NormalCoordinates.second_variation_position_eq {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u k : (X dim)) (hv : v ∈ interior (disk g y (R y))) :
    (secondParameterVariation (normalGeodesicPhase expMap y) u k (v,1)).1 =
      fderiv ℝ (normalVerticalJacobian expMap y) v k u := by
  have hPhase := hN.contDiffAt_phase hy (v,1) (by simpa only [one_smul] using interior_subset hv)
  let J := firstParameterVariation (normalGeodesicPhase expMap y) u
  have hJ : ContDiffAt ℝ ∞ J (v,1) :=
    contDiffAt_firstParameterVariation (normalGeodesicPhase expMap y) u (v,1) hPhase
  have hSlice : ContDiffAt ℝ ∞ (fun x => J (x,1)) v :=
    hJ.comp v (contDiffAt_id.prodMk contDiffAt_const)
  have hFst := (hSlice.differentiableAt (by simp)).hasFDerivAt.fst
  have hNear : (fun x => (J (x,1)).1) =ᶠ[𝓝 v] (fun x => normalVerticalJacobian expMap y x u) := by
    filter_upwards [isOpen_interior.mem_nhds hv] with x hx
    change (normalVelocityVariation expMap y x u 1).1 = _
    simpa only [one_smul] using hN.variation_position_eq hy x u 1
      (by simpa only [one_smul] using interior_subset hx)
  calc
    _ = (fderiv ℝ (fun x => J (x,1)) v k).1 := by
      rw [fderiv_base_slice_of_contDiffAt J v k 1 hJ]
      rfl
    _ = fderiv ℝ (fun x => (J (x,1)).1) v k := by
      rw [hFst.fderiv]
      rfl
    _ = fderiv ℝ (fun x => normalVerticalJacobian expMap y x u) v k :=
      congrArg (fun T : (X dim) →L[ℝ] (X dim) => T k) hNear.fderiv_eq
    _ = _ := by
      have hEval := ((hN.contDiffAt_normalVerticalJacobian hy v (interior_subset hv)).differentiableAt
        (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const u v)
      rw [hEval.fderiv]
      simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
        zero_apply,map_zero,zero_add]

/-- Uniform full operator bound for the second vertical derivative of the actual
    normal map, using only three frozen metric jets. -/
theorem Background.normalVerticalJacobian_derivative_bound {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : (MetricField dim)} {e : (Frame dim)}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : (X dim)} (hy : y ∈ Y) (v : (X dim)) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (normalVerticalJacobian expMap y) v‖ ≤ backgroundSecondNormalVariationBudget dim hm K M := by
  have hBudget : 0 ≤ backgroundSecondNormalVariationBudget dim hm K M := by
    unfold backgroundSecondNormalVariationBudget secondNormalVariationBudget
      backgroundSecondConnectionBudget secondConnectionBudget backgroundConnectionDerivativeBudget
    positivity
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hBudget
  intro k u
  have hS := h.normal_second_velocity_variation_bound hΩ hK hm hN hy v u k hv hv1
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hh := (norm_fst_le (secondParameterVariation (normalGeodesicPhase expMap y) u k (v,1))).trans hS
  rw [hN.second_variation_position_eq hy v u k hv] at hh
  exact hh.trans_eq (by ring)

end CalderonN
