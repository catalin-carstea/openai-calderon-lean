import Proof.UniformJointNormalMetricJets
import Proof.NormalMetricQuadraticDerivative
import Proof.MetricKoszul

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma contDiffAt_jointNormalMetricPair (g : MetricField) (E : X × X → X) (p : X × X) (u w : X)
    (hE : ContDiffAt ℝ ∞ E p) (hg : ∀ i j,ContDiffAt ℝ ∞ (fun x => g x i j) (E p)) :
    ContDiffAt ℝ ∞ (jointNormalMetricPair g E u w) p := by
  have hJ := hE.fderiv_right (m:=∞) (by simp)
  have hU (z : X) (i : I) : ContDiffAt ℝ ∞ (fun q => fderiv ℝ E q ((0:X),z) i) p :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.contDiffAt.comp p (hJ.clm_apply contDiffAt_const)
  change ContDiffAt ℝ ∞ (fun q => ∑ i : I,∑ j : I,g (E q) i j * fderiv ℝ E q ((0:X),u) i * fderiv ℝ E q ((0:X),w) j) p
  exact ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
    (((hg i j).comp p hE).mul (hU u i)).mul (hU w j)))

lemma NormalCoordinates.joint_normal_metric_zero {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (e : Frame)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (u w : X) :
    jointNormalMetricPair g expMap u w (y,0) = metricPair g y u w := by
  simp only [jointNormalMetricPair,normalVerticalJacobian,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply,hN.exp_zero hy,hN.vertical_zero hy e hFrame]

/-- The first vertical joint jet of the actual reference normal metric is zero
    at zero velocity; this follows from metric compatibility, not a frame gauge. -/
theorem Background.joint_normal_metric_vertical_zero {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 3 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (u w b : X) :
    fderiv ℝ (jointNormalMetricPair g expMap u w) (y,0) (0,b) = 0 := by
  let C := 243*K*|M ⟨1,by omega⟩|
  let D := backgroundConnectionDerivativeBudget (show 2 ≤ m by omega) K M
  let E := backgroundSecondConnectionBudget hm K M
  have hC : 0 ≤ C := by dsimp [C];positivity
  have hD : 0 ≤ D := by dsimp [D,backgroundConnectionDerivativeBudget];positivity
  have hE : 0 ≤ E := by dsimp [E,backgroundSecondConnectionBudget,secondConnectionBudget];positivity
  have hyΩ := hN.center_mem hy
  have hFrame := h.2.2.2.2.2.2.2 y hyΩ
  have hJ0 : normalVerticalJacobian expMap y 0 = ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro a
    exact hN.vertical_zero hy e hFrame a
  have hInterior : (0:X) ∈ interior (disk g y (R y)) := by
    apply mem_interior_disk_of_metricPair_lt
    have hRpos := (hN.2 y hy).1
    simpa [metricPair] using sq_pos_of_pos hRpos
  have hb := hN.normal_metric_velocity_derivative_small hΩ h.1 hK hC hD hE (abs_nonneg _) (abs_nonneg _)
    (fun x hx => h.connection_budget hK (by omega) hx)
    (fun x hx => h.connection_derivative_budget hΩ hK (by omega) hx)
    (fun x hx => h.connection_second_derivative_budget hΩ hK hm hx)
    (fun x hx i j => (h.reference_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
    (fun x hx i j => (h.reference_second_fderiv_bound (by omega) hx i j).trans (le_abs_self _))
    hy 0 u w b hInterior (by simp) (by rw [hJ0,sub_self,norm_zero];norm_num)
  have hZero : fderiv ℝ (fun z => metricPair g (expMap (y,z))
      (normalVerticalJacobian expMap y z u) (normalVerticalJacobian expMap y z w)) 0 b = 0 := by
    apply abs_nonpos_iff.mp
    simpa only [norm_zero,mul_zero,zero_mul] using hb
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hExp : ContDiffAt ℝ ∞ expMap (y,0) := hReg.contDiffAt
    (hU.mem_nhds (hTube ⟨hy,zero_mem_disk g y (R y)⟩))
  have hB := contDiffAt_jointNormalMetricPair g expMap (y,0) u w hExp
    (fun i j => by rw [hN.exp_zero hy];exact (h.1.1 i j).contDiffAt (hΩ.mem_nhds hyΩ))
  have hInput : HasFDerivAt (fun z : X => (y,z)) (ContinuousLinearMap.inr ℝ X X) 0 :=
    (hasFDerivAt_const y 0).prodMk (hasFDerivAt_id 0)
  have hComp := (hB.differentiableAt (by simp)).hasFDerivAt.comp 0 hInput
  have hh := congrArg (fun L : X →L[ℝ] ℝ => L b) hComp.fderiv
  change fderiv ℝ (fun z => metricPair g (expMap (y,z))
      (normalVerticalJacobian expMap y z u) (normalVerticalJacobian expMap y z w)) 0 b = _ at hh
  exact hh.symm.trans hZero

/-- Differentiating the actual zero-velocity tensor identity identifies its
    center derivative with the genuine metric differential. -/
theorem Background.joint_normal_metric_center_zero {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (u w a : X) :
    fderiv ℝ (jointNormalMetricPair g expMap u w) (y,0) (a,0) = metricDifferential g y a u w := by
  have hNear : (fun x => jointNormalMetricPair g expMap u w (x,0)) =ᶠ[𝓝 y]
      (fun x => metricPair g x u w) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hN.joint_normal_metric_zero hx e (h.2.2.2.2.2.2.2 x (hN.center_mem hx)) u w
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hExp : ContDiffAt ℝ ∞ expMap (y,0) := hReg.contDiffAt
    (hU.mem_nhds (hTube ⟨hy,zero_mem_disk g y (R y)⟩))
  have hB := contDiffAt_jointNormalMetricPair g expMap (y,0) u w hExp
    (fun i j => by rw [hN.exp_zero hy];exact (h.1.1 i j).contDiffAt (hΩ.mem_nhds (hN.center_mem hy)))
  have hInput : HasFDerivAt (fun z : X => (z,(0:X))) (ContinuousLinearMap.inl ℝ X X) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const (0:X) y)
  have hComp := (hB.differentiableAt (by simp)).hasFDerivAt.comp y hInput
  have hh := congrArg (fun L : X →L[ℝ] ℝ => L a) (hComp.fderiv.symm.trans hNear.fderiv_eq)
  exact hh.trans (fderiv_metricPair_fixed hΩ h.1 (hN.center_mem hy) a u w)

end ShrinkingSpheres
