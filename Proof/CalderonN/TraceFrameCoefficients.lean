module

public import Proof.CalderonN.FrameOperators
public import Proof.CalderonN.SmoothSupportedTraceHorizontal

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Coordinate contraction identities for the normalized moving trace. -/

public section

noncomputable section
open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2100000
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem axis_sum_chart (v : X dim) : (∑ i : I dim,v i • axis i) = v := by
  classical
  ext i
  simp [axis,Pi.single_apply,mul_ite]

@[expose] def traceFrameCoordinate (g : MetricField dim) (e : Frame dim)
    (a i : I dim) (x : X dim) : ℝ :=
  frameCoordinatesL g x (e x) (axis i) a

theorem contDiffOn_traceFrameCoordinate {Y : Set (X dim)} {K : ℝ}
    {g : MetricField dim} {e : Frame dim} (hg : Elliptic Y K g)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y) (a i : I dim) :
    ContDiffOn ℝ ∞ (traceFrameCoordinate g e a i) Y := by
  apply (hg.contDiffOn_metricPair (fun _ => axis i) (fun x => e x a) contDiffOn_const (he a)).congr
  intro x _
  rw [traceFrameCoordinate,frameCoordinatesL_apply]
  rfl

theorem traceFrameCoordinate_contract_metric (g : MetricField dim) (e : Frame dim)
    (x : X dim) (hg : (g x).PosDef) (a j : I dim) :
    (∑ i : I dim,(g x)⁻¹ i j*traceFrameCoordinate g e a i x) = e x a j := by
  have hG : (g x)⁻¹ * (g x) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hg.det_pos.ne')
  have hSym (i : I dim) : (g x)⁻¹ i j = (g x)⁻¹ j i :=
    congrFun (congrFun hg.inv.isHermitian.isSymm.eq j) i
  simp_rw [hSym,traceFrameCoordinate,frameCoordinatesL_apply]
  change (∑ i : I dim,(g x)⁻¹ j i*metricPair g x (axis i) (e x a)) = e x a j
  simp_rw [metricPair_axis_left]
  change ((g x)⁻¹ *ᵥ (g x) *ᵥ (fun i => e x a i)) j = e x a j
  rw [Matrix.mulVec_mulVec,hG,Matrix.one_mulVec]

theorem traceFrameCoordinate_contract_frame (g : MetricField dim) (e : Frame dim)
    (x : X dim) (he : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (a b : I dim) :
    (∑ j : I dim,e x a j*traceFrameCoordinate g e b j x) = if a=b then 1 else 0 := by
  have h := congrArg (frameCoordinatesL g x (e x)) (axis_sum_chart (e x a))
  simp only [map_sum,map_smul] at h
  have ha := congrArg (fun v : X dim => v b) h
  have heₐ : frameVectorL (e x) (axis a) = e x a := by
    rw [frameVectorL_apply (e x) (axis a) x]
    simp [frameVector,axis,PiLp.single_apply]
  rw [show frameCoordinatesL g x (e x) (e x a) = axis a from
    heₐ ▸ frameCoordinatesL_frameVectorL g x (e x) he (axis a)] at ha
  simpa [traceFrameCoordinate,axis,PiLp.single_apply,eq_comm] using ha

theorem traceFrameCoordinate_double_contract (g : MetricField dim) (e : Frame dim)
    (x : X dim) (hg : (g x).PosDef)
    (he : ∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0) (a b : I dim) :
    (∑ i : I dim,∑ j : I dim,(g x)⁻¹ i j*traceFrameCoordinate g e a i x*
      traceFrameCoordinate g e b j x) = if a=b then 1 else 0 := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,traceFrameCoordinate_contract_metric g e x hg a]
  exact traceFrameCoordinate_contract_frame _ _ _ he a b

end CalderonN
