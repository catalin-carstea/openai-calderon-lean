module

public import Proof.CalderonN.SupportedMovingTrace
public import Proof.CalderonN.SmoothSupportedTraceScalarCalculus

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Write the Christoffel terms of the actual moving trace as a single
scalar drift times the first-order trace derivative. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g g₂ : MetricField dim} {e : Frame dim} {r : X dim → ℝ}
variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (hr : ContDiffOn ℝ ∞ r Y)
  (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal g g₂ x i j) Y)
  (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift g g₂ x k) Y)

@[expose] def traceCoordinateDrift (g g₂ : MetricField dim) (k : I dim) (x : X dim) : ℝ :=
  drift g g₂ x k-∑ i : I dim,∑ j : I dim,principal g g₂ x i j*christoffel g x k i j

include hY hg hK hQ hb in
omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem contDiffOn_traceCoordinateDrift (k : I dim) :
    ContDiffOn ℝ ∞ (traceCoordinateDrift g g₂ k) Y :=
  (hb k).sub (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (hQ i j).mul (hg.contDiffOn_christoffel hY hK k i j))

@[expose] def supportedPrincipalTraceCoeff (i j : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  smoothSupportedTraceBaseMul hY (fun x => r x*principal g g₂ x i j) (hr.mul (hQ i j))

@[expose] def supportedCoordinateTraceDrift (k : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  smoothSupportedTraceBaseMul hY (fun x => r x*traceCoordinateDrift g g₂ k x)
    (hr.mul (contDiffOn_traceCoordinateDrift hY hg hK hQ hb k))

private theorem trace_square_drift_rearrange {R ι : Type*} [Ring R] [Fintype ι]
    (A : ι → ι → R) (Γ : ι → ι → ι → R) (b W : ι → R) :
    (∑ i,∑ j,A i j*(W i*W j-∑ k,Γ k i j*W k))+(∑ k,b k*W k) =
      (∑ i,∑ j,A i j*(W i*W j))+(∑ k,(b k-∑ i,∑ j,A i j*Γ k i j)*W k) := by
  have hSum :
      (∑ i,∑ j,∑ k,A i j*Γ k i j*W k) = ∑ k,∑ i,∑ j,A i j*Γ k i j*W k := by
    simp_rw [Finset.sum_comm (f := fun j k => A _ j*Γ k _ j*W k)]
    exact Finset.sum_comm
  simp only [mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul,← mul_assoc,hSum]
  abel

theorem supportedMovingTrace_eq_coordinateSquare
    (C : I dim → X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (C i)) :
    let W := supportedTraceDerivative hY hg hK he C hC
    supportedMovingTrace hY hg hK he C hC hr hQ hb =
      (∑ i : I dim,∑ j : I dim,supportedPrincipalTraceCoeff hY hr hQ i j*(W i*W j))+
        (∑ k : I dim,supportedCoordinateTraceDrift hY hg hK hr hQ hb k*W k) := by
  let W := supportedTraceDerivative hY hg hK he C hC
  let R := smoothSupportedTraceBaseMul hY r hr
  let A (i j : I dim) := smoothSupportedTraceBaseMul hY (fun x => principal g g₂ x i j) (hQ i j)
  let Γ (k i j : I dim) := smoothSupportedTraceBaseMul hY (fun x => christoffel g x k i j)
    (hg.contDiffOn_christoffel hY hK k i j)
  let b (k : I dim) := smoothSupportedTraceBaseMul hY (fun x => drift g g₂ x k) (hb k)
  have hB (k : I dim) : R*(b k-∑ i : I dim,∑ j : I dim,A i j*Γ k i j) =
      supportedCoordinateTraceDrift hY hg hK hr hQ hb k := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [R,b,A,Γ,supportedCoordinateTraceDrift,traceCoordinateDrift,Module.End.mul_apply,
      LinearMap.sub_apply,LinearMap.sum_apply,map_sub,map_sum,smoothSupportedTraceBaseMul_fiber,smul_smul]
    simp only [← Finset.sum_smul,← sub_smul]
    simp only [mul_sub,Finset.mul_sum]
  have hA (i j : I dim) : R*A i j = supportedPrincipalTraceCoeff hY hr hQ i j := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [R,A,supportedPrincipalTraceCoeff,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,smul_smul]
  change R*((∑ i : I dim,∑ j : I dim,A i j*(W i*W j-∑ k : I dim,Γ k i j*W k))+
    (∑ k : I dim,b k*W k)) = _
  rw [trace_square_drift_rearrange A Γ b W]
  simp only [mul_add,Finset.mul_sum,← mul_assoc,hA,hB]
  rfl

end CalderonN
