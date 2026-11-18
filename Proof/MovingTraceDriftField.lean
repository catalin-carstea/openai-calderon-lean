import Proof.PhysicalOutputRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff
namespace ShrinkingSpheres

/-- The second-metric drift part of the actual moving trace. -/
def movingTraceDrift (g g₂ : MetricField) (r : X → ℝ) (A : TraceAdjoint) (φ : Field) : Field :=
  fun p => r p.1 • ∑ k : I,drift g g₂ p.1 k • traceDerivative g A k φ p

/-- The principal and connection part, with the drift treated separately. -/
def principalMovingTrace (g g₂ : MetricField) (r : X → ℝ) (A : TraceAdjoint) (φ : Field) : Field :=
  fun p => (r p.1 : ℂ)*(∑ i : I,∑ j : I,(principal g g₂ p.1 i j : ℂ)*
    (traceDerivative g A i (traceDerivative g A j φ) p-
      ∑ k : I,(christoffel g p.1 k i j : ℂ)*traceDerivative g A k φ p))

theorem movingTrace_principal_add_drift (g g₂ : MetricField) (r : X → ℝ) (A : TraceAdjoint)
    (φ : Field) (p : X × X) :
    movingTrace g g₂ r A φ p = principalMovingTrace g g₂ r A φ p+movingTraceDrift g g₂ r A φ p := by
  simp only [movingTrace,principalMovingTrace,movingTraceDrift,Complex.real_smul]
  rw [mul_add]

theorem smoothNear_movingTraceDrift {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K)
    {e : Frame} {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hr : ContDiffOn ℝ ∞ r Y) (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) :
    smoothNear (movingTraceDrift g g₂ r A φ) (bundle Y g) := by
  have hW (k : I) := smoothNear_traceDerivative hY h hK hA hφ k
  have hD (k : I) := smoothNear_base (g:=g) hY (contDiffOn_drift hY h h₂ hK k)
  have hR := smoothNear_base (g:=g) hY hr
  have hProduct := hR.mul (smoothNear.finset_sum Finset.univ _ (fun k _ => (hD k).mul (hW k)))
  have hEq : movingTraceDrift g g₂ r A φ = (fun p => (r p.1 : ℂ)*
      ∑ k : I,(drift g g₂ p.1 k : ℂ)*traceDerivative g A k φ p) := by
    funext p
    simp only [movingTraceDrift,Complex.real_smul]
  rw [hEq]
  exact hProduct

theorem smoothNear_principalMovingTrace {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K)
    {e : Frame} {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hr : ContDiffOn ℝ ∞ r Y) (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) :
    smoothNear (principalMovingTrace g g₂ r A φ) (bundle Y g) := by
  have hEq : principalMovingTrace g g₂ r A φ =
      (fun p => movingTrace g g₂ r A φ p+ -movingTraceDrift g g₂ r A φ p) := by
    funext p
    rw [movingTrace_principal_add_drift]
    abel
  rw [hEq]
  exact (smoothNear_movingTrace hY h h₂ hK hr hA hφ).add
    (smoothNear_movingTraceDrift hY h h₂ hK hr hA hφ).neg

theorem movingTraceDrift_zero_of_support {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ g₂ : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A) (hD : Dirichlet Y g g₁ expMap r)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) (S : Set X) (hS : IsClosed S)
    (hzero : ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,φ (y,w) = 0)
    {y : X} (hy : y ∈ Y \ S) (w : X) (hw : w ∈ sphereAt g y) :
    movingTraceDrift g g₂ r A φ (y,w) = 0 := by
  have hW (k : I) := traceDerivative_zero_of_support hY h hK e he hframe hA hD hφ S hS hzero k hy w hw
  simp only [movingTraceDrift,hW,smul_zero,Finset.sum_const_zero]

theorem principalMovingTrace_zero_of_support {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ g₂ : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A) (hD : Dirichlet Y g g₁ expMap r)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) (S : Set X) (hS : IsClosed S)
    (hzero : ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,φ (y,w) = 0)
    {y : X} (hy : y ∈ Y \ S) (w : X) (hw : w ∈ sphereAt g y) :
    principalMovingTrace g g₂ r A φ (y,w) = 0 := by
  have hFull := movingTrace_zero_of_support (g₂:=g₂) hY h hK e he hframe hA hD hφ S hS hzero hy w hw
  have hDrift := movingTraceDrift_zero_of_support (g₂:=g₂) hY h hK e he hframe hA hD hφ S hS hzero hy w hw
  rw [movingTrace_principal_add_drift,hDrift,add_zero] at hFull
  exact hFull

end ShrinkingSpheres
