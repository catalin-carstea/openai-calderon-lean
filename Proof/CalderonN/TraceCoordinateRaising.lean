module

public import Proof.CalderonN.TraceFrameCoefficients
public import Proof.CalderonN.SmoothSupportedTraceScalarCalculus
public import Proof.CalderonN.FlatTraceRaisingIdentities

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Contract the leading translation from coordinate directions into the
orthonormal frame, and cancel the double-raising term. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim} {r : X dim → ℝ}
variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (hr : ContDiffOn ℝ ∞ r Y) (hr₀ : ∀ x ∈ Y,r x ≠ 0)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

@[expose] def supportedCoordinateRaising (i : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  ∑ a : I dim,smoothSupportedTraceBaseMul hY (traceFrameCoordinate g e a i)
      (contDiffOn_traceFrameCoordinate hg he a i)*supportedRaising hA hEll S hY a

@[expose] def supportedLeadingTraceVelocity (i : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  smoothSupportedTraceBaseMul hY (fun x => (r x)⁻¹) (hr.inv hr₀)*
    supportedCoordinateRaising hY hg he hA hEll S i

theorem smoothSupportedTraceFiberL_leadingVelocity {x : X dim} (hx : x ∈ Y)
    (i : I dim) (u : SmoothSupportedTraceSection Y) :
    smoothSupportedTraceFiberL x (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i u) =
      (r x)⁻¹ • ∑ a : I dim, traceFrameCoordinate g e a i x •
        smoothTraceRaising (smoothTraceFlatDegree hA hEll S) a (smoothSupportedTraceFiberL x u) := by
  simp only [supportedLeadingTraceVelocity,supportedCoordinateRaising,Module.End.mul_apply,
    smoothSupportedTraceBaseMul_fiber,LinearMap.sum_apply,map_sum,smoothSupportedTraceFiberAction_fiber,
    Finset.smul_sum]

@[expose] def supportedReferenceTraceCoeff (i j : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  smoothSupportedTraceBaseMul hY (fun x => r x*(g x)⁻¹ i j)
    (hr.mul (hg.contDiffOn_inverse_entry hK i j))

include hK in
theorem supportedReferenceVelocity_cross
    (D : I dim → Module.End ℝ (SmoothSupportedTraceSection Y)) :
    (∑ i : I dim,∑ j : I dim,supportedReferenceTraceCoeff hY hg hK hr i j*
      (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i*D j)) =
      ∑ a : I dim,supportedRaising hA hEll S hY a*
        (∑ j : I dim,smoothSupportedTraceBaseMul hY (fun x => e x a j)
          (contDiffOn_vector_component _ (he a) j)*D j) := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  let R := smoothTraceRaising (smoothTraceFlatDegree hA hEll S)
  let U (j : I dim) := smoothSupportedTraceFiberL x (D j u)
  simp only [LinearMap.sum_apply,map_sum,Module.End.mul_apply,supportedReferenceTraceCoeff,
    smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceFiberL_leadingVelocity hY hg he hr hr₀ hA hEll S hx,
    smoothSupportedTraceFiberAction_fiber,map_smul]
  change (∑ i : I dim,∑ j : I dim,(r x*(g x)⁻¹ i j) • ((r x)⁻¹ •
    ∑ a : I dim,traceFrameCoordinate g e a i x • R a (U j))) =
    ∑ a : I dim,∑ j : I dim,e x a j • R a (U j)
  have hStep (i j : I dim) :
      (r x*(g x)⁻¹ i j) • ((r x)⁻¹ • ∑ a : I dim,traceFrameCoordinate g e a i x • R a (U j)) =
        ∑ a : I dim, ((g x)⁻¹ i j*traceFrameCoordinate g e a i x) • R a (U j) := by
    rw [smul_smul,show r x*(g x)⁻¹ i j*(r x)⁻¹ = (g x)⁻¹ i j by field_simp [hr₀ x hx]]
    simp only [Finset.smul_sum,smul_smul]
  simp_rw [hStep]
  rw [Finset.sum_comm (f := fun i j : I dim =>
    ∑ a : I dim,((g x)⁻¹ i j*traceFrameCoordinate g e a i x) • R a (U j)),Finset.sum_comm (f :=
    fun a j : I dim => e x a j • R a (U j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_smul,traceFrameCoordinate_contract_metric g e x (hg.posDef hK hx) a j]

include hK in
theorem supportedReferenceVelocity_square_zero (hn : 3 ≤ dim)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0) :
    (∑ i : I dim,∑ j : I dim,supportedReferenceTraceCoeff hY hg hK hr i j*
      (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i*
        supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S j)) = 0 := by
  rw [supportedReferenceVelocity_cross]
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  let R := smoothTraceRaising (smoothTraceFlatDegree hA hEll S)
  let v := smoothSupportedTraceFiberL x u
  simp only [LinearMap.sum_apply,map_sum,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,
    smoothSupportedTraceFiberL_leadingVelocity hY hg he hr hr₀ hA hEll S hx,
    smoothSupportedTraceFiberAction_fiber,map_smul,LinearMap.zero_apply,map_zero]
  change (∑ a : I dim,∑ j : I dim,e x a j • ((r x)⁻¹ •
      ∑ b : I dim,traceFrameCoordinate g e b j x • R a (R b v))) = 0
  simp only [Finset.smul_sum,smul_smul]
  have hAssoc (a j b : I dim) : e x a j*((r x)⁻¹*traceFrameCoordinate g e b j x) =
      (r x)⁻¹*(e x a j*traceFrameCoordinate g e b j x) := by ring
  have hInner (a : I dim) :
      (∑ j : I dim,∑ b : I dim,(e x a j*traceFrameCoordinate g e b j x) • R a (R b v)) =
        R a (R a v) := by
    classical
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul,traceFrameCoordinate_contract_frame g e x (hframe x hx)]
    simp only [ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hScale (a : I dim) : (∑ j : I dim,∑ b : I dim,
      (e x a j*((r x)⁻¹*traceFrameCoordinate g e b j x)) • R a (R b v)) =
      (r x)⁻¹ • R a (R a v) := by
    simp only [hAssoc]
    rw [← hInner a]
    simp only [Finset.smul_sum,smul_smul]
  simp_rw [hScale,← Finset.smul_sum]
  have hZ := congrArg (fun T : Module.End ℝ (SmoothSphereTrace dim) => T v)
    (sum_smoothTraceRaising_twice hn hA hEll S)
  simp only [LinearMap.sum_apply,Module.End.mul_apply,LinearMap.zero_apply] at hZ
  rw [show (∑ a : I dim,R a (R a v)) = 0 from hZ,smul_zero]

end CalderonN
