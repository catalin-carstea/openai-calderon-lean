module

public import Proof.CalderonN.TraceCoordinateRaising
public import Proof.CalderonN.TraceFrameHorizontalLinearity
public import Proof.CalderonN.PhysicalTraceModelPairings

import Mathlib.Tactic

/-! The raised principal cross term in chart coordinates is exactly the
physical background model already bounded by the harmonic argument. -/

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
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)

@[expose] def traceCoordinateLogGradient (r : X dim → ℝ) (i : I dim) (x : X dim) : ℝ :=
  fderiv ℝ (fun y => Real.log (r y)) x (axis i)

include hY hlog in
omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem contDiffOn_traceCoordinateLogGradient (i : I dim) :
    ContDiffOn ℝ ∞ (traceCoordinateLogGradient r i) Y :=
  (hlog.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const

omit [Nontrivial (Fin dim)] in
theorem traceModelLogGradient_eq_sum (a : I dim) (x : X dim) :
    traceModelLogGradient e r a x = ∑ j : I dim,e x a j*traceCoordinateLogGradient r j x := by
  unfold traceModelLogGradient traceCoordinateLogGradient
  conv_lhs => rw [← axis_sum_chart (e x a)]
  simp only [map_sum,map_smul,smul_eq_mul]

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)

@[expose] def supportedCoordinateModelDerivative (i : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  supportedHorizontal hY hg hK he (fun _ => axis i) contDiffOn_const+
    smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient r i)
      (contDiffOn_traceCoordinateLogGradient hY hlog i)*supportedFlatDegree hA hEll S hY

theorem supportedFrameModelDerivative_eq_sum
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0) (a : I dim) :
    supportedHorizontal hY hg hK he (fun x => e x a) (he a)+
      smoothSupportedTraceBaseMul hY (traceModelLogGradient e r a)
        (contDiffOn_traceModelLogGradient hY he hlog a)*supportedFlatDegree hA hEll S hY =
    ∑ j : I dim,smoothSupportedTraceBaseMul hY (fun x => e x a j)
      (contDiffOn_vector_component _ (he a) j)*supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S j := by
  rw [supportedHorizontal_axis_sum hY hg hK he hframe _ (he a)]
  let D (j : I dim) := supportedHorizontal hY hg hK he (fun _ => axis j) contDiffOn_const
  let Iₛ := supportedFlatDegree hA hEll S hY
  let M (j : I dim) := smoothSupportedTraceBaseMul hY (fun x => e x a j) (contDiffOn_vector_component _ (he a) j)
  let F (j : I dim) := smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient r j)
      (contDiffOn_traceCoordinateLogGradient hY hlog j)
  let L := smoothSupportedTraceBaseMul hY (traceModelLogGradient e r a)
      (contDiffOn_traceModelLogGradient hY he hlog a)
  change (∑ j : I dim,M j*D j)+L*Iₛ = ∑ j : I dim,M j*(D j+F j*Iₛ)
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  simp only [L,M,F,LinearMap.sum_apply,map_sum,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,smul_smul]
  rw [← Finset.sum_smul,traceModelLogGradient_eq_sum]

theorem supportedCoordinateRaising_cross_eq_model
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    (hr : ContDiffOn ℝ ∞ r Y) (hr₀ : ∀ x ∈ Y,r x ≠ 0) :
    (∑ i : I dim,∑ j : I dim,supportedReferenceTraceCoeff hY hg hK hr i j*
      (supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S i*
        supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S j)) =
      physicalRaisingModel hY hg hK he hlog hA hEll S := by
  rw [supportedReferenceVelocity_cross]
  change _ = ∑ a : I dim,supportedRaising hA hEll S hY a *
    (supportedHorizontal hY hg hK he (fun x => e x a) (he a)+
      smoothSupportedTraceBaseMul hY (traceModelLogGradient e r a)
        (contDiffOn_traceModelLogGradient hY he hlog a)*supportedFlatDegree hA hEll S hY)
  apply Finset.sum_congr rfl
  intro i _
  rw [← supportedFrameModelDerivative_eq_sum hY hg hK he hlog hA hEll S hframe i]

end CalderonN
