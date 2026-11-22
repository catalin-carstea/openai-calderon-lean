module

public import Proof.CalderonN.TraceCoordinateRadialCancellation

import Mathlib.Tactic

/-! Separate the coordinate derivative from its angular potential.
Differentiating the latter differentiates only scalar coefficients. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim}
  (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)

@[expose] def traceCoordinateConnectionScalar (g : MetricField dim) (e : Frame dim)
    (j a b : I dim) (x : X dim) : ℝ :=
  (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis j) a b

include hY hg hK he in
omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem contDiffOn_traceCoordinateConnectionScalar (j a b : I dim) :
    ContDiffOn ℝ ∞ (traceCoordinateConnectionScalar g e j a b) Y :=
  contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK e he _ contDiffOn_const a b)

theorem supportedBaseDiff_mul_constFiber
    (i : I dim) (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f Y)
    (S : Module.End ℝ (SmoothSupportedTraceSection Y))
    (hS : smoothSupportedTraceBaseDiff (axis i)*S = S*smoothSupportedTraceBaseDiff (axis i)) :
    let f' := coordDeriv i f
    let hf' : ContDiffOn ℝ ∞ f' Y := (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
    smoothSupportedTraceBaseDiff (axis i)*(smoothSupportedTraceBaseMul hY f hf*S) =
      (smoothSupportedTraceBaseMul hY f hf*S)*smoothSupportedTraceBaseDiff (axis i)+
        smoothSupportedTraceBaseMul hY f' hf'*S := by
  dsimp only
  rw [← mul_assoc,smoothSupportedTraceBaseDiff_mul hY,add_mul,mul_assoc _ _ S,hS,← mul_assoc]
  rfl

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    {r : X dim → ℝ} (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)

@[expose] def supportedCoordinateModelPotential (j : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  (∑ a : I dim,∑ b : I dim,smoothSupportedTraceBaseMul hY (traceCoordinateConnectionScalar g e j a b)
    (contDiffOn_traceCoordinateConnectionScalar hY hg hK he j a b)*supportedRotation hY a b)+
  smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient r j)
    (contDiffOn_traceCoordinateLogGradient hY hlog j)*supportedFlatDegree hA hEll S hY

@[expose] def supportedCoordinateModelPotentialDerivative (i j : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  (∑ a : I dim,∑ b : I dim,smoothSupportedTraceBaseMul hY
    (coordDeriv i (traceCoordinateConnectionScalar g e j a b))
    (((contDiffOn_traceCoordinateConnectionScalar hY hg hK he j a b).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply
      contDiffOn_const)*supportedRotation hY a b)+
  smoothSupportedTraceBaseMul hY (coordDeriv i (traceCoordinateLogGradient r j))
    (((contDiffOn_traceCoordinateLogGradient hY hlog j).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply
      contDiffOn_const)*supportedFlatDegree hA hEll S hY

theorem supportedCoordinateModelDerivative_eq_base_add_potential (j : I dim) :
    supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S j =
      smoothSupportedTraceBaseDiff (axis j)+supportedCoordinateModelPotential hY hg hK he hA hEll S hlog j := by
  unfold supportedCoordinateModelDerivative supportedCoordinateModelPotential
  change supportedCoordinateHorizontal hY hg hK he j+_ = _
  rw [supportedCoordinateHorizontal_eq_base_add_rotation,add_assoc]
  rfl

theorem supportedCoordinateModelPotential_comm_base (hn : 3 ≤ dim) (i j : I dim) :
    let K₀ := supportedCoordinateModelPotential hY hg hK he hA hEll S hlog j
    let D := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
    D*K₀ = K₀*D+supportedCoordinateModelPotentialDerivative hY hg hK he hA hEll S hlog i j := by
  dsimp only
  let D := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let Γ (a b : I dim) := traceCoordinateConnectionScalar g e j a b
  let hΓ (a b : I dim) := contDiffOn_traceCoordinateConnectionScalar hY hg hK he j a b
  let F := traceCoordinateLogGradient r j
  let hF := contDiffOn_traceCoordinateLogGradient hY hlog j
  let R (a b : I dim) := supportedRotation hY a b
  let B := supportedFlatDegree hA hEll S hY
  have hR (a b : I dim) := supportedBaseDiff_mul_constFiber hY i (Γ a b) (hΓ a b)
    (R a b) (supportedRotation_comm_base hn hY a b (axis i))
  have hB := supportedBaseDiff_mul_constFiber hY i F hF B
    (supportedFlatDegree_comm_base hn hA hEll S hY (axis i))
  unfold supportedCoordinateModelPotential supportedCoordinateModelPotentialDerivative
  dsimp only [Γ,R,F,B] at hR hB
  simp only [mul_add,Finset.mul_sum,add_mul,Finset.sum_mul,hR,hB,Finset.sum_add_distrib]
  abel

end CalderonN
