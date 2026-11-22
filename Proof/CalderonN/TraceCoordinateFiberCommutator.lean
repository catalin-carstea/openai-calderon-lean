module

public import Proof.CalderonN.ActualSupportedLowerOrderVelocity
public import Proof.CalderonN.SmoothTraceRotationBracket

import Mathlib.Tactic

/-! Evaluate a coordinate-model commutator as a fiber derivative plus
the angular connection and degree commutators. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceFiberDerivative_adjoint (hn : 3 ≤ dim)
    (hY : IsOpen Y) (F G : X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hF : SmoothSupportedTraceFiberRegular Y F) (hG : SmoothSupportedTraceFiberRegular Y G)
    (hAdj : ∀ x ∈ Y,SmoothTraceAdjoint hn (F x) (G x)) (a : X dim) {x : X dim} (hx : x ∈ Y) :
    SmoothTraceAdjoint hn (smoothSupportedTraceFiberDerivative hY F hF a x)
      (smoothSupportedTraceFiberDerivative hY G hG a x) := by
  intro u v
  have hEq : (fun y => ⟪smoothSphereTraceL2 hn (F y u),smoothSphereTraceL2 hn v⟫_ℝ) =ᶠ[𝓝 x]
      fun y => ⟪smoothSphereTraceL2 hn (G y v),smoothSphereTraceL2 hn u⟫_ℝ := by
    filter_upwards [hY.mem_nhds hx] with y hy
    exact (hAdj y hy u v).trans (real_inner_comm _ _)
  rw [← fderiv_smoothTrace_fiber_matrix_element hn hY hx F hF a u v,
    real_inner_comm,← fderiv_smoothTrace_fiber_matrix_element hn hY hx G hG a v u,hEq.fderiv_eq]

variable (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim} {r : X dim → ℝ}
  (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

theorem supportedCoordinateModelDerivative_comm_fiber
    (F : X dim → Module.End ℝ (SmoothSphereTrace dim)) (hF : SmoothSupportedTraceFiberRegular Y F)
    (i : I dim) {x : X dim} (hx : x ∈ Y) (u : SmoothSupportedTraceSection Y) :
    let P := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i
    let T := smoothSupportedTraceFiberAction hY F hF
    let B := smoothTraceFlatDegree hA hEll S
    let D := smoothSupportedTraceFiberDerivative hY F hF (axis i) x
    let Γ (a b : I dim) := (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis i) a b
    let l := traceCoordinateLogGradient r i x
    smoothSupportedTraceFiberL x ((P*T-T*P) u) =
      (D+(∑ a : I dim,∑ b : I dim,Γ a b • smoothTraceAngularComm a b (F x))+
        l • (B*F x-F x*B)) (smoothSupportedTraceFiberL x u) := by
  dsimp only
  let P := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i
  let T := smoothSupportedTraceFiberAction hY F hF
  let Q := supportedFlatDegree hA hEll S hY
  let D := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let c (a b : I dim) (x : X dim) := -(1/2:ℝ)*frameConnectionCoefficient g e x (axis i) a b
  let C (a b : I dim) := smoothSupportedTraceBaseMul hY (c a b)
    (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK e he _ contDiffOn_const a b))
  let L := smoothSupportedTraceBaseMul hY (traceCoordinateLogGradient r i)
    (contDiffOn_traceCoordinateLogGradient hY hlog i)
  let R := supportedRotation (Y:=Y) hY
  have hP : P = D+(∑ a : I dim,∑ b : I dim,C a b*R a b)+L*Q := by
    unfold P supportedCoordinateModelDerivative
    exact congrArg (fun H => H+L*Q)
      (supportedCoordinateHorizontal_eq_base_add_rotation hY hg hK he i)
  have hC (a b : I dim) : C a b*T = T*C a b :=
    smoothSupportedTraceBaseMul_comm_fiber hY _ _ F hF
  have hL : L*T = T*L := smoothSupportedTraceBaseMul_comm_fiber hY _ _ F hF
  have hTerm (a b : I dim) :
      (C a b*R a b)*T-T*(C a b*R a b) = C a b*(R a b*T-T*R a b) := by
    rw [mul_assoc (C a b),← mul_assoc T,← hC a b,mul_assoc (C a b)]
    exact (mul_sub (C a b) (R a b*T) (T*R a b)).symm
  have hDeg : (L*Q)*T-T*(L*Q) = L*(Q*T-T*Q) := by
    rw [mul_assoc L,← mul_assoc T,← hL,mul_assoc L]
    exact (mul_sub L (Q*T) (T*Q)).symm
  have hEq : P*T-T*P = (D*T-T*D)+
      (∑ a : I dim,∑ b : I dim,C a b*(R a b*T-T*R a b))+L*(Q*T-T*Q) := by
    rw [hP,add_mul,mul_add,add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]
    have hSum : (∑ a : I dim,(∑ b : I dim,C a b*R a b)*T)-(∑ a : I dim,T*(∑ b : I dim,C a b*R a b)) =
        ∑ a : I dim,∑ b : I dim,C a b*(R a b*T-T*R a b) := by
      rw [← Finset.sum_sub_distrib (f:=fun a : I dim => (∑ b : I dim,C a b*R a b)*T)
        (g:=fun a : I dim => T*(∑ b : I dim,C a b*R a b))]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib (f:=fun b : I dim => (C a b*R a b)*T)
        (g:=fun b : I dim => T*(C a b*R a b))]
      exact Finset.sum_congr rfl (fun b _ => hTerm a b)
    rw [← hSum,← hDeg]
    abel
  rw [hEq,LinearMap.add_apply,map_add,LinearMap.add_apply,map_add,
    ← smoothSupportedTraceFiberDerivative_apply hY F hF (axis i) hx u]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.sum_apply,map_sum,map_sub,
    Module.End.mul_apply,T,R,Q,C,L,c,smoothTraceAngularComm,smoothSupportedTraceBaseMul_fiber,
    smoothSupportedTraceFiberAction_fiber,LinearMap.smul_apply,smul_sub]

end CalderonN
