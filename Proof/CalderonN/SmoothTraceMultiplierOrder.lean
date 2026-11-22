module

public import Proof.CalderonN.SmoothTraceAngularOrder

import Proof.CalderonN.SmoothBoundaryMultiplier
import Mathlib.Tactic

/-! Scalar multiplication and its rotation derivative on the same core
as the conormal operators. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace Gradient
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothSphereTraceMul_symmetric (hn : 3 ≤ dim) (m : SmoothData dim) :
    SmoothTraceAdjoint hn (smoothSphereTraceMul m) (smoothSphereTraceMul m) := by
  intro u v
  obtain ⟨x,rfl⟩ := smoothSphereTraceL_surjective u
  obtain ⟨y,rfl⟩ := smoothSphereTraceL_surjective v
  let U : SmoothData dim := ⟨x.1,smoothBallData_contDiff x⟩
  let V : SmoothData dim := ⟨y.1,smoothBallData_contDiff y⟩
  have hMul (f : SmoothData dim) : smoothSphereTraceMul m (smoothSphereTrace f) =
      smoothSphereTrace (smoothDataMul m f) := by
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    rfl
  change ⟪smoothSphereTraceL2 hn (smoothSphereTraceMul m (smoothSphereTrace U)),
    smoothSphereTraceL2 hn (smoothSphereTrace V)⟫_ℝ =
      ⟪smoothSphereTraceL2 hn (smoothSphereTrace U),smoothSphereTraceL2 hn
        (smoothSphereTraceMul m (smoothSphereTrace V))⟫_ℝ
  simp only [hMul,smoothSphereTraceL2_apply,smoothSphereLift_inner]
  apply integral_congr_ae
  filter_upwards with z
  change m.1 z*U.1 z*V.1 z = U.1 z*(m.1 z*V.1 z)
  ring

theorem smoothSphereTraceMul_rotation_comm (m : SmoothData dim) (i j : Fin dim) :
    let K := smoothSphereTraceRotation i j
    K*smoothSphereTraceMul m-smoothSphereTraceMul m*K =
      smoothSphereTraceMul ⟨sphereRotationDerivative i j m.1,contDiff_sphereRotationDerivative i j m.1 m.2⟩ := by
  dsimp only
  ext u : 1
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let F : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  have hMul : smoothSphereTraceMul m (smoothSphereTrace F) = smoothSphereTrace (smoothDataMul m F) := by
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    rfl
  apply Subtype.ext
  funext z
  change (smoothSphereTraceRotation i j (smoothSphereTraceMul m (smoothSphereTrace F))).1 z-
    (smoothSphereTraceMul m (smoothSphereTraceRotation i j (smoothSphereTrace F))).1 z = _
  rw [hMul,smoothSphereTraceRotation_apply,smoothSphereTraceMul_apply,smoothSphereTraceRotation_apply,
    smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply,smoothSphereTraceL_apply]
  change sphereRotationDerivative i j (fun w => m.1 w*F.1 w) z-
    m.1 z*sphereRotationDerivative i j F.1 z =
    sphereRotationDerivative i j m.1 z*F.1 z
  unfold sphereRotationDerivative
  rw [fderiv_fun_mul (m.2.differentiable (by simp) z) (F.2.differentiable (by simp) z)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem norm_smoothSphereTraceMul_half_le (hn : 3 ≤ dim) (m : SmoothData dim)
    {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |m.1 x| ≤ C)
    (hG : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient m.1 x‖ ≤ C)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (smoothSphereTraceMul m u)‖ ≤
      (2*Real.sqrt ((dim : ℝ)+3))*C*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let F : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  have hMul : smoothSphereTraceMul m (smoothSphereTrace F) = smoothSphereTrace (smoothDataMul m F) := by
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    rfl
  change ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (smoothSphereTraceMul m (smoothSphereTrace F))‖ ≤
    (2*Real.sqrt ((dim : ℝ)+3))*C*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (smoothSphereTrace F)‖
  rw [hMul,smoothSphereTraceSobolev_apply,smoothSphereTraceSobolev_apply]
  exact norm_smoothBoundarySobolev_mul_half_le hn m F hC hM hG

theorem smoothSphereTraceMul_angularBound (hn : 3 ≤ dim) (m : SmoothData dim)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |m.1 x| ≤ C)
    (hG : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient m.1 x‖ ≤ C)
    (hKM : ∀ (i j : Fin dim) x, x ∈ (fixedBallOpens dim : Set (X dim)) →
      |sphereRotationDerivative i j m.1 x| ≤ D)
    (hKG : ∀ (i j : Fin dim) x, x ∈ (fixedBallOpens dim : Set (X dim)) →
      ‖gradient (sphereRotationDerivative i j m.1) x‖ ≤ D) :
    let c := (2*Real.sqrt ((dim : ℝ)+3))*C
    let d := (2*Real.sqrt ((dim : ℝ)+3))*D
    SmoothTraceAngularBound hn 0 (max c (smoothTraceRotationLiftConstant dim c d)) (smoothSphereTraceMul m) := by
  dsimp only
  let c := (2*Real.sqrt ((dim : ℝ)+3))*C
  let d := (2*Real.sqrt ((dim : ℝ)+3))*D
  let c' := smoothTraceRotationLiftConstant dim c d
  let T := smoothSphereTraceMul m
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hc' : 0 ≤ c' := Real.sqrt_nonneg _
  have hAdj := smoothSphereTraceMul_symmetric hn m
  have hHalf (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (T u)‖ ≤
        c*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ :=
    norm_smoothSphereTraceMul_half_le hn m hC hM hG u
  have hK (i j : Fin dim) (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num)
        ((smoothSphereTraceRotation i j*T-T*smoothSphereTraceRotation i j) u)‖ ≤
      d*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
    let mθ : SmoothData dim := ⟨sphereRotationDerivative i j m.1,contDiff_sphereRotationDerivative i j m.1 m.2⟩
    have hEq : smoothSphereTraceRotation i j*T-T*smoothSphereTraceRotation i j = smoothSphereTraceMul mθ :=
      smoothSphereTraceMul_rotation_comm m i j
    have hMθ : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |mθ.1 x| ≤ D := hKM i j
    have hGθ : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient mθ.1 x‖ ≤ D := hKG i j
    rw [hEq]
    exact norm_smoothSphereTraceMul_half_le hn mθ hD hMθ hGθ u
  have hHigh (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) (T u)‖ ≤
        c'*‖smoothSphereTraceSobolev hn (3/2:ℝ) (by norm_num) u‖ := by
    have hh := norm_smoothSphereTrace_higher_of_rotation hn (1/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
      T c d hc hd (fun v => hHalf v) (fun i j v => hK i j v) u
    rw [smoothSphereTraceSobolev_order_eq hn (show (1/2:ℝ)+1=3/2 by norm_num) _ (by norm_num),
      smoothSphereTraceSobolev_order_eq hn (show (1/2:ℝ)+1=3/2 by norm_num) _ (by norm_num)] at hh
    exact hh
  have hLow := norm_smoothTrace_adjoint_of_bound hn (1/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) T T hAdj c hc hHalf
  have hVeryLow := norm_smoothTrace_adjoint_of_bound hn (3/2:ℝ) (3/2:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) T T hAdj c' hc' hHigh
  intro i j hij u
  have hj : j = i := Fin.ext (by simpa using hij)
  subst j
  change traceOrderNorm hn i (T u) ≤ max c c'*traceOrderNorm hn i u
  have hAt (i : Fin 4) (s : ℝ) (hs : s ≤ 2) (h : traceOrderExponent i = s)
      (w : SmoothSphereTrace dim) : traceOrderNorm hn i w = ‖smoothSphereTraceSobolev hn s hs w‖ :=
    congrArg norm (smoothSphereTraceSobolev_order_eq hn h _ hs w)
  fin_cases i
  · change traceOrderNorm hn (0:Fin 4) (T u) ≤ max c c'*traceOrderNorm hn (0:Fin 4) u
    simp_rw [hAt (0:Fin 4) (- (3/2):ℝ) (by norm_num) (by norm_num [traceOrderExponent])]
    exact (hVeryLow u).trans (mul_le_mul_of_nonneg_right (le_max_right c c') (norm_nonneg _))
  · change traceOrderNorm hn (1:Fin 4) (T u) ≤ max c c'*traceOrderNorm hn (1:Fin 4) u
    simp_rw [hAt (1:Fin 4) (-(1/2):ℝ) (by norm_num) (by norm_num [traceOrderExponent])]
    exact (hLow u).trans (mul_le_mul_of_nonneg_right (le_max_left c c') (norm_nonneg _))
  · change traceOrderNorm hn (2:Fin 4) (T u) ≤ max c c'*traceOrderNorm hn (2:Fin 4) u
    simp_rw [hAt (2:Fin 4) (1/2:ℝ) (by norm_num) (by norm_num [traceOrderExponent])]
    exact (hHalf u).trans (mul_le_mul_of_nonneg_right (le_max_left c c') (norm_nonneg _))
  · change traceOrderNorm hn (3:Fin 4) (T u) ≤ max c c'*traceOrderNorm hn (3:Fin 4) u
    simp_rw [hAt (3:Fin 4) (3/2:ℝ) (by norm_num) (by norm_num [traceOrderExponent])]
    exact (hHigh u).trans (mul_le_mul_of_nonneg_right (le_max_right c c') (norm_nonneg _))

end CalderonN
