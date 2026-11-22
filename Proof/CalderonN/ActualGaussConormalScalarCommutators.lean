module

public import Proof.CalderonN.ActualGaussConormalRotatedMultiplier
public import Proof.CalderonN.ActualGaussConormalBounds
public import Proof.CalderonN.SmoothMultiplierJetFromLocal
public import Proof.CalderonN.SmoothTraceMultiplierCommLift

import Mathlib.Tactic

/-! Scalar multiplication commutators of the actual conormal remainder
at all four half-integer levels. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actualGauss_scaledConormal_scalar_commutators (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ D : ActualGaussFiberData d y,
        ∀ (b : SmoothData dim) (J : ℝ), 0 ≤ J →
        (∀ z ∈ closedBall (0:X dim) 1,LocalSmoothJetBudget b.1 z 3 J) →
        let R := ((d.radius y)^2)⁻¹ • D.conormalRemainder
        let B := smoothSphereTraceMul b
        SmoothTraceAngularBound hn 0 (C*J) (R*B-B*R) := by
  obtain ⟨η₀,C₀,hη₀,hC₀,hHalf⟩ := uniform_actualGauss_scaledConormal_multiplier_bounds (Y:=Y)
    hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,C₁,hη₁,hC₁,hRot⟩ := uniform_actualGauss_scaledConormal_rotation_multiplier_bound (Y:=Y)
    hn hΩ (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨η₂,_,hη₂,_,hAdj⟩ := uniform_actualGauss_conormal_angularBounds (Y:=Y)
    hn hY hΩ hm K ρ c₀ M Cj hK hρ
  let C := 2*C₀+smoothTraceRotationLiftConstant dim (2*C₀) (2*C₁+16*C₀)
  have hLift : 0 ≤ smoothTraceRotationLiftConstant dim (2*C₀) (2*C₁+16*C₀) := Real.sqrt_nonneg _
  have hC : 0 ≤ C := add_nonneg (by positivity) hLift
  refine ⟨min (min η₀ η₁) η₂,C,lt_min (lt_min hη₀ hη₁) hη₂,hC,?_⟩
  intro floor hf ε he hs d hd y hy D b J hJ hJets
  dsimp only
  let R := ((d.radius y)^2)⁻¹ • D.conormalRemainder
  let B := smoothSphereTraceMul b
  let Q := R*B-B*R
  let H := 2*C₀*J
  let I₀ := 2*C₁*J
  let I₁ := 16*C₀*J
  let G := smoothTraceRotationLiftConstant dim H (I₀+I₁)
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hR := (hAdj floor hf ε he (hs.trans (min_le_right _ _)) d hd y hy D).1
  have hB := smoothMultiplierJetBound_of_local b J hJ (fun z hz =>
    ⟨(hJets z hz).smooth,fun n hn => (hJets z hz).bound n (by omega)⟩)
  have hA u := hHalf floor hf ε he (hs.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy D
    b (2*J) (by positivity) hB u
  have hHp (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) (Q u)‖ ≤
      H*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ :=
    (hA u).1.trans_eq (by dsimp [H]; ring)
  have hHn (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) (Q u)‖ ≤
      H*‖smoothSphereTraceSobolev hn (-(1/2):ℝ) (by norm_num) u‖ :=
    (hA u).2.trans_eq (by dsimp [H]; ring)
  have hFirst (i j : I dim) (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num)
        ((smoothTraceAngularComm i j R*B-B*smoothTraceAngularComm i j R) u)‖ ≤
        I₀*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ :=
    (hRot floor hf ε he (hs.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy D
      b (2*J) (by positivity) hB i j u).trans_eq (by dsimp [I₀]; ring)
  have hSecond (i j : I dim) (u : SmoothSphereTrace dim) :
      let b' := smoothRotationData i j b
      let B' := smoothSphereTraceMul b'
      ‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) ((R*B'-B'*R) u)‖ ≤
        I₁*‖smoothSphereTraceSobolev hn (1/2:ℝ) (by norm_num) u‖ := by
    dsimp only
    let b' := smoothRotationData i j b
    have hRot' (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
        LocalSmoothJetBudget b'.1 z 2 (8*J) := by
      have h := localSmoothJetBudget_sphereRotation i j (mem_closedBall_zero_iff.mp hz) (N:=2) (hJets z hz)
      exact h.enlarge (by norm_num)
    have hb' := smoothMultiplierJetBound_of_local b' (8*J) (by positivity) hRot'
    exact (hHalf floor hf ε he (hs.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy D
      b' (2*(8*J)) (by positivity) hb' u).1.trans_eq (by dsimp [I₁]; ring)
  have hHigh := norm_smoothTraceMultiplierComm_threeHalf_of_rotated_half hn R b H I₀ I₁
    (by dsimp [H]; positivity) (by dsimp [I₀]; positivity) (by dsimp [I₁]; positivity) hHp hFirst hSecond
  have hLow := norm_smoothTraceMultiplierComm_negThreeHalf_of_threeHalf hn R hR b G hG hHigh
  have hH_le : H ≤ C*J := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hLift) hJ
  have hG_le : G ≤ C*J := by
    have h : G = smoothTraceRotationLiftConstant dim (2*C₀) (2*C₁+16*C₀)*J := by
      dsimp only [G,H,I₀,I₁,smoothTraceRotationLiftConstant]
      rw [show 2*(2*C₀*J)^2+(dim:ℝ)^2*(2*C₁*J+16*C₀*J+2*C₀*J*(2*(dim:ℝ)))^2 =
        (2*(2*C₀)^2+(dim:ℝ)^2*(2*C₁+16*C₀+(2*C₀)*(2*(dim:ℝ)))^2)*J^2 by ring,
        Real.sqrt_mul (by positivity),Real.sqrt_sq hJ]
    rw [h]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hJ
  intro i j hij u
  have hji : j = i := Fin.ext (by simpa using hij)
  subst j
  change traceOrderNorm hn i (Q u) ≤ C*J*traceOrderNorm hn i u
  fin_cases i
  · change traceOrderNorm hn 0 (Q u) ≤ C*J*traceOrderNorm hn 0 u
    unfold traceOrderNorm
    have h0 : traceOrderExponent (0 : Fin 4) = -(3/2:ℝ) := by
      norm_num [traceOrderExponent,Fin.reduceFinMk]
    rw [smoothSphereTraceSobolev_order_eq hn h0 _ (by norm_num),
      smoothSphereTraceSobolev_order_eq hn h0 _ (by norm_num)]
    exact (hLow u).trans (mul_le_mul_of_nonneg_right hG_le (norm_nonneg _))
  · change traceOrderNorm hn 1 (Q u) ≤ C*J*traceOrderNorm hn 1 u
    rw [traceOrderNorm_negHalf_eq,traceOrderNorm_negHalf_eq]
    exact (hHn u).trans (mul_le_mul_of_nonneg_right hH_le (norm_nonneg _))
  · change traceOrderNorm hn 2 (Q u) ≤ C*J*traceOrderNorm hn 2 u
    rw [traceOrderNorm_half_eq,traceOrderNorm_half_eq]
    exact (hHp u).trans (mul_le_mul_of_nonneg_right hH_le (norm_nonneg _))
  · change traceOrderNorm hn 3 (Q u) ≤ C*J*traceOrderNorm hn 3 u
    rw [traceOrderNorm_threeHalf_eq,traceOrderNorm_threeHalf_eq]
    exact (hHigh u).trans (mul_le_mul_of_nonneg_right hG_le (norm_nonneg _))

end CalderonN
