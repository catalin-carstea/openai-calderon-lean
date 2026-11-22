module

public import Proof.CalderonN.SmoothStrongBallEstimates

import Proof.CalderonN.GreenSourceCutoff
import Mathlib.Tactic

/-! Moving a smooth multiplier inside the Dirichlet solution creates
a first-order bulk source. Its bound uses only the native H¹ input norm. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem norm_multiplier_forcing_le {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (m u : SmoothData dim) (C J : ℝ) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hEntry : ∀ z ∈ ball (0 : X dim) 1, ∀ i j,
      |A z i j| ≤ C ∧ ‖fderiv ℝ (fun x => A x i j) z‖ ≤ C)
    (hM : ∀ z ∈ ball (0 : X dim) 1, ‖fderiv ℝ m.1 z‖ ≤ J ∧
      ∀ i, ‖fderiv ℝ (coordDeriv i m.1) z‖ ≤ J) :
    ∃ F : SmoothData dim, F.1 = greenSourceCutoffError A m.1 u.1 ∧
      ‖smoothBallSobolev 0 F‖ ≤ (4*(dim:ℝ)^2*C*J)*‖smoothSobolev u‖ := by
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let L := 2*(dim:ℝ)^2*C*J
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hSmooth (i j : I dim) : ContDiff ℝ ∞ (fun z => A z i j) :=
    contDiff_pi.mp (contDiff_pi.mp hA i) j
  have hmSmooth (i : I dim) : ContDiff ℝ ∞ (coordDeriv i m.1) :=
    (smoothDataCoordDeriv i m).2
  have huSmooth (i : I dim) : ContDiff ℝ ∞ (coordDeriv i u.1) :=
    (smoothDataCoordDeriv i u).2
  let F : SmoothData dim := ⟨greenSourceCutoffError A m.1 u.1,
    (u.2.mul (contDiff_negativeBallDivergence hA m.2)).sub
      (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
        ((hSmooth i j).mul (hmSmooth i)).mul (huSmooth j)))⟩
  refine ⟨F,rfl,?_⟩
  have hAxis (i : Fin dim) : ‖axis i‖ = 1 := by simp [axis]
  have hApply (z : X dim) (i : Fin dim) (f : X dim → ℝ) :
      |coordDeriv i f z| ≤ ‖fderiv ℝ f z‖ := by
    rw [coordDeriv,← Real.norm_eq_abs,← mul_one ‖fderiv ℝ f z‖,← hAxis i]
    exact (fderiv ℝ f z).le_opNorm (axis i)
  have hDiv (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      |negativeBallDivergence A m.1 z| ≤ L := by
    have hEach (i j : I dim) :
        |coordDeriv i (fun x => A x i j * coordDeriv j m.1 x) z| ≤ 2*C*J := by
      have h (F G : X dim → ℝ) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
          coordDeriv i (fun z => F z*G z) z =
            F z*coordDeriv i G z+G z*coordDeriv i F z := by
        unfold coordDeriv
        rw [fderiv_fun_mul (hF.differentiable (by simp) z) (hG.differentiable (by simp) z)]
        rfl
      rw [h _ _ (hSmooth i j) (hmSmooth j)]
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul]
      have h₁ := mul_le_mul (hEntry z hz i j).1
        ((hApply z i (coordDeriv j m.1)).trans ((hM z hz).2 j)) (abs_nonneg _) hC
      have h₂ := mul_le_mul ((hApply z j m.1).trans (hM z hz).1)
        ((hApply z i (fun x => A x i j)).trans (hEntry z hz i j).2) (abs_nonneg _) hJ
      exact (add_le_add h₁ h₂).trans_eq (by ring)
    unfold negativeBallDivergence Elliptic.Lop
    rw [abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ i : Fin dim,∑ j : Fin dim, 2*C*J := by
        apply Finset.sum_le_sum
        intro i _
        have hSum : Elliptic.pd i (fun x => ∑ j, A x i j*Elliptic.pd j m.1 x) z =
            ∑ j, coordDeriv i (fun x => A x i j*coordDeriv j m.1 x) z := by
          change fderiv ℝ (fun x => ∑ j, A x i j*coordDeriv j m.1 x) z (axis i) = _
          rw [fderiv_fun_sum (fun j _ =>
            ((hSmooth i j).mul (hmSmooth j)).differentiable (by simp) z),ContinuousLinearMap.sum_apply]
          rfl
        rw [hSum]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hEach i j)
      _ = L := by simp [L,Finset.sum_const,nsmul_eq_mul]; ring
  have hPoint (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      |F.1 z| ≤ L*(|u.1 z| +‖gradient u.1 z‖) := by
    have hd (j : I dim) : |coordDeriv j u.1 z| ≤ ‖gradient u.1 z‖ := by
      rw [gradient,LinearIsometryEquiv.norm_map]
      exact hApply z j u.1
    have hPart : |∑ i,∑ j, A z i j*coordDeriv i m.1 z*coordDeriv j u.1 z| ≤
        (dim:ℝ)^2*C*J*‖gradient u.1 z‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (?_ : _ ≤ _)
      calc
        _ ≤ ∑ i : Fin dim,∑ j : Fin dim, C*J*‖gradient u.1 z‖ := by
          apply Finset.sum_le_sum
          intro i _
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          simp only [abs_mul]
          exact mul_le_mul (mul_le_mul (hEntry z hz i j).1 ((hApply z i m.1).trans (hM z hz).1)
            (abs_nonneg _) hC) (hd j) (abs_nonneg _) (by positivity)
        _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]; ring
    change |u.1 z*negativeBallDivergence A m.1 z-
      2*(∑ i,∑ j, A z i j*coordDeriv i m.1 z*coordDeriv j u.1 z)| ≤ _
    refine (abs_sub _ _).trans ?_
    simp only [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    calc
      _ ≤ |u.1 z| * L+2*((dim:ℝ)^2*C*J*‖gradient u.1 z‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (hDiv z hz) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hPart (by norm_num))
      _ = _ := by dsimp [L]; ring
  let U := smoothSobolev u
  have hNormF : ‖smoothBallSobolev 0 F‖^2 = ∫ x in ball (0 : X dim) 1, F.1 x^2 := by
    change ‖Wkp.value 0 (smoothBallSobolev 0 F)‖^2 = _
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [value_smoothBallSobolev_ae 0 F] with x hx
    rw [hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hV : (∫ x in ball (0 : X dim) 1, u.1 x^2) = ‖W1p.value U‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [value_smoothSobolev_ae u] with x hx
    change u.1 x^2 = ⟪(W1p.value U) x,(W1p.value U) x⟫_ℝ
    rw [show (W1p.value U) x = u.1 x from hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hG : (∫ x in ball (0 : X dim) 1, ‖gradient u.1 x‖^2) = ‖W1p.gradient U‖^2 := by
    rw [← W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae u] with x hx
    rw [show (W1p.gradient U) x = gradient u.1 x from hx]
  have hInt {g : X dim → ℝ} (hg : Continuous g) : IntegrableOn g (ball (0 : X dim) 1) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall
  have hIu : IntegrableOn (fun x => u.1 x^2) (ball (0 : X dim) 1) :=
    hInt (u.2.continuous.pow 2)
  have hIg : IntegrableOn (fun x => ‖gradient u.1 x‖^2) (ball (0 : X dim) 1) :=
    hInt (((u.2.gradient_right (m:=∞) (by simp)).continuous.norm).pow 2)
  rw [show 4*(dim:ℝ)^2*C*J = 2*L by dsimp [L]; ring]
  change ‖smoothBallSobolev 0 F‖ ≤ (2*L)*‖U‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hNormF]
  calc
    _ ≤ ∫ x in ball (0 : X dim) 1, (2*L)^2*(u.1 x^2+‖gradient u.1 x‖^2) := by
      apply setIntegral_mono_on (hInt (F.2.continuous.pow 2))
        ((hIu.add hIg).const_mul _) measurableSet_ball
      intro z hz
      change F.1 z^2 ≤ (2*L)^2*(u.1 z^2+‖gradient u.1 z‖^2)
      have hS := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hPoint z hz)
      rw [sq_abs,mul_pow] at hS
      have hY : (|u.1 z| +‖gradient u.1 z‖)^2 ≤ 4*(u.1 z^2+‖gradient u.1 z‖^2) := by
        nlinarith [sq_abs (u.1 z),sq_nonneg (|u.1 z|-‖gradient u.1 z‖)]
      exact hS.trans ((mul_le_mul_of_nonneg_left hY (sq_nonneg L)).trans_eq (by ring))
    _ = _ := by
      rw [integral_const_mul,integral_add hIu hIg,hV,hG,← W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,mul_pow]
      ring

end CalderonN
