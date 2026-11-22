module

public import Proof.CalderonN.NativeCoefficientBallForcing
public import Proof.CalderonN.FixedBallFluxUnique
public import Proof.CalderonN.SharpBallCoefficientOperator
public import Proof.CalderonN.CutoffCoefficientJets

import Proof.CalderonN.MatrixFieldJetNorms
import Mathlib.Tactic

/-! The native strong operator estimates apply to a smooth coefficient
specified on the ball via a compact extension. -/

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim]

theorem smoothBallSobolev_eq_of_eqOn_ball (k : ℕ) (u v : SmoothData dim)
    (h : EqOn u.1 v.1 (ball (0 : X dim) 1)) : smoothBallSobolev k u = smoothBallSobolev k v := by
  apply Wkp.ext k
  apply Lp.ext
  filter_upwards [value_smoothBallSobolev_ae k u,value_smoothBallSobolev_ae k v,
    ae_restrict_mem (μ := (volume : Measure (X dim))) (fixedBallOpens dim).isOpen.measurableSet]
    with z hu hv hz
  exact hu.trans ((h hz).trans hv.symm)

theorem negativeBallDivergence_sub_solution {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (u v : SmoothData dim) (z : X dim) :
    negativeBallDivergence a (u.1-v.1) z =
      negativeBallDivergence a u.1 z-negativeBallDivergence a v.1 z := by
  have hEq : u.1 = (u.1-v.1)+v.1 := by abel
  have h := negativeBallDivergence_add ha (u.2.sub v.2) v.2 z
  change negativeBallDivergence a ((u.1-v.1)+v.1) z =
    negativeBallDivergence a (u.1-v.1) z+negativeBallDivergence a v.1 z at h
  rw [← hEq] at h
  linarith only [h]

theorem negativeBallDivergence_const_smul_solution {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (u : SmoothData dim) (r : ℝ) (z : X dim) :
    negativeBallDivergence a (r • u.1) z = r*negativeBallDivergence a u.1 z := by
  have hD (x : X dim) : fderiv ℝ (r • u.1) x = r • fderiv ℝ u.1 x :=
    fderiv_const_smul (u.2.differentiable (by simp) x) r
  have hProd (i : Fin dim) : (fun x => ∑ j, a x i j * coordDeriv j (r • u.1) x) =
      r • (fun x => ∑ j, a x i j * coordDeriv j u.1 x) := by
    funext x
    simp only [coordDeriv,hD,Pi.smul_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change -(∑ i, coordDeriv i (fun x => ∑ j, a x i j * coordDeriv j (r • u.1) x) z) =
    r*(-∑ i, coordDeriv i (fun x => ∑ j, a x i j * coordDeriv j u.1 x) z)
  simp_rw [hProd]
  rw [mul_neg,Finset.mul_sum,neg_inj]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordDeriv,fderiv_const_smul_field]
  rfl

theorem negativeBallDivergence_add_coefficient {a b : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (u : SmoothData dim) (z : X dim) :
    negativeBallDivergence (a+b) u.1 z =
      negativeBallDivergence a u.1 z+negativeBallDivergence b u.1 z := by
  have h (i : Fin dim) : (fun x => ∑ j, (a x+b x) i j * coordDeriv j u.1 x) =
      (fun x => ∑ j, a x i j * coordDeriv j u.1 x)+(fun x => ∑ j, b x i j * coordDeriv j u.1 x) := by
    funext x
    simp only [Matrix.add_apply,add_mul,Finset.sum_add_distrib,Pi.add_apply]
  change -(∑ i, coordDeriv i (fun x => ∑ j, (a+b) x i j * coordDeriv j u.1 x) z) =
    -(∑ i, coordDeriv i (fun x => ∑ j, a x i j * coordDeriv j u.1 x) z) +
    -(∑ i, coordDeriv i (fun x => ∑ j, b x i j * coordDeriv j u.1 x) z)
  rw [← neg_add,← Finset.sum_add_distrib]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i _
  change coordDeriv i (fun x => ∑ j, (a x+b x) i j * coordDeriv j u.1 x) z = _
  rw [h i]
  have hSmooth (A : X dim → Mat dim) (hA : ContDiff ℝ ∞ A) :
      ContDiff ℝ ∞ (fun x => ∑ j, A x i j * fderiv ℝ u.1 x (axis j)) :=
    ContDiff.sum fun j _ => (contDiff_pi.mp (contDiff_pi.mp hA i) j).mul
      ((u.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  simp only [coordDeriv,fderiv_add ((hSmooth a ha).differentiable (by simp) z)
    ((hSmooth b hb).differentiable (by simp) z),add_apply]

theorem negativeBallDivergence_sub_coefficient {a b : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (u : SmoothData dim) (z : X dim) :
    negativeBallDivergence (a-b) u.1 z =
      negativeBallDivergence a u.1 z-negativeBallDivergence b u.1 z := by
  have hEq : a = (a-b)+b := by abel
  have h := negativeBallDivergence_add_coefficient (ha.sub hb) hb u z
  change negativeBallDivergence ((a-b)+b) u.1 z =
    negativeBallDivergence (a-b) u.1 z+negativeBallDivergence b u.1 z at h
  rw [← hEq] at h
  linarith only [h]

theorem negativeBallDivergence_const_smul_coefficient (a : X dim → Mat dim)
    (u : X dim → ℝ) (r : ℝ) (z : X dim) :
    negativeBallDivergence (r • a) u z = r*negativeBallDivergence a u z := by
  have h (i : Fin dim) : (fun x => ∑ j, (r • a) x i j * coordDeriv j u x) =
      r • (fun x => ∑ j, a x i j * coordDeriv j u x) := by
    funext x
    simp only [Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum]
  change -(∑ i, coordDeriv i (fun x => ∑ j, (r • a) x i j * coordDeriv j u x) z) =
    r*(-∑ i, coordDeriv i (fun x => ∑ j, a x i j * coordDeriv j u x) z)
  rw [mul_neg,Finset.mul_sum,neg_inj]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]
  simp only [coordDeriv,fderiv_const_smul_field]
  rfl

variable [Nontrivial (Fin dim)]

/-- A smooth coefficient admits a compact lift agreeing on a neighborhood of the closed unit ball. -/
theorem exists_smoothCoefficientMatrix_eqOn {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) :
    ∃ F : SmoothCoefficientMatrix dim 2,
      EqOn (coefficientMatrixField 2 F) a (ball (0 : X dim) (5/4)) := by
  let χ := unitBallSmoothCutoff dim
  let v (k l : Fin dim) (x : X dim) := χ x * a x k l
  have hV (k l : Fin dim) : ContDiff ℝ ∞ (v k l) :=
    χ.contDiff.mul (contDiff_pi.mp (contDiff_pi.mp ha k) l)
  let F : SmoothCoefficientMatrix dim 2 := fun k l =>
    compactCoefficient 2 (v k l) (hV k l) χ.hasCompactSupport.mul_right
  refine ⟨F,?_⟩
  intro z hz
  ext k l
  rw [show coefficientMatrixField 2 F z k l = v k l z from
    congrFun (coefficientValue_compactCoefficient 2 (v k l) _ _) z]
  change χ z*a z k l = a z k l
  have hz2 : z ∈ closedBall (0 : X dim) χ.rIn :=
    closedBall_subset_closedBall (show (5/4 : ℝ) ≤ 2 by norm_num) (ball_subset_closedBall hz)
  rw [χ.one_of_mem_closedBall hz2,one_mul]

/-- Control the strong forcing on the actual unit ball by the local C1
coefficient bound and the H2 norm of the smooth solution. -/
theorem norm_smoothBallSobolev_negativeDivergence_le {a : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (u : SmoothData dim) (q : ℝ) (hq : 0 ≤ q)
    (hBounds : ∀ z ∈ ball (0 : X dim) 1, ‖a z‖ ≤ q ∧ ‖fderiv ℝ a z‖ ≤ q) :
    ‖smoothBallSobolev 0 ⟨negativeBallDivergence a u.1,contDiff_negativeBallDivergence ha u.2⟩‖ ≤
      fullC1OperatorBudget (dim := dim)*q*‖smoothBallSobolev 2 u‖ := by
  obtain ⟨F,hF⟩ := exists_smoothCoefficientMatrix_eqOn ha
  let A := coefficientMatrixField 2 F
  have hV (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] a := by
    filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 5/4) hz)]
      with w hw using hF hw
  obtain ⟨hs,hExact⟩ := fullBallDivergence_native_smooth 0 F u
  rw [← smoothBallSobolev_eq_of_eqOn_ball 0 ⟨negativeBallDivergence A u.1,hs⟩
    ⟨negativeBallDivergence a u.1,contDiff_negativeBallDivergence ha u.2⟩ (fun z hz =>
      negativeBallDivergence_congr_germ (hV z hz) EventuallyEq.rfl),← hExact]
  apply ((fullBallDivergenceL 0 F).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply norm_fullCoefficientOperator_zero_le F q hq
  · intro k l z hz
    change |A z k l| ≤ _
    rw [show A z = a z from (hV z hz).eq_of_nhds,← Real.norm_eq_abs]
    exact (Matrix.norm_entry_le_entrywise_sup_norm (a z)).trans (hBounds z hz).1
  · intro k l z hz
    change ‖fderiv ℝ (fun x => A x k l) z‖ ≤ _
    have he : (fun x => A x k l) =ᶠ[𝓝 z] fun x => a x k l := (hV z hz).fun_comp (matrixEntryL k l)
    rw [he.fderiv_eq,fderiv_matrix_entry _ _ (ha.differentiable (by simp) z)]
    have hEntry : ‖matrixEntryL k l‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro M
      simpa only [matrixEntryL_apply,one_mul] using
        Matrix.norm_entry_le_entrywise_sup_norm M (i := k) (j := l)
    exact ((matrixEntryL k l).opNorm_comp_le _).trans
      ((mul_le_mul hEntry (hBounds z hz).2 (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

/-- Any smooth zero-trace solution has the norm bound of the actual
strong inverse for its coefficient. -/
theorem norm_smooth_zeroDirichlet_le_of_forcing
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (coefficientMatrixField 2 F) lo hi)
    (u g : SmoothData dim) (hT : EqOn u.1 0 (standardSphere dim))
    (hEq : EqOn (negativeBallDivergence (coefficientMatrixField 2 F) u.1) g.1 (ball (0 : X dim) 1)) :
    ‖smoothBallSobolev 2 u‖ ≤ ‖(strongDirichletOperator fixedSobolevCalculus 0 F).inverse‖*
      ‖smoothBallSobolev 0 g‖ := by
  let A := coefficientMatrixField 2 F
  let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
  let Inv := (strongDirichletOperator fixedSobolevCalculus 0 F).inverse
  obtain ⟨v,hvT,hvEq,hvNorm⟩ := exists_native_classical_zeroDirichlet F hEll g
  let w : SmoothData dim := ⟨u.1-v.1,u.2.sub v.2⟩
  have ha : ContDiff ℝ ∞ A := contDiff_coefficientMatrixField 2 F
  have hwEq : EqOn (negativeBallDivergence A w.1) 0 (ball (0 : X dim) 1) := by
    intro z hz
    change negativeBallDivergence A (u.1-v.1) z = 0
    rw [negativeBallDivergence_sub_solution ha u v,hEq hz,hvEq hz,sub_self]
  have hwT : EqOn w.1 0 (standardSphere dim) := by
    intro z hz
    change u.1 z-v.1 z = 0
    exact sub_eq_zero.mpr ((hT hz).trans (hvT hz).symm)
  have hZ := eqOn_closedUnitBall_of_negativeBallDivergence_eq_zero ha hEll w hwEq hwT
  have hUV : EqOn u.1 v.1 (ball (0 : X dim) 1) :=
    fun z hz => sub_eq_zero.mp (hZ (ball_subset_closedBall hz))
  rw [smoothBallSobolev_eq_of_eqOn_ball 2 u v hUV,hvNorm]
  change ‖j (Inv (smoothBallSobolev 0 g))‖ ≤ _
  change ‖Inv (smoothBallSobolev 0 g)‖ ≤ _
  exact Inv.le_opNorm _


end CalderonN
