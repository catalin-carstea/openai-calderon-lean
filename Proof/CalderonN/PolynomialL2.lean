module

public import Proof.CalderonN.Coercivity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Adapted from `Calderon/LocalPolynomialCoefficientL2Bound.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc in
the earlier anisotropic Calderón formalization. The Euclidean chart type
is shared with the current statement. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal

-- Current selected Section 06 finite-dimensional polynomial coefficient step.
namespace CalderonN

variable {dim : ℕ} [NeZero dim]
open Set Metric MeasureTheory

public theorem exists_polynomial_coefficient_le_unitBall_eLpNorm (m : ℕ) :
    let I := {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
    ∃ C : ℝ, 0 < C ∧ ∀ a : I → ℝ, ∀ alpha : I,
      |a alpha| ≤ C *
        (eLpNorm
          (fun z : (X dim) => ∑ beta : I,
            a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val)
          2 (volume.restrict (ball (0 : (X dim)) 1))).toReal := by
  classical
  let I := {alpha : Fin dim → Fin (m + 1) // ∑ i, (alpha i).val ≤ m}
  let μ : Measure (X dim) := volume.restrict (ball (0 : (X dim)) 1)
  let P : (I → ℝ) → (X dim) → ℝ := fun a z =>
    ∑ beta : I, a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val
  change ∃ C : ℝ, 0 < C ∧ ∀ a : I → ℝ, ∀ alpha : I,
    |a alpha| ≤ C * (eLpNorm (P a) 2 μ).toReal
  -- C1: the original Euclidean polynomial is continuous and bounded on the ball.
  have hCont (a : I → ℝ) : Continuous (P a) := by
    apply continuous_finsetSum
    intro beta _
    apply continuous_const.mul
    apply continuous_finsetProd
    intro i _
    exact (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ).continuous.pow _
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (measure_ball_ne_top (μ := (volume : Measure (X dim))))
  have hMem (a : I → ℝ) : MemLp (P a) 2 μ := by
    apply MemLp.of_bound (hCont a).aestronglyMeasurable (∑ beta : I, |a beta|)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
    have hProd (beta : I) : ‖∏ i : Fin dim, (z i) ^ (beta.val i).val‖ ≤ 1 := by
      rw [norm_prod]
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro i _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ((PiLp.norm_apply_le z i).trans hz1)
    calc
      ‖P a z‖ ≤ ∑ beta : I, ‖a beta * ∏ i : Fin dim, (z i) ^ (beta.val i).val‖ :=
        norm_sum_le _ _
      _ ≤ ∑ beta : I, |a beta| := by
        apply Finset.sum_le_sum
        intro beta _
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hProd beta)
  -- C2: the SAME L2 class map is linear, using the actual toLp laws.
  have hAdd (a b : I → ℝ) : P (a + b) = P a + P b := by
    funext z
    simp only [P, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hSmul (r : ℝ) (a : I → ℝ) : P (r • a) = r • P a := by
    funext z
    simp only [P, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  let T : (I → ℝ) →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun a => (hMem a).toLp (P a)
      map_add' := fun a b => by
        calc
          (hMem (a + b)).toLp (P (a + b)) =
              ((hMem a).add (hMem b)).toLp (P a + P b) :=
            MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (hAdd a b)))
          _ = (hMem a).toLp (P a) + (hMem b).toLp (P b) :=
            MemLp.toLp_add _ _
      map_smul' := fun r a => by
        calc
          (hMem (r • a)).toLp (P (r • a)) =
              ((hMem a).const_smul r).toLp (r • P a) :=
            MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (congrFun (hSmul r a)))
          _ = r • (hMem a).toLp (P a) := MemLp.toLp_const_smul r _ }
  -- C3-C6: an L2-zero polynomial vanishes pointwise, then all its coefficients vanish.
  have hZero (a : I → ℝ) (hTa : T a = 0) : a = 0 := by
    have hAE : P a =ᵐ[μ] (fun _ : (X dim) => (0 : ℝ)) := by
      have h := (hMem a).coeFn_toLp
      change (T a : (X dim) → ℝ) =ᵐ[μ] P a at h
      rw [hTa] at h
      exact h.symm.trans (Lp.coeFn_zero ℝ 2 μ)
    have hBall : EqOn (P a) (fun _ : (X dim) => (0 : ℝ)) (ball (0 : (X dim)) 1) :=
      Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (X dim))) hAE isOpen_ball
        (hCont a).continuousOn continuous_const.continuousOn
    let e : I → (Fin dim →₀ ℕ) := fun beta =>
      Finsupp.equivFunOnFinite.symm (fun i => (beta.val i).val)
    have he : Function.Injective e := by
      intro alpha beta h
      apply Subtype.ext
      funext i
      apply Fin.ext
      have hi := congrArg (fun d : Fin dim →₀ ℕ => d i) h
      simpa only [e, Finsupp.coe_equivFunOnFinite_symm] using hi
    let p : MvPolynomial (Fin dim) ℝ :=
      ∑ beta : I, MvPolynomial.monomial (e beta) (a beta)
    have hEval (u : Fin dim → ℝ) :
        MvPolynomial.eval u p = ∑ beta : I, a beta * ∏ i : Fin dim, (u i) ^ (beta.val i).val := by
      simp only [p, map_sum, MvPolynomial.eval_monomial]
      apply Finset.sum_congr rfl
      intro beta _
      congr 1
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      rfl
    have hp : p = 0 := by
      let t : ℝ := ((dim : ℝ) + 1)⁻¹
      have ht : 0 < t := by dsimp [t]; positivity
      apply MvPolynomial.funext_set (fun _ : Fin dim => Icc (-t) t)
        (fun _ => Set.Icc_infinite (by linarith))
      intro u hu
      let z : X dim := WithLp.toLp 2 u
      have hCoord (i : Fin dim) : (u i)^2 ≤ t^2 := by
        have hi := hu i (Set.mem_univ i)
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg (u i)) ht.le).mpr (abs_le.mpr hi)
      have hNorm : ‖z‖^2 ≤ (dim : ℝ) * t^2 := by
        calc
          ‖z‖^2 = ∑ i : Fin dim, (u i)^2 := EuclideanSpace.real_norm_sq_eq z
          _ ≤ ∑ _i : Fin dim, t^2 := Finset.sum_le_sum (fun i _ => hCoord i)
          _ = _ := by simp
      have hSmall : (dim : ℝ) * t^2 < 1 := by
        have heq : ((dim : ℝ)+1) * t = 1 := mul_inv_cancel₀ (by positivity)
        have hOne : t ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) dim])
        calc
          _ < ((dim : ℝ)+1) * t^2 :=
            mul_lt_mul_of_pos_right (lt_add_one _) (sq_pos_of_pos ht)
          _ = t := by rw [pow_two, ← mul_assoc,heq,one_mul]
          _ ≤ 1 := hOne
      have hz : z ∈ ball (0 : X dim) 1 := by
        apply mem_ball_zero_iff.mpr
        exact (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hNorm.trans_lt hSmall)
      rw [map_zero, hEval]
      exact hBall hz
    funext alpha
    have hCoeff := congrArg (fun q : MvPolynomial (Fin dim) ℝ => q.coeff (e alpha)) hp
    have hCoeff' : (∑ x : I, if x = alpha then a x else 0) = 0 := by
      simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, he.eq_iff] using hCoeff
    have hsum : (∑ x : I, if x = alpha then a x else 0) = a alpha := by
      classical
      exact Fintype.sum_ite_eq' alpha a
    rw [hsum] at hCoeff'
    exact hCoeff'
  -- C7-C8: finite dimensionality gives a positive bound in the existing norms.
  have hKer : LinearMap.ker T = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    change a = 0
    exact hZero a (LinearMap.mem_ker.mp ha)
  obtain ⟨K, hKpos, hK⟩ := T.exists_antilipschitzWith hKer
  refine ⟨(K : ℝ), hKpos, ?_⟩
  intro a alpha
  calc
    |a alpha| = ‖a alpha‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖a‖ := norm_le_pi_norm a alpha
    _ ≤ (K : ℝ) * ‖T a‖ := ZeroHomClass.bound_of_antilipschitz T hK a
    _ = (K : ℝ) * (eLpNorm (P a) 2 μ).toReal := by
      change (K : ℝ) * ‖(hMem a).toLp (P a)‖ = _
      rw [Lp.norm_toLp]

end CalderonN
