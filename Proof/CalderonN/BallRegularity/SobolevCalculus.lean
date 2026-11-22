module

public import Proof.CalderonN.WkpCalculus
public import Proof.CalderonN.BallRegularity.FixedRegularity
public import Proof.CalderonN.BallRegularity.FixedCalculus
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! From Proof/Archive/CollaboratorWkpCalculusOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Gradient
namespace CalderonN.BallSobolevCalculus

variable {dim : ℕ} [NeZero dim]

open TauCeti CalderonN.WkpCalculus

variable {Ω : Opens (X dim)}


theorem d_add (i : Fin dim) (k : ℕ) (u v : Wkp (volume : Measure (X dim)) Ω 2 (k + 1)) :
    d i k (u + v) = d i k u + d i k v := by
  apply Wkp.ext k
  rw [Wkp.value_add]
  apply Lp.ext
  have hg : W1p.gradient (Wkp.firstOrder k (u + v)) =
      W1p.gradient (Wkp.firstOrder k u) + W1p.gradient (Wkp.firstOrder k v) := by
    simp only [← Wkp.firstOrderL_apply, ← W1p.gradientL_apply, map_add]
  filter_upwards [value_d i k (u + v), value_d i k u, value_d i k v,
    Lp.coeFn_add (Wkp.value k (d i k u)) (Wkp.value k (d i k v)),
    Lp.coeFn_add (W1p.gradient (Wkp.firstOrder k u)) (W1p.gradient (Wkp.firstOrder k v))]
    with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, hg, h5, Pi.add_apply]
  rfl

theorem d_smul (i : Fin dim) (k : ℕ) (c : ℝ) (u : Wkp (volume : Measure (X dim)) Ω 2 (k + 1)) :
    d i k (c • u) = c • d i k u := by
  apply Wkp.ext k
  rw [Wkp.value_smul]
  apply Lp.ext
  have hg : W1p.gradient (Wkp.firstOrder k (c • u)) = c • W1p.gradient (Wkp.firstOrder k u) := by
    simp only [← Wkp.firstOrderL_apply, ← W1p.gradientL_apply, map_smul]
  filter_upwards [value_d i k (c • u), value_d i k u,
    Lp.coeFn_smul c (Wkp.value k (d i k u)),
    Lp.coeFn_smul c (W1p.gradient (Wkp.firstOrder k u))] with x h1 h2 h4 h5
  rw [h1, h4, Pi.smul_apply, h2, hg, h5, Pi.smul_apply]
  rfl

theorem continuous_d (i : Fin dim) : ∀ k : ℕ,
    Continuous (d (Ω := Ω) i k)
  | 0 => ((ContinuousLinearMap.compLpL 2 _ (EuclideanSpace.proj i : (X dim) →L[ℝ] ℝ)).continuous.comp
      (Wkp.iteratedGradientL 0).continuous)
  | k + 1 => by
      rw [Wkp.continuous_iff_lowerOrder_iteratedGradient]
      constructor
      · simp only [lowerOrder_d]
        exact (continuous_d i k).comp (Wkp.lowerOrderL (k + 1)).continuous
      · simp only [iteratedGradient_d]
        exact (ContinuousLinearMap.compLpL 2 _ (contr i k)).continuous.comp
          (Wkp.iteratedGradientL (k + 1)).continuous


def dL (i : Fin dim) (k : ℕ) :
    Wkp (volume : Measure (X dim)) Ω 2 (k + 1) →L[ℝ] Wkp (volume : Measure (X dim)) Ω 2 k where
  toFun := d i k
  map_add' := d_add i k
  map_smul' := d_smul i k
  cont := continuous_d i k

theorem dL_apply (i : Fin dim) (k : ℕ) (u : Wkp (volume : Measure (X dim)) Ω 2 (k + 1)) :
    dL i k u = d i k u := rfl

theorem norm_lift_le (i : Fin dim) : ∀ j : ℕ, ‖lift i j‖ ≤ 1
  | 0 => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun (s : (X dim)) => by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun (v : (X dim)) => ?_
      change ‖(inner ℝ s v) • e i‖ ≤ ‖s‖ * ‖v‖
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      exact abs_real_inner_le_norm s v
  | j + 1 => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => by
      change ‖(lift i j).comp T‖ ≤ 1 * ‖T‖
      have := norm_lift_le i j
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right this (norm_nonneg _))


theorem norm_ofPartials_le : ∀ (k : ℕ) (w : W1p (volume : Measure (X dim)) Ω 2)
    (g : Fin dim → Wkp (volume : Measure (X dim)) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure (X dim)).restrict Ω]
      fun x => W1p.gradient w x i),
    ‖ofPartials k w g h‖ ≤ ‖w‖ + k * ∑ i, ‖g i‖
  | 0, w, g, h => by simp only [CharP.cast_eq_zero, zero_mul, add_zero]; exact le_rfl
  | k + 1, w, g, h => by
      have hU' := norm_ofPartials_le k w (fun i => Wkp.lowerOrder k (g i)) h
      set U' := ofPartials k w (fun i => Wkp.lowerOrder k (g i)) h
      set F := ∑ i : Fin dim, (lift i k).compLp (Wkp.iteratedGradient k (g i))
      have hF : ‖F‖ ≤ ∑ i, ‖g i‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        refine (ContinuousLinearMap.norm_compLp_le _ _).trans ?_
        calc ‖lift i k‖ * ‖Wkp.iteratedGradient k (g i)‖ ≤ 1 * ‖g i‖ :=
              mul_le_mul (norm_lift_le i k) (Wkp.norm_iteratedGradient_le k (g i))
                (norm_nonneg _) zero_le_one
          _ = ‖g i‖ := one_mul _
      have hlow : ∑ i, ‖Wkp.lowerOrder k (g i)‖ ≤ ∑ i, ‖g i‖ :=
        Finset.sum_le_sum fun i _ => Wkp.norm_lowerOrder_le k (g i)
      have hsq := Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq (k + 1)
        (ofPartials (k + 1) w g h)
      have hlo : Wkp.lowerOrder (k + 1) (ofPartials (k + 1) w g h) = U' := by
        rw [ofPartials, ofPartialsPack]
        unfold ofPartialsStep
        simp only [Wkp.lowerOrder_mk, U', ofPartials]
      have hig : Wkp.iteratedGradient (k + 1) (ofPartials (k + 1) w g h) = F := by
        rw [ofPartials, ofPartialsPack]
        unfold ofPartialsStep
        simp only [Wkp.iteratedGradient_mk, F]
      rw [hlo, hig] at hsq
      have hsum : 0 ≤ ∑ i, ‖g i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
      have hb : ‖ofPartials (k + 1) w g h‖ ≤ ‖U'‖ + ‖F‖ := by
        nlinarith [norm_nonneg (ofPartials (k + 1) w g h), norm_nonneg U', norm_nonneg F]
      push_cast
      nlinarith [norm_nonneg w, Nat.cast_nonneg (α := ℝ) k]

end CalderonN.BallSobolevCalculus
