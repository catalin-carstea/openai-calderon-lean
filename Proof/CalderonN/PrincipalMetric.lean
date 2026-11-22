module

public import Proof.CalderonN.NormalizedMetric

import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]
theorem contDiffOn_normalized_inv_entry_of_entries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Set E}
    {γ g : E → (Mat dim)} (hγ : ∀ i j, ContDiffOn ℝ ∞ (fun y => γ y i j) Ω)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) Ω)
    (hγpos : ∀ y ∈ Ω, (γ y).PosDef) (hgpos : ∀ y ∈ Ω, (g y).PosDef) (i j : (I dim)) :
    ContDiffOn ℝ ∞ (fun y => (((dim : ℝ) / (γ y * (g y)⁻¹).trace : ℝ) • (g y)⁻¹) i j) Ω := by
  have hinv := contDiffOn_inv_entry_of_entries hg (fun x hx => (hgpos x hx).det_pos.ne')
  have htrace : ContDiffOn ℝ ∞ (fun y => (γ y * (g y)⁻¹).trace) Ω := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ => (hγ k l).mul (hinv l k)
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (contDiffOn_const.div htrace
    (fun y hy => (trace_mul_pos_of_posDef (hγpos y hy) (hgpos y hy).inv).ne')).mul (hinv i j)

theorem contDiffOn_principal_entry {Ω : Set (X dim)} {γ g : (MetricField dim)}
    (hγ : SmoothMetric Ω γ) (hg : SmoothMetric Ω g) (i j : (I dim)) :
    ContDiffOn ℝ ∞ (fun y => principal γ g y i j) Ω :=
  contDiffOn_normalized_inv_entry_of_entries hγ.1 hg.1 hγ.2 hg.2 i j


/-- The metric dual to the trace-normalized inverse metric. -/
@[expose] def principalMetric (γ g : (MetricField dim)) : (MetricField dim) :=
  fun y => (principal γ g y)⁻¹

@[expose] def principalMetricScale (γ g : (MetricField dim)) (y : (X dim)) : ℝ :=
  (γ y * (g y)⁻¹).trace / (dim : ℝ)

theorem principal_posDef {γ g : (MetricField dim)} {y : (X dim)}
    (hγ : (γ y).PosDef) (hg : (g y).PosDef) : (principal γ g y).PosDef :=
  hg.inv.smul (div_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dim)) (trace_mul_pos_of_posDef hγ hg.inv))

theorem principalMetricScale_pos {γ g : (MetricField dim)} {y : (X dim)}
    (hγ : (γ y).PosDef) (hg : (g y).PosDef) : 0 < principalMetricScale γ g y :=
  div_pos (trace_mul_pos_of_posDef hγ hg.inv) (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dim))

theorem principalMetric_eq_smul {γ g : (MetricField dim)} {y : (X dim)}
    (hγ : (γ y).PosDef) (hg : (g y).PosDef) :
    principalMetric γ g y = principalMetricScale γ g y • g y := by
  let c := (dim : ℝ) / (γ y * (g y)⁻¹).trace
  have hc : 0 < c := div_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne dim)) (trace_mul_pos_of_posDef hγ hg.inv)
  change (c • (g y)⁻¹)⁻¹ = ((γ y * (g y)⁻¹).trace / (dim : ℝ)) • g y
  have hInv : (c • (g y)⁻¹)⁻¹ = c⁻¹ • (g y)⁻¹⁻¹ :=
    Matrix.inv_smul' _ (Units.mk0 c hc.ne') (isUnit_iff_ne_zero.mpr hg.inv.det_pos.ne')
  rw [hInv,Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne')]
  simp only [c,inv_div]

theorem inverse_principalMetric {γ g : (MetricField dim)} {y : (X dim)}
    (hγ : (γ y).PosDef) (hg : (g y).PosDef) : (principalMetric γ g y)⁻¹ = principal γ g y :=
  Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (principal_posDef hγ hg).det_pos.ne')

theorem contDiffOn_principalMetricScale {Ω : Set (X dim)} {γ g : (MetricField dim)}
    (hγ : SmoothMetric Ω γ) (hg : SmoothMetric Ω g) :
    ContDiffOn ℝ ∞ (principalMetricScale γ g) Ω := by
  unfold principalMetricScale
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    (hγ.1 i j).mul (contDiffOn_metric_inv_entry hg j i)).div_const (dim : ℝ)

theorem smoothMetric_principalMetric {Ω : Set (X dim)} {γ g : (MetricField dim)}
    (hγ : SmoothMetric Ω γ) (hg : SmoothMetric Ω g) :
    SmoothMetric Ω (principalMetric γ g) := by
  refine ⟨fun i j => ?_,fun x hx => (principal_posDef (hγ.2 x hx) (hg.2 x hx)).inv⟩
  exact contDiffOn_inv_entry_of_entries (contDiffOn_principal_entry hγ hg)
    (fun x hx => (principal_posDef (hγ.2 x hx) (hg.2 x hx)).det_pos.ne') i j

theorem contDiff_principalMetric_family_entry {γ g : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j))
    (hpγ : ∀ a y, (γ a y).PosDef) (hpg : ∀ a y, (g a y).PosDef) (i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => principalMetric (γ q.1) (g q.1) q.2 i j) := by
  apply contDiffOn_univ.mp
  exact contDiffOn_inv_entry_of_entries
    (g := fun q : ℝ × (X dim) => principal (γ q.1) (g q.1) q.2)
    (contDiffOn_normalized_inv_entry_of_entries (fun i j => (hγ i j).contDiffOn)
      (fun i j => (hg i j).contDiffOn) (fun q _ => hpγ q.1 q.2) (fun q _ => hpg q.1 q.2))
    (fun q _ => (principal_posDef (hpγ q.1 q.2) (hpg q.1 q.2)).det_pos.ne') i j

end CalderonN
