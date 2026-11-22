module

public import Proof.CalderonN.PrincipalMetric
public import Proof.CalderonN.DilationConnection
import Proof.CalderonN.ParameterJets
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem smallJet_eq_zero_on {V : Set (X dim)} (hV : IsOpen V) {γ g : MetricField dim}
    (hprincipal : EqOn (principal γ g) (fun y => (γ y)⁻¹) V) :
    EqOn (smallJet γ g) 0 V := by
  intro y hy
  have hjet (a : I dim → Fin 9) (i j : I dim) :
      chartPartial (fun t => (a t).val) (fun x => (principal γ g x - (γ x)⁻¹) i j) y = 0 := by
    apply chartPartial_eq_zero_of_eqOn_zero hV _ _ hy
    intro x hx
    simp [hprincipal hx]
  simp only [smallJet, hjet, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero,
    Real.sqrt_zero]
  rfl

private theorem contDiffOn_normalized_difference_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    {A B : E → (Mat dim)}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun q => A q i j) U)
    (hB : ∀ i j, ContDiffOn ℝ ∞ (fun q => B q i j) U)
    (hApos : ∀ q ∈ U, (A q).PosDef) (hBpos : ∀ q ∈ U, (B q).PosDef) (i j : (I dim)) :
    ContDiffOn ℝ ∞ (fun q =>
      (((dim : ℝ) / (A q * (B q)⁻¹).trace : ℝ) • (B q)⁻¹ - (A q)⁻¹) i j) U := by
  exact (contDiffOn_normalized_inv_entry_of_entries hA hB hApos hBpos i j).sub
    (contDiffOn_inv_entry_of_entries hA (fun q hq => (hApos q hq).det_pos.ne') i j)

/-- A single small dilation makes the entire normalized eight-jet small
on any fixed compact center region. The conformal factor is fixed before
the dilation. The equality at λ=0 is used only for this choice. -/
theorem eventually_smallJet_le_of_common_origin
    {Ω K : Set (X dim)} (hΩ : IsOpen Ω) (h₀ : (0 : (X dim)) ∈ Ω) (hK : IsCompact K)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hmatch : g₁ 0 = g₂ 0) {σ : (X dim) → ℝ} (hσ : ContDiff ℝ ∞ σ)
    (hσpos : ∀ y, 0 < σ y) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K,
      lam • y ∈ Ω ∧ smallJet (conformalReference σ g₁ lam) (dilatedMetric g₂ lam) y ≤ ε := by
  let U : Set (ℝ × (X dim)) := {q | q.1 • q.2 ∈ Ω}
  let A (q : ℝ × (X dim)) := conformalReference σ g₁ q.1 q.2
  let B (q : ℝ × (X dim)) := dilatedMetric g₂ q.1 q.2
  have hU : IsOpen U := hΩ.preimage (continuous_fst.smul continuous_snd)
  have hcomp (g : (MetricField dim)) (hg : SmoothMetric Ω g) (i j : (I dim)) :
      ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => g (q.1 • q.2) i j) U :=
    (hg.1 i j).comp (contDiff_fst.smul contDiff_snd).contDiffOn (fun _ hq => hq)
  have hA (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => A q i j) U :=
    (hσ.comp contDiff_snd).contDiffOn.mul (hcomp g₁ hg₁ i j)
  have hB (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => B q i j) U := hcomp g₂ hg₂ i j
  have hApos : ∀ q ∈ U, (A q).PosDef :=
    fun q hq => (hg₁.2 (q.1 • q.2) hq).smul (hσpos q.2)
  have hBpos : ∀ q ∈ U, (B q).PosDef := fun q hq => hg₂.2 (q.1 • q.2) hq
  let F (i j : (I dim)) (q : ℝ × (X dim)) := (((dim : ℝ) / (A q * (B q)⁻¹).trace : ℝ) • (B q)⁻¹ - (A q)⁻¹) i j
  have hF (i j : (I dim)) : ContDiffOn ℝ ∞ (F i j) U :=
    contDiffOn_normalized_difference_entry hA hB hApos hBpos i j
  let J := (Finset.univ : Finset (I dim → Fin 9)).filter (fun a => (∑ i, (a i).val) ≤ 8)
  let H (q : ℝ × X dim) := ∑ a ∈ J,
    Real.sqrt (∑ i, ∑ j, (baseChartPartial (fun t => (a t).val) (F i j) q)^2)
  have hH : ContinuousOn H U := by
    refine continuousOn_finsetSum _ fun a _ => ContinuousOn.sqrt ?_
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact (contDiffOn_baseChartPartial hU (hF i j) (fun t => (a t).val)).continuousOn.pow 2
  have hslice (q : ℝ × X dim) (hq : q ∈ U) :
      H q = smallJet (conformalReference σ g₁ q.1) (dilatedMetric g₂ q.1) q.2 := by
    rcases q with ⟨lam, y⟩
    dsimp only [H]
    simp_rw [fun (a : I dim → Fin 9) (i j : I dim) =>
      baseChartPartial_eq_slice hU (hF i j) hq (fun t => (a t).val)]
    rfl
  have hU₀ (y : (X dim)) : ((0 : ℝ), y) ∈ U := by
    change (0 : ℝ) • y ∈ Ω
    simpa using h₀
  have hzero : EqOn (smallJet (conformalReference σ g₁ 0) (dilatedMetric g₂ 0)) 0 univ := by
    apply smallJet_eq_zero_on isOpen_univ
    intro y _
    have hpos : (dilatedMetric g₂ 0 y).PosDef := hBpos (0, y) (hU₀ y)
    apply principal_eq_inv_of_pos_smul hpos (hσpos y)
    change σ y • g₁ ((0 : ℝ) • y) = σ y • g₂ ((0 : ℝ) • y)
    rw [zero_smul, hmatch]
  have hnear : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K, (lam, y) ∈ U ∧ H (lam, y) < ε := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have hu := hU.mem_nhds (hU₀ y)
    have hzero' : H (0, y) = 0 := (hslice (0, y) (hU₀ y)).trans (hzero (mem_univ y))
    have ha : H (0, y) < ε := by rwa [hzero']
    have hb := (hH.continuousAt hu).preimage_mem_nhds (Iio_mem_nhds ha)
    filter_upwards [hu, hb] with q hq hqε
    exact ⟨hq, hqε⟩
  filter_upwards [hnear] with lam hlam y hy
  obtain ⟨hu, hsmall⟩ := hlam y hy
  exact ⟨hu, ((hslice (lam, y) hu).symm.trans_lt hsmall).le⟩

/-- Undo the fixed positive spatial dilation in a metric equality on a ball. -/
theorem eqOn_ball_of_eqOn_dilated {g₁ g₂ : (MetricField dim)} {r lam : ℝ} (hlam : 0 < lam)
    (heq : EqOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) (Metric.ball (0 : (X dim)) r)) :
    EqOn g₁ g₂ (Metric.ball (0 : (X dim)) (lam * r)) := by
  intro x hx
  have hy : lam⁻¹ • x ∈ Metric.ball (0 : (X dim)) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam)]
    have hx' : ‖x‖ < lam * r := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact (inv_mul_lt_iff₀ hlam).mpr hx'
  have he := heq hy
  simpa only [dilatedMetric, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul] using he

end CalderonN
