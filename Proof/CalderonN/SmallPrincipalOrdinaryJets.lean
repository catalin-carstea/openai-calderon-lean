module

public import Proof.CalderonN.ChartSchwarzWords

import Proof.CalderonN.LocalMixedParameterJetCalculus
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.MetricSmooth
import Proof.CalderonN.ChartGeometry
import Mathlib.Tactic

/-! Convert the protected multi-index smallness assumption to ordinary
Fréchet jet bounds in the same chart, through order eight. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem count_chartWord_sum (W : List (I dim)) : (∑ i : I dim,W.count i) = W.length := by
  classical
  induction W with
  | nil => simp
  | cons j W ih =>
      simp only [List.count_cons,Finset.sum_add_distrib,beq_iff_eq,List.length_cons]
      rw [ih]
      have he : (∑ i : I dim,(if j=i then 1 else 0)) = 1 := by simp
      first | rw [he] | rw [show (∑ i : I dim,(if i=j then 1 else 0)) = 1 by simp]

omit [NeZero dim] in
private theorem chartDerivativeWord_eqOn {U : Set (X dim)} (hU : IsOpen U)
    {f F : X dim → ℝ} (h : EqOn f F U) (L : List (I dim)) :
    EqOn (chartDerivativeWord L f) (chartDerivativeWord L F) U := by
  induction L with
  | nil => exact h
  | cons j L ih => exact eqOn_coordDeriv hU ih j

theorem norm_iteratedFDeriv_principalDifference_le_smallJet
    {Y : Set (X dim)} (hY : IsOpen Y) {γ g : MetricField dim}
    (hγ : SmoothMetric Y γ) (hg : SmoothMetric Y g)
    {x : X dim} (hx : x ∈ Y) (n : ℕ) (hn : n ≤ 8) (i j : I dim) :
    ‖iteratedFDeriv ℝ n (fun y => (principal γ g y-(γ y)⁻¹) i j) x‖ ≤
      (dim:ℝ)^n*smallJet γ g x := by
  let f (y : X dim) := (principal γ g y-(γ y)⁻¹) i j
  have hf : ContDiffOn ℝ ∞ f Y :=
    (contDiffOn_principal_entry hγ hg i j).sub (contDiffOn_metric_inv_entry hγ i j)
  obtain ⟨F,hF,hNear⟩ := exists_global_smooth_germ_of_open f hY hf hx
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp hNear
  have hEq : EqOn F f U := hUsub
  rw [← (hNear.iteratedFDeriv ℝ n).eq_of_nhds]
  have hE (idx : Fin n → I dim) :
      |iteratedFDeriv ℝ n F x (fun s => axis (idx s))| ≤ smallJet γ g x := by
    let a (k : I dim) := (List.ofFn idx).count k
    have ha : (∑ k : I dim,a k) ≤ 8 := by
      have ha' := count_chartWord_sum (List.ofFn idx)
      rw [List.length_ofFn] at ha'
      exact ha'.trans_le hn
    rw [iteratedFDeriv_chart_axes_eq_chartPartial hF,← chartDerivativeWord_sorted a]
    change |chartDerivativeWord (sortedChartWord a) F x| ≤ _
    rw [show chartDerivativeWord (sortedChartWord a) F x = chartDerivativeWord (sortedChartWord a) f x from
      chartDerivativeWord_eqOn hU hEq _ hxU,chartDerivativeWord_sorted]
    exact abs_chartPartial_principal_sub_inverse_le_smallJet γ g x ha i j
  have hZero : 0 ≤ smallJet γ g x := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  exact norm_multilinear_le_of_chart_components _ _ hZero hE

end CalderonN
