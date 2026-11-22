module

public import Proof.CalderonN.Chart
public import Mathlib.Analysis.Calculus.SmoothSeries

import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {d : ℕ}

private abbrev FirstJet (d : ℕ) := X d →L[ℝ] ℝ
private abbrev SecondJet (d : ℕ) := X d →L[ℝ] FirstJet d

private def laplaceFirstJet (g : (MetricField d)) (x : (X d)) : FirstJet d →L[ℝ] ℝ :=
  ∑ i, ∑ j, ∑ k, (-((g x)⁻¹ i j * christoffel g x k i j)) •
    ContinuousLinearMap.apply ℝ ℝ (axis k)

private def laplaceSecondJet (g : (MetricField d)) (x : (X d)) : SecondJet d →L[ℝ] ℝ :=
  ∑ i, ∑ j, (g x)⁻¹ i j •
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).comp (ContinuousLinearMap.apply ℝ (FirstJet d) (axis i))

private theorem laplace_eq_jetEval {g : (MetricField d)} {u : (X d) → ℝ} {x : (X d)}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    laplace g u x = laplaceFirstJet g x (fderiv ℝ u x) +
      laplaceSecondJet g x (fderiv ℝ (fderiv ℝ u) x) := by
  have hsecond (i j : (I d)) :
      coordDeriv i (coordDeriv j u) x = fderiv ℝ (fderiv ℝ u) x (axis i) (axis j) := by
    let L := ContinuousLinearMap.apply ℝ ℝ (axis j)
    have h := L.hasFDerivAt.comp x hu.hasFDerivAt
    change fderiv ℝ (L ∘ fderiv ℝ u) x (axis i) = _
    rw [h.fderiv]
    rfl
  unfold laplace
  simp_rw [hsecond]
  simp only [laplaceFirstJet, laplaceSecondJet, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, coordDeriv,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [sub_eq_add_neg, mul_add, mul_neg, Finset.mul_sum, mul_assoc, neg_mul,
    Finset.sum_neg_distrib]
  exact add_comm _ _

set_option maxHeartbeats 2200000 in
/-- A normally convergent smooth series commutes with the chart Laplacian. -/
theorem hasSum_laplace_of_uniform_jets {ι : Type*} {f : ι → (X d) → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (v : ℕ → ι → ℝ)
    (hs : ∀ k : ℕ, Summable (v k))
    (hbound : ∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i)
    (g : (MetricField d)) (x : (X d)) :
    HasSum (fun i => laplace g (f i) x) (laplace g (fun y => ∑' i, f i y) x) := by
  let F (x : (X d)) := ∑' i, f i x
  have h₀ : ∀ x : (X d), Summable (fun i => f i x) := fun x =>
    (hs 0).of_norm_bounded (by simpa only [norm_iteratedFDeriv_zero] using fun i => hbound 0 i x)
  have h₁ (i : ι) (x : (X d)) : ‖fderiv ℝ (f i) x‖ ≤ v 1 i := by
    simpa only [norm_iteratedFDeriv_one] using hbound 1 i x
  have h₂ (i : ι) (x : (X d)) : ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ v 2 i := by
    rw [← norm_iteratedFDeriv_one (x := x) (fderiv ℝ (f i)), norm_iteratedFDeriv_fderiv]
    exact hbound 2 i x
  have hf' (i : ι) : ContDiff ℝ ∞ (fderiv ℝ (f i)) := (hf i).fderiv_right (by simp)
  have d₁ : fderiv ℝ F = fun x => ∑' i, fderiv ℝ (f i) x :=
    fderiv_tsum (hs 1) (fun i => (hf i).differentiable (by simp)) h₁ (h₀ 0)
  have hsecond : HasFDerivAt (fderiv ℝ F) (∑' i, fderiv ℝ (fderiv ℝ (f i)) x) x := by
    rw [d₁]
    exact hasFDerivAt_tsum (hs 2) (fun i x => ((hf' i).differentiable (by simp) x).hasFDerivAt) h₂
      ((hs 1).of_norm_bounded (fun i => h₁ i 0)) x
  have hs₁ : Summable (fun i => fderiv ℝ (f i) x) := (hs 1).of_norm_bounded (fun i => h₁ i x)
  let F₂ : ι → SecondJet d := fun i => fderiv ℝ (fderiv ℝ (f i)) x
  have hB₂ : ∀ i, ‖F₂ i‖ ≤ v 2 i := fun i => h₂ i x
  have hs₂ : Summable F₂ :=
    Summable.of_norm_bounded (E := SecondJet d) (f := F₂) (g := v 2) (hs 2) hB₂
  have hL₁ : HasSum (fun i => laplaceFirstJet g x (fderiv ℝ (f i) x))
      (laplaceFirstJet g x (fderiv ℝ F x)) := by
    rw [d₁]
    exact (laplaceFirstJet g x).hasSum hs₁.hasSum
  have hL₂ : HasSum (fun i => laplaceSecondJet g x (fderiv ℝ (fderiv ℝ (f i)) x))
      (laplaceSecondJet g x (fderiv ℝ (fderiv ℝ F) x)) := by
    rw [hsecond.fderiv]
    exact (laplaceSecondJet g x).hasSum hs₂.hasSum
  have h := hL₁.add hL₂
  have he (i : ι) := laplace_eq_jetEval (g := g) ((hf' i).differentiable (by simp) x)
  have hF := laplace_eq_jetEval (g := g) hsecond.differentiableAt
  rw [show (fun i => laplace g (f i) x) = _ from funext he, hF]
  exact h

end CalderonN
