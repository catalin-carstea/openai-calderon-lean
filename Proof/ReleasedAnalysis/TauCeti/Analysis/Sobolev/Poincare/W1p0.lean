/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Poincare.Slab
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Zero

/-! From Proof/TauCeti/Analysis/Sobolev/Poincare/W1p0.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

 































public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {p : ENNReal} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
 

private theorem norm_testFunctionLp_eq (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := volume) p phi‖ = (eLpNorm (phi : _ → ℝ) p volume).toReal := by
  rw [Lp.norm_def, ← Lp.enorm_def, enorm_testFunctionLp_eq_eLpNorm]

omit [Fact (1 ≤ p)] in
 

private theorem norm_gradientTestFunctionLp_eq (phi : 𝓓(Omega, ℝ)) :
    ‖gradientTestFunctionLp (mu := volume) p phi‖ =
      (eLpNorm (fderiv ℝ (phi : _ → ℝ)) p volume).toReal := by
  rw [Lp.norm_def, ← Lp.enorm_def, enorm_gradientTestFunctionLp_eq_eLpNorm_fderiv]

 
private theorem norm_testFunctionLp_le_of_subset_slab (hp : p ≠ ∞) {i : Fin (n + 1)} {a b : ℝ}
    (hab : a ≤ b)
    (hOmega : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc a b)
    (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := volume) p phi‖ ≤
      (b - a) * ‖gradientTestFunctionLp (mu := volume) p phi‖ := by
  have hfinite : eLpNorm (fderiv ℝ (phi : _ → ℝ)) p volume ≠ ∞ :=
    ((phi.contDiff.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
      (phi.hasCompactSupport.fderiv ℝ)).ne
  have hslab := eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab (i := i)
    (phi.contDiff.of_le (by simp)) hab
    (fun x hx => hOmega x (phi.tsupport_subset (subset_tsupport _ hx))) Fact.out hp
  rw [norm_testFunctionLp_eq, norm_gradientTestFunctionLp_eq,
    ← ENNReal.toReal_ofReal (sub_nonneg.2 hab), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) hfinite) hslab

 





theorem W1p.norm_value_le_mul_norm_gradient_of_subset_slab (hp : p ≠ ∞) {i : Fin (n + 1)}
    {a b : ℝ} (hab : a ≤ b)
    (hOmega : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc a b)
    {u : W1p volume Omega p} (hu : u ∈ w1p0Submodule volume Omega p) :
    ‖W1p.value u‖ ≤ (b - a) * ‖W1p.gradient u‖ := by
  have hclosedL : IsClosed {v : W1p volume Omega p |
      ‖W1p.valueL v‖ ≤ (b - a) * ‖W1p.gradientL v‖} :=
    isClosed_le (W1p.valueL (mu := volume) (Omega := Omega) (p := p)).continuous.norm
      ((W1p.gradientL (mu := volume) (Omega := Omega) (p := p)).continuous.norm.const_mul _)
  have hclosed : IsClosed {v : W1p volume Omega p |
      ‖W1p.value v‖ ≤ (b - a) * ‖W1p.gradient v‖} := by
    simpa only [W1p.valueL_apply, W1p.gradientL_apply] using hclosedL
  refine w1p0Submodule_subset_of_isClosed hclosed (fun phi => ?_) hu
  simpa using norm_testFunctionLp_le_of_subset_slab hp hab hOmega phi

 




theorem W1p.norm_value_le_mul_norm_gradient_of_subset_ball
    {c : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ≠ ∞) {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball c R)
    {u : W1p volume Omega p} (hu : u ∈ w1p0Submodule volume Omega p) :
    ‖W1p.value u‖ ≤ 2 * R * ‖W1p.gradient u‖ := by
  rcases le_or_gt R 0 with hR | hR
  · have hball : Metric.ball c R = ∅ := Metric.ball_eq_empty.2 hR
    have hempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ∅ :=
      subset_empty_iff.1 (hball ▸ hOmega)
     
     
    have hbot : ae (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) = ⊥ :=
      ae_eq_bot.2 (by rw [hempty, Measure.restrict_empty])
    have hvalue : W1p.value u = 0 := Lp.ext (by rw [hbot]; exact Filter.eventually_bot)
    have hgradient : W1p.gradient u = 0 := Lp.ext (by rw [hbot]; exact Filter.eventually_bot)
    rw [hvalue, hgradient]
    simp
  have hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      x (0 : Fin (n + 1)) ∈ Icc (c 0 - R) (c 0 + R) :=
    fun x hx => apply_mem_Icc_of_mem_ball (hOmega hx) 0
  have hwidth : (c 0 + R) - (c 0 - R) = 2 * R := by ring
  simpa only [hwidth] using W1p.norm_value_le_mul_norm_gradient_of_subset_slab hp
    (by linarith : c 0 - R ≤ c 0 + R) hslab hu

end TauCeti
