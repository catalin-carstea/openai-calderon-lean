/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.InvariantTranslation
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Extension

public section

noncomputable section

namespace TauCeti
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient InnerProductSpace
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem W1p0.norm_value_extendByZeroL (hsub : Omega ≤ (⊤ : Opens E))
    (u : W1p0 mu Omega p) :
    ‖W1p.value (W1p0.extendByZeroL hsub u : W1p mu ⊤ p)‖ =
      ‖W1p.value (u : W1p mu Omega p)‖ := by
  rw [W1p0.value_extendByZeroL]
  exact LinearIsometry.norm_map _ _

private theorem W1p0.norm_gradient_extendByZeroL (hsub : Omega ≤ (⊤ : Opens E))
    (u : W1p0 mu Omega p) :
    ‖W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu ⊤ p)‖ =
      ‖W1p.gradient (u : W1p mu Omega p)‖ := by
  rw [W1p0.gradient_extendByZeroL]
  exact LinearIsometry.norm_map _ _

/-! ### Domains mapped onto themselves by the translation -/

/-- **Difference quotients preserve zero boundary values.** If translation by `t • w` maps `Ω`
onto itself, then the difference quotient of `u ∈ W^{1,p}_0(Ω)` in the direction `w`
with step `t` lies in `W^{1,p}_0(Ω)`. -/
theorem W1p.differenceQuotient_mem_w1p0Submodule {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) Omega Omega) (hΩ : ∀ x, x + t • w ∈ Omega → x ∈ Omega)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    W1p.differenceQuotient le_rfl w t hVO u ∈ w1p0Submodule mu Omega p := by
  rw [W1p.differenceQuotient_def, W1p.restrictL_self]
  exact (w1p0Submodule mu Omega p).toSubmodule.smul_mem _
    (sub_mem (W1p.translate_mem_w1p0Submodule hVO hΩ hu) hu)

/-- **Difference quotients commute with extension by zero.** Let translation by `t • w` map `Ω`
onto itself and `p < ∞`. If `g ∈ W^{1,p}_0(Ω)` is the difference quotient of `u ∈ W^{1,p}_0(Ω)`
in the direction `w` with step `t`, then the zero-extension of `g` to the whole space is the
difference quotient of the zero-extension of `u`. -/
theorem W1p0.extendByZeroL_eq_differenceQuotient {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) Omega Omega) (hΩ : ∀ x, x + t • w ∈ Omega → x ∈ Omega)
    {u g : W1p0 mu Omega p}
    (hg : (g : W1p mu Omega p) = W1p.differenceQuotient le_rfl w t hVO (u : W1p mu Omega p)) :
    (W1p0.extendByZeroL le_top g : W1p mu ⊤ p) =
      W1p.differenceQuotient le_rfl w t (Set.mapsTo_univ (· + t • w) _)
        (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) := by
  have hm := Omega.isOpen.measurableSet
  have hsub : (Omega : Set E) ⊆ ((⊤ : Opens E) : Set E) := subset_univ _
  -- Both sides vanish off `Ω`, and on `Ω` they are the difference quotient of `u`.
  have hext : ∀ v : Lp ℝ p (mu.restrict Omega),
      (extendByZeroLpₗᵢ ℝ mu hm hsub v : E → ℝ) =ᵐ[mu] (Omega : Set E).indicator v := fun v => by
    simpa only [Opens.coe_top, Measure.restrict_univ] using coeFn_extendByZeroLpₗᵢ ℝ hm hsub v
  refine W1p.ext_value (Lp.ext ?_)
  rw [W1p0.value_extendByZeroL, hg]
  filter_upwards [ae_restrict_of_ae (hext _), W1p.value_differenceQuotient_ae le_rfl w t
      (Set.mapsTo_univ (· + t • w) _) (W1p0.extendByZeroL le_top u : W1p mu ⊤ p),
    ae_restrict_of_ae (hext (W1p.value (u : W1p mu Omega p))),
    ae_restrict_of_ae ((measurePreserving_add_right mu (t • w)).quasiMeasurePreserving.ae_eq_comp
      (hext (W1p.value (u : W1p mu Omega p)))),
    ae_restrict_of_ae ((ae_restrict_iff' hm).1
      (W1p.value_differenceQuotient_ae le_rfl w t hVO (u : W1p mu Omega p)))]
    with x h1 h2 h3 h4 h5
  simp only [Function.comp_apply] at h4
  rw [h1, h2, W1p0.value_extendByZeroL, h4, h3]
  by_cases hx : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem (hVO hx), h5 hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx,
      indicator_of_notMem (mt (hΩ x) hx), sub_zero, mul_zero]

/-- **The difference-quotient bound for zero boundary values.** If translation by `t • w` maps
`Ω` onto itself and `p < ∞`, the difference quotient of `u ∈ W^{1,p}_0(Ω)` satisfies
`‖D^t_w u‖_p ≤ ‖w‖ ‖∇u‖_p`, with no compactness and uniformly in `t`, as on the whole space. -/
theorem W1p0.norm_value_differenceQuotient_le (hp : p ≠ ∞) {w : E} {t : ℝ}
    (hVO : MapsTo (· + t • w) Omega Omega) (hΩ : ∀ x, x + t • w ∈ Omega → x ∈ Omega)
    (u : W1p0 mu Omega p) :
    ‖W1p.value (W1p.differenceQuotient le_rfl w t hVO (u : W1p mu Omega p))‖ ≤
      ‖w‖ * ‖W1p.gradient (u : W1p mu Omega p)‖ := by
  have h := W1p.norm_value_differenceQuotient_le hp w t (W1p0.extendByZeroL le_top u : W1p mu ⊤ p)
  rwa [← W1p0.extendByZeroL_eq_differenceQuotient (g := ⟨_,
      W1p.differenceQuotient_mem_w1p0Submodule hVO hΩ u.2⟩) hVO hΩ rfl,
    W1p0.norm_value_extendByZeroL, W1p0.norm_gradient_extendByZeroL] at h

end TauCeti
