module

public import Proof.CalderonN.InteriorJetCutoff
public import Proof.CalderonN.HarmonicSeries

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.GreenWeak
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {d : ℕ} [NeZero d]

private theorem laplace_eq_of_eventuallyEq (g : (MetricField d)) {f k : (X d) → ℝ} {x : (X d)}
    (heq : f =ᶠ[𝓝 x] k) : laplace g f x = laplace g k x := by
  obtain ⟨U,he,hU,hx⟩ := eventually_nhds_iff.mp heq
  exact laplace_congrOn hU (fun _ _ => rfl) he hx

/-- An absolutely summable series of classical harmonic L² classes
has a classical harmonic representative for its actual L² sum. -/
theorem exists_harmonic_representative_of_hasSum
    {U : Set (X d)} (hU : IsOpen U) {g : (MetricField d)} (hg : SmoothMetric U g)
    {ι : Type*} [Countable ι] (u : ι → ChartL2 (d := d) U) (a : ι → (X d) → ℝ)
    (ha : ∀ i, Harmonic U g (a i)) (hae : ∀ i, (u i : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] a i)
    (hab : Summable (fun i => ‖u i‖)) {Q : ChartL2 (d := d) U} (hQ : HasSum u Q) :
    ∃ F : (X d) → ℝ, Harmonic U g F ∧
      (Q : (X d) → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] F := by
  let F (x : (X d)) := ∑' i, a i x
  refine ⟨F,?_,?_⟩
  · have hJet := harmonicInteriorJets_of_smoothMetric hU hg
    suffices hlocal : ∀ x ∈ U, ContDiffAt ℝ ∞ F x ∧ laplace g F x = 0 by
      exact ⟨fun x hx => (hlocal x hx).1.contDiffWithinAt,fun x hx => (hlocal x hx).2⟩
    intro x hx
    obtain ⟨χ,hχ,hχc,hχU,hPlateau⟩ :=
      Elliptic.exists_plateau_cutoff hU (isCompact_singleton (x := x))
        (singleton_subset_iff.mpr hx)
    have hχx := hPlateau x (mem_singleton x)
    let b (i : ι) (y : (X d)) := χ y * a i y
    have hb (i : ι) : ContDiff ℝ ∞ (b i) :=
      Elliptic.contDiff_mul_of_tsupport_subset hU hχ hχU (ha i).1
    choose C hC hBound using exists_global_cutoff_jet_bound hU hJet hχ hχc hχU
    have hNorm (k : ℕ) (i : ι) (y : (X d)) : ‖iteratedFDeriv ℝ k (b i) y‖ ≤ C k * ‖u i‖ :=
      hBound k (u i) (a i) (ha i) (hae i) y
    let G (y : (X d)) := ∑' i, b i y
    have hG : ContDiff ℝ ∞ G := by
      apply contDiff_tsum (v := fun k i => C k * ‖u i‖) hb
      · exact fun k _ => hab.mul_left (C k)
      · exact fun k i y _ => hNorm k i y
    have hEq : G =ᶠ[𝓝 x] F := by
      filter_upwards [hχx] with y hy
      simp only [G,F,b,hy,one_mul]
    have hLap (i : ι) : laplace g (b i) x = 0 := by
      have heq : b i =ᶠ[𝓝 x] a i := by
        filter_upwards [hχx] with y hy
        simp only [b,hy,one_mul]
      exact (laplace_eq_of_eventuallyEq g heq).trans ((ha i).2 x hx)
    have hp := hasSum_laplace_of_uniform_jets hb (fun k i => C k * ‖u i‖)
      (fun k => hab.mul_left (C k)) hNorm g x
    simp only [hLap] at hp
    exact ⟨hG.contDiffAt.congr_of_eventuallyEq hEq.symm,
      (laplace_eq_of_eventuallyEq g hEq).symm.trans (hp.unique hasSum_zero)⟩
  · have hsum := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hab)
    rw [hQ.tsum_eq] at hsum
    filter_upwards [hsum, ae_all_iff.mpr hae] with x hs hx
    simpa only [F,hx] using hs.tsum_eq.symm

end CalderonN
