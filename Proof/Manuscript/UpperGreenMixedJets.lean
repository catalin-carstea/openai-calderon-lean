module

public import Proof.Manuscript.MovingGreenMixedJets

import Proof.Manuscript.UpperGreenDatum
import Proof.CalderonN.FixedTube.DilatedGeometry
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN FixedTube
open scoped ContDiff Topology

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The part of the moving Green trace with fixed positive separation
has uniform angular jets, including their first unscaled base derivatives. -/
theorem exists_uniform_upper_movingGreen_mixed_jets
    (m : ℕ) {g₁ g₂ : MetricField dim}
    (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {γ : ℝ → MetricField dim} {E : ℝ → X dim × X dim → X dim} {e : ℝ → Frame dim}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × X dim => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X dim => e q.1 q.2 i))
    {S : Set ℝ} {K Y Y' Ω : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K)
    (hS₁ : S ⊆ Icc (-1 : ℝ) 1)
    (hY : IsOpen Y) (hYK : Y ⊆ K) (hKY' : K ⊆ Y')
    {ρ d D M : ℝ} (hρ : 0 < ρ) (hd : 0 < d) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y' Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ S, ∀ y ∈ K, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ S, ∀ r : X dim → ℝ, ContDiff ℝ ∞ r →
      (∀ y ∈ Y, r y ∈ Ioc 0 (ρ/2)) →
      ∀ {O₀ : Set (X dim × X dim)}, IsOpen O₀ → fixedSeparationSet 4 (d/2) ⊆ O₀ →
      ∀ F : X dim × X dim → ℝ,
      ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O₀ F →
      (∀ q ∈ fixedSeparationSet 4 (d/2), |F q| ≤ M) →
      ∀ {O : Set (X dim × X dim)}, IsOpen O → ∀ G : X dim × X dim → ℝ, ContDiffOn ℝ ∞ G O →
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim), normalGreenPoint E e (lam,(y,r y)) w ∈ O) →
      ∀ y ∈ Y, ‖fderiv ℝ r y‖ ≤ D →
      (∀ w ∈ standardSphere dim,
        let q := normalGreenPoint E e (lam,(y,r y)) w
        q ∈ fixedSeparationSet 3 d ∧ G =ᶠ[𝓝 q] F) →
      ∀ w : ↥(standardSphere dim), ∃ H : X dim × X dim → ℝ, ContDiff ℝ ∞ H ∧
        H =ᶠ[𝓝 (y,(w : X dim))]
          (fun q => movingGreenFluxDensity (γ lam) (dilatedMetric g₁ lam) (E lam) (e lam) r G
            (q.1,frameVector (e lam) q.1 q.2)) ∧
        ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun z => H (y,z)) (w : X dim)‖ ≤ C ∧
          ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun x => H (x,z)) y) (w : X dim)‖ ≤ C := by
  obtain ⟨A,hA,hDatum⟩ := exists_upper_fixedSeparation_datumJets hg₁ hg₂ hE he hS hK hS₁
    hd (half_pos hρ) hM (m+dim+4)
  obtain ⟨b,hb,hFloor⟩ := exists_upper_fixedSeparation_radius_floor hE he hS hK hKY' hd hNormal
  have hg (i j : I dim) : ContDiff ℝ ∞ (fun p : ℝ × X dim => dilatedMetric g₁ p.1 p.2 i j) :=
    contDiff_dilatedMetric_entry hg₁ i j
  have hgPos (lam : ℝ) (y : X dim) : (dilatedMetric g₁ lam y).PosDef := hg₁.2 _ (mem_univ _)
  obtain ⟨C,hC,hUpper⟩ := exists_uniform_framed_movingGreen_mixed_jets m
    hγ hγPos hg hgPos hE he hS hK hY hYK hKY' hρ hb hD hA hNormal hFrame
  refine ⟨C,hC,?_⟩
  intro lam hlam r hr hRad O₀ hO₀ hRoom F hF hMB O hO G hG hSphere y hy hSlope hTop w
  have hRad' := hRad y hy
  have hSep : d ≤ dist (normalGreenPoint E e (lam,(y,r y)) w).1 y := by
    simpa only [dist_eq_norm,normalGreenPoint] using (hTop w w.property).1.2.2
  have hbY := hFloor lam hlam y (hYK hy) (r y) ⟨hRad'.1.le,hRad'.2⟩ w w.property hSep
  have hJ := hDatum lam hlam y (hYK hy) (r y) hRad' hO₀ hRoom F G hF hMB hTop
  exact hUpper lam hlam r hr hRad hO G hG hSphere y hy hbY hSlope hJ w

end CalderonPaper
