module

public import Proof.Manuscript.MovingTrace.VelocityClassicalSymbol
public import Proof.Manuscript.MovingTrace.VelocityChartQuantization
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter MeasureTheory
open OAI.AnisotropicCalderon.SmoothSphereRotation
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

def ChartQuantization (A : SmoothRadialVelocity G) (χ η : Z → ℂ)
    (s : Q → E → ℂ) (J : Set P) : Prop :=
  ∀ p ∈ J, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
    let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
    let integrand := fun ξ => angularFourierPhase (dim := n+1) x ξ * s (p,x) ξ * angularFourierTransform (dim := n+1) f ξ
    Integrable f ∧ Integrable integrand ∧
      χ (angularPoint C.pole x) * A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
        ∫ ξ, integrand ξ

/-- Choose the cutoffs, parameter domain, and homogeneous expansion for
one literal stereographic chart. The annular jet witnesses are retained
for differentiating in the independent radius. -/
theorem exists_quantized_velocity_chart_symbol
    (A : SmoothRadialVelocity G) {J : Set P} (hJ : IsCompact J) (hJU : J ⊆ A.U)
    {χ η : Z → ℂ} (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hχS : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (hηS : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source)
    {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {Kζ : Set E} (hKζ : IsCompact Kζ)
    (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) (hOne : EqOn ζ 1 (angularChartSupport C.pole η)) :
    ∃ (U : Set P) (s : Q → E → ℂ),
      IsOpen U ∧ J ⊆ U ∧ U ⊆ A.U ∧
      ∃ H : CompactClassicalAngularSymbol (U ×ˢ (univ : Set E))
        (J ×ˢ angularChartSupport C.pole χ) 1 s,
        C.ChartQuantization A χ η s U ∧
        (∀ p ∈ U, ∀ x ξ, s (p,x) ξ =
          C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ) ∧
        (∀ p x ξ, x ∉ angularChartSupport C.pole χ → s (p,x) ξ = 0) ∧
        (∀ k p x ξ, x ∉ angularChartSupport C.pole χ ∩ Kζ → H.coefficient k (p,x) ξ = 0) ∧
        (∀ p ∈ U, ∀ x ξ, ξ ≠ 0 → H.coefficient 0 (p,x) ξ =
          C.velocityPrincipalSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ) ∧
        ∃ (D : Set E) (b : ℕ → Q → E → ℂ),
          IsOpen D ∧ unitAnnulus E ⊆ D ∧ D ⊆ {0}ᶜ ∧
          (∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D)) ∧
          LocalNormalizedAnnulusJetBounds U s b ∧
          H.coefficient = homogeneousAngularCoefficient b ∧
          (∀ k p x ξ, x ∉ angularChartSupport C.pole χ ∩ Kζ → b k (p,x) ξ = 0) := by
  let Kχ := angularChartSupport C.pole χ
  have hKχ : IsCompact Kχ := angularChartSupport_isCompact C.pole χ hχS
  have hχc : ContDiff ℝ ∞ (χ ∘ angularPoint C.pole) := by
    obtain ⟨O,hO,hSO,hχO⟩ := hχ
    apply contDiffOn_univ.mp
    exact hχO.comp (angularPoint_contDiff C.pole).contDiffOn
      (fun x _ => hSO (angularPoint_mem_standardSphere C.pole x))
  obtain ⟨U,s,hU,hJU',hUA,H,hExact,hs₀,hB₀,hPrincipal,hAnnulus⟩ :=
    C.exists_velocity_classical_symbol A hJ hJU hχc hζ hKχ hKζ
      (fun x hx => angularDatum_zero_outside_chartSupport C.pole χ hx) hζ₀
  refine ⟨U,s,hU,hJU',hUA,H,?_,hExact,hs₀,hB₀,hPrincipal,hAnnulus⟩
  obtain ⟨D,b,hD,hDD,hD₀,hb,hRemainder,hCoeff,hSuppB⟩ := hAnnulus
  intro p hp u hu x
  have hs : Continuous (fun q : E × E => s (p,q.1) q.2) := by
    apply ContDiff.continuous (n := ∞) (𝕜 := ℝ)
    apply contDiffOn_univ.mp
    exact H.smooth.comp (((contDiff_const (c := p)).prodMk contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun _ _ => ⟨⟨hp,mem_univ _⟩,mem_univ _⟩)
  obtain ⟨H₀,_⟩ := classicalSymbol_of_localAnnulus hU hD hDD isCompact_singleton
    (singleton_subset_iff.mpr hp) hKχ s b H.smooth hb hRemainder
  obtain ⟨B,hB,hBound⟩ := H₀.remainder 0 0 0
  have hGrowth (x ξ : E) : ‖s (p,x) ξ‖ ≤ B*(1+‖ξ‖) := by
    by_cases hx : x ∈ Kχ
    · simpa [angularMixedJet,Finset.sum_range_zero,Int.cast_one,
        norm_iteratedFDeriv_zero,Real.rpow_one] using hBound (p,x) ⟨mem_singleton _,hx⟩ ξ
    · rw [hs₀ p x ξ hx,norm_zero]
      positivity
  exact C.velocity_chart_quantization A (hUA hp) hχ hη hχS hηS hζ hKζ hζ₀ hOne
    hs hB.le hGrowth (hExact p hp) u hu x


end SignedPoissonCollar
end CalderonPaper
