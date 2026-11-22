module

public import Proof.Manuscript.MovingTrace.RadiusVelocityChartRawModels
public import Proof.Manuscript.MovingTrace.QuantizedVelocityChart
public import Proof.Manuscript.MovingTrace.SignedGeometryDirections
public import Proof.Manuscript.RadiusChartQuantization
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
open CalderonN Set Filter MeasureTheory
open scoped ContDiff Topology
set_option maxHeartbeats 7000000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "E" => X n
local notation "S" => standardSphere (n+1)
local notation "P" => MovingSymbolGeometry (n+1)

local instance : Fact (Module.finrank ℝ Z = (n+1)-1+1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

/-- Extend the chosen chart's two analytic radius witnesses to global
geometry while preserving the literal quantization on all physical points. -/
theorem exists_radius_velocity_chart_models
    {G : BallPoissonTube (MovingSymbolGeometry (n+1)) (n+1)}
    (C : SignedPoissonCollar (n := n) G) (A : SmoothRadialVelocity G)
    {Y : Set Z} (hY : IsCompact (closure Y)) {ρ B δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hJA : signedGeometryCompact Y ρ B δ ⊆ A.U)
    {Z₀ : Set P} (hZ₀ : Z₀ ⊆ movingSymbolGeometryCompact Y ρ B)
    {χ η : Z → ℂ} (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hχS : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (hηS : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source)
    {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {Kζ : Set E} (hKζ : IsCompact Kζ)
    (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) (hOne : EqOn ζ 1 (angularChartSupport C.pole η))
    (hPrincipal : ∀ p ∈ Z₀, ∀ x ξ : E, ξ ≠ 0 →
      HasDerivAt
        (fun r => C.velocityPrincipalSymbol A (χ ∘ angularPoint C.pole) ζ
          (movingSymbolSignedRadiusEquiv (n+1)
            (((movingSymbolSignedRadiusEquiv (n+1)).symm p).1,r),x) ξ) 0 0) :
    let J₀ := movingSymbolGeometryCompact Y ρ B
    let Jpos := J₀ ∩ {p : P | 0 < p.1.2.2}
    let L := movingSymbolSignedRadiusEquiv (n+1)
    ∃ aFirst aTail : P × E → E → ℂ,
      GeometryClassicalSymbolPrincipalZero (dim := n+1) univ J₀ Z₀ 1 aFirst ∧
      UniformGeometryClassicalAngularSymbol (dim := n+1) univ Jpos 1 aTail ∧
      (∀ p ∈ J₀, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
        let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
        let i := fun ξ => angularFourierPhase (dim := n+1) x ξ * aFirst (p,x) ξ * angularFourierTransform (dim := n+1) f ξ
        Integrable f ∧ Integrable i ∧
          χ (angularPoint C.pole x) *
            radiusFirstSphereOperator (dim := n+1) L A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
              ∫ ξ, i ξ) ∧
      (∀ p ∈ Jpos, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
        let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
        let i := fun ξ => angularFourierPhase (dim := n+1) x ξ * aTail (p,x) ξ * angularFourierTransform (dim := n+1) f ξ
        Integrable f ∧ Integrable i ∧
          χ (angularPoint C.pole x) *
            radiusTaylorSphereOperator (dim := n+1) L A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
              ∫ ξ, i ξ) := by
  obtain ⟨U,a,hU,hJU,hUA,H,hQuant,hExact,ha₀,hB₀,hPr,D,b,hD,hDD,hD₀,hb,hAnn,hCoeff,hSuppB⟩ :=
    C.exists_quantized_velocity_chart_symbol A (signedGeometryCompact_isCompact hY ρ B δ)
      hJA hχ hη hχS hηS hζ hKζ hζ₀ hOne
  exact C.radius_velocity_chart_models_of_exact_symbol A hY hρ hδ hZ₀ hχ hη hχS hηS
    hPrincipal hU hJU H hQuant ha₀ hPr hD hDD hb hAnn hCoeff
    (fun k p x ξ hx => hSuppB k p x ξ (fun h => hx h.1))

end SignedPoissonCollar
end CalderonPaper
