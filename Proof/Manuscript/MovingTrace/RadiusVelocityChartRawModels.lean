module

public import Proof.Manuscript.MovingTrace.RadiusClassicalLocalAssembly
public import Proof.Manuscript.MovingTrace.VelocityChartPlaneDatum
public import Proof.Manuscript.MovingTrace.AngularChartCutoffs
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
theorem radius_velocity_chart_models_of_exact_symbol
    {G : BallPoissonTube (MovingSymbolGeometry (n+1)) (n+1)}
    (C : SignedPoissonCollar (n := n) G) (A : SmoothRadialVelocity G)
    {Y : Set Z} (hY : IsCompact (closure Y)) {ρ B δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    {Z₀ : Set P} (hZ₀ : Z₀ ⊆ movingSymbolGeometryCompact Y ρ B)
    {χ η : Z → ℂ} (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hχS : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (hηS : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source)
    {ζ : E → ℂ}
    (hPrincipal : ∀ p ∈ Z₀, ∀ x ξ : E, ξ ≠ 0 →
      HasDerivAt
        (fun r => C.velocityPrincipalSymbol A (χ ∘ angularPoint C.pole) ζ
          (movingSymbolSignedRadiusEquiv (n+1)
            (((movingSymbolSignedRadiusEquiv (n+1)).symm p).1,r),x) ξ) 0 0)
    {U : Set P} (hU : IsOpen U) (hJU : signedGeometryCompact Y ρ B δ ⊆ U)
    {a : P × E → E → ℂ}
    (H : CompactClassicalAngularSymbol (U ×ˢ (univ : Set E))
      (signedGeometryCompact Y ρ B δ ×ˢ angularChartSupport C.pole χ) 1 a)
    (hQuant : ∀ p ∈ U, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
      let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
      let i := fun ξ => angularFourierPhase (dim := n+1) x ξ * a (p,x) ξ *
        angularFourierTransform (dim := n+1) f ξ
      Integrable f ∧ Integrable i ∧
        χ (angularPoint C.pole x) * A.operator p (fun w => η w*u w) (angularPoint C.pole x)
          = ∫ ξ, i ξ)
    (ha₀ : ∀ p x ξ, x ∉ angularChartSupport C.pole χ → a (p,x) ξ = 0)
    (hPr : ∀ p ∈ U, ∀ x ξ, ξ ≠ 0 → H.coefficient 0 (p,x) ξ =
      C.velocityPrincipalSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ)
    {D : Set E} {b : ℕ → P × E → E → ℂ} (hD : IsOpen D) (hDD : unitAnnulus E ⊆ D)
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hAnn : LocalNormalizedAnnulusJetBounds U a b)
    (hCoeff : H.coefficient = homogeneousAngularCoefficient b)
    (hSuppB : ∀ k p x ξ, x ∉ angularChartSupport C.pole χ → b k (p,x) ξ = 0) :
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
  let J := signedGeometryCompact Y ρ B δ
  let J₀ := movingSymbolGeometryCompact Y ρ B
  let Jpos := J₀ ∩ {p : P | 0 < p.1.2.2}
  let L := movingSymbolSignedRadiusEquiv (n+1)
  let K := angularChartSupport C.pole χ
  have hJ : IsCompact J := signedGeometryCompact_isCompact hY ρ B δ
  have hJ₀ : IsCompact J₀ := isCompact_movingSymbolGeometryCompact hY ρ B
  have hK : IsCompact K := angularChartSupport_isCompact C.pole χ hχS
  have hJ₀J : J₀ ⊆ J := movingSymbolGeometryCompact_subset_signed hδ.le
  have hZeroJ : MapsTo (geometryZeroRadiusLinear L) J₀ J := by
    intro p hp
    rw [geometryZeroRadiusLinear_apply]
    exact signedGeometryCompact_radius_line_mem hp ⟨neg_nonpos.mpr hδ.le,hρ.le⟩
  have hSeg : J₀ ⊆ geometryRadiusSegment L U := movingSymbolGeometryCompact_subset_radiusSegment hδ.le hJU
  have hPr₀ (p : P) (hp : p ∈ Z₀) (x ξ : E) (hξ : ξ ≠ 0) :
      radiusFirstAngular L (H.coefficient 0) (geometryZeroRadiusLinear L p,x) ξ = 0 := by
    have hp0 := hZ₀ hp
    have hHd := hasDerivAt_radiusFirstAngular_line (e := L) hU isClosed_singleton.isOpen_compl
      (H.coefficientSmooth 0) (L.symm p).1 0 (hJU (hZeroJ hp0)) x
      (show ξ ∈ ({0}ᶜ : Set E) from hξ)
    have he : (fun r => H.coefficient 0 (L ((L.symm p).1,r),x) ξ) =ᶠ[𝓝 (0:ℝ)]
        (fun r => C.velocityPrincipalSymbol A (χ ∘ angularPoint C.pole) ζ
          (L ((L.symm p).1,r),x) ξ) := by
      filter_upwards [signedGeometryCompact_eventually_radius_mem hδ hρ hp0] with r hr
      exact hPr _ (hJU hr) x ξ hξ
    simpa only [geometryZeroRadiusLinear_apply] using
      hHd.unique ((hPrincipal p hp x ξ hξ).congr_of_eventuallyEq he)
  obtain ⟨aF,aT,hF,hT,hFval,hTval,M,hM,hMbd⟩ :=
    exists_radius_classical_symbol_pair (dim := n+1) L hU hJ hJU hJ₀ hSeg hZeroJ hZ₀
      hD hDD hK H hb hAnn hCoeff
      (fun p x hx ξ => ha₀ p x ξ hx) (fun k p x hx ξ => hSuppB k p x ξ hx) hPr₀
  have hFirst (p : P) (hp : p ∈ J₀) (u : Z → ℂ) (hu : smoothNear u S) (x : E) :
      let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
      let s := fun ξ => angularFourierPhase (dim := n+1) x ξ *
        radiusFirstAngular L a (geometryZeroRadiusLinear L p,x) ξ * angularFourierTransform (dim := n+1) f ξ
      Integrable f ∧ Integrable s ∧
        χ (angularPoint C.pole x) *
          radiusFirstSphereOperator (dim := n+1) L A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
            ∫ ξ, s ξ := by
    let q := (L.symm p).1
    let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
    let uη := fun z => η z*u z
    let T (r : ℝ) := A.operator (L (q,r)) uη (angularPoint C.pole x)
    let O := {r | L (q,r) ∈ J}
    have hO : O ∈ 𝓝 (0:ℝ) := signedGeometryCompact_eventually_radius_mem hδ hρ hp
    obtain ⟨hf,hfK⟩ := compactSmooth_angularDatum C.pole hη hu hηS
    have hAtZero := hQuant (L (q,0)) (hJU (hZeroJ hp)) u hu x
    have hD := radiusChartQuantization_first (dim := n+1) (e := L) hU H.smooth q x f hf hfK T
      (χ (angularPoint C.pole x)) hO (fun r hr => hJU hr)
      (fun r hr => (hQuant (L (q,r)) (hJU hr) u hu x).2.2) hAtZero.2.1
      M (fun r hr ξ => hMbd (L (q,r)) hr x ξ)
    exact ⟨hAtZero.1,hD⟩
  refine ⟨aF,aT,hF,hT.restrict_geometry (show Jpos ⊆ J₀ from inter_subset_left),?_,?_⟩
  · intro p hp u hu x
    simp only [hFval p hp]
    exact hFirst p hp u hu x
  · intro p hp u hu x
    let q := (L.symm p).1
    let r := (L.symm p).2
    let f := fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)
    let uη := fun z => η z*u z
    let T (r : ℝ) := A.operator (L (q,r)) uη (angularPoint C.pole x)
    have hr : r ≠ 0 := (show 0 < r from hp.2).ne'
    have hR : L (q,r) = p := L.apply_symm_apply p
    have hAtZero := hQuant (L (q,0)) (hJU (hZeroJ hp.1)) u hu x
    have hAt := hQuant p (hJU (hJ₀J hp.1)) u hu x
    have hD := hFirst p hp.1 u hu x
    have hA : χ (angularPoint C.pole x) * T r = ∫ ξ, angularFourierPhase (dim := n+1) x ξ *
        a (L (q,r),x) ξ * angularFourierTransform (dim := n+1) f ξ := by
      simpa only [T,hR,uη] using hAt.2.2
    have hInt : Integrable (fun ξ => angularFourierPhase (dim := n+1) x ξ * a (L (q,r),x) ξ *
        angularFourierTransform (dim := n+1) f ξ) := by simpa only [hR] using hAt.2.1
    have hQ := radiusChartQuantization_remainder (dim := n+1) (e := L) hU H.smooth q r hr (hSeg hp.1) x f T
      (χ (angularPoint C.pole x)) hAtZero.2.2 hA hD.2.2 hAtZero.2.1 hInt hD.2.1
    simp only [hTval p hp.1]
    refine ⟨hAt.1,?_⟩
    simpa only [hR,radiusTaylorSphereOperator,radiusFirstSphereOperator,T,uη] using hQ

end SignedPoissonCollar
end CalderonPaper
