module

public import Proof.Manuscript.MovingTrace.RadiusVelocityChartModels
public import Proof.Manuscript.MovingTrace.MovingAdjointOperatorAssembly
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
open CalderonN MeasureTheory Set
open scoped ContDiff
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "d" => n+1
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "P" => MovingSymbolGeometry (n+1)
local notation "E" => AngularCoordinates (n+1)

/-- The two radius operators use the exact quantization of the one signed
adjoint model in every stereographic chart and its own off-diagonal kernels. -/
theorem movingTrace_radius_classes_of_exact_kernels
    [Fact (Module.finrank ℝ Z = d-1+1)]
    {G : BallPoissonTube P d} (A : SmoothRadialVelocity G)
    {Y : Set Z} (hY : IsCompact (closure Y)) {ρ B δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (hJA : signedGeometryCompact Y ρ B δ ⊆ A.U)
    (hCollars : ∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v)
    (hPrincipal : ∀ C : SignedPoissonCollar G, ∀ χ ζ : E → ℂ,
      ∀ p ∈ movingSymbolPhysicalLocus Y ρ B, ∀ x ξ : E, ξ ≠ 0 →
        HasDerivAt (fun r => C.velocityPrincipalSymbol A χ ζ
          (movingSymbolSignedRadiusEquiv d (((movingSymbolSignedRadiusEquiv d).symm p).1,r),x) ξ) 0 0)
    (hOffFirst : ∀ χ η : Z → ℂ, smoothNear χ S → smoothNear η S →
      Disjoint (angularSupport χ) (angularSupport η) →
      ∃ K : P × Z → Z → ℂ, UniformGeometryAngularSmoothing univ (movingSymbolGeometryCompact Y ρ B) K ∧
        ∀ p ∈ movingSymbolGeometryCompact Y ρ B, ∀ u : Z → ℂ, smoothNear u S →
          ∀ w : ↥S, χ w * radiusFirstSphereOperator (dim := d) (movingSymbolSignedRadiusEquiv d)
            A.operator p (fun z => η z * u z) w =
              ∫ z : ↥S, K (p,w) z * u z ∂(sphereProbability d))
    (hOffTail : ∀ χ η : Z → ℂ, smoothNear χ S → smoothNear η S →
      Disjoint (angularSupport χ) (angularSupport η) →
      ∃ K : P × Z → Z → ℂ, UniformGeometryAngularSmoothing univ (movingSymbolPositiveLocus Y ρ B) K ∧
        ∀ p ∈ movingSymbolPositiveLocus Y ρ B, ∀ u : Z → ℂ, smoothNear u S →
          ∀ w : ↥S, χ w * radiusTaylorSphereOperator (dim := d) (movingSymbolSignedRadiusEquiv d)
            A.operator p (fun z => η z * u z) w =
              ∫ z : ↥S, K (p,w) z * u z ∂(sphereProbability d)) :
    UniformGeometryClassicalSphereOperator univ (movingSymbolPositiveLocus Y ρ B) 1
      (radiusTaylorSphereOperator (dim := d) (movingSymbolSignedRadiusEquiv d) A.operator) ∧
    GeometryClassicalSphereOperatorPrincipalZero univ (movingSymbolGeometryCompact Y ρ B)
      (movingSymbolPhysicalLocus Y ρ B) 1
      (radiusFirstSphereOperator (dim := d) (movingSymbolSignedRadiusEquiv d) A.operator) := by
  let J := movingSymbolGeometryCompact Y ρ B
  let Jpos := movingSymbolPositiveLocus Y ρ B
  let Z₀ := movingSymbolPhysicalLocus Y ρ B
  let L := movingSymbolSignedRadiusEquiv d
  have hChart (v : ↥S) (χ η : Z → ℂ) (hχ : smoothNear χ S) (hη : smoothNear η S)
      (hχS : angularSupport χ ⊆ (stereographic' (d-1) v).source)
      (hηS : angularSupport η ⊆ (stereographic' (d-1) v).source) :
      let κ := stereographic' (d-1) v
      ∃ aFirst aTail : P × E → E → ℂ,
        GeometryClassicalSymbolPrincipalZero univ J Z₀ 1 aFirst ∧
        UniformGeometryClassicalAngularSymbol univ Jpos 1 aTail ∧
        (∀ p ∈ J, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
          let f := fun ξ => η (κ.symm ξ) * u (κ.symm ξ)
          let i := fun ξ => angularFourierPhase (dim := d) x ξ * aFirst (p,x) ξ *
            angularFourierTransform (dim := d) f ξ
          Integrable f ∧ Integrable i ∧
            χ (κ.symm x) * radiusFirstSphereOperator (dim := n+1) L A.operator p (fun z => η z*u z) (κ.symm x) =
              ∫ ξ, i ξ) ∧
        (∀ p ∈ Jpos, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
          let f := fun ξ => η (κ.symm ξ) * u (κ.symm ξ)
          let i := fun ξ => angularFourierPhase (dim := d) x ξ * aTail (p,x) ξ *
            angularFourierTransform (dim := d) f ξ
          Integrable f ∧ Integrable i ∧
            χ (κ.symm x) * radiusTaylorSphereOperator (dim := n+1) L A.operator p (fun z => η z*u z) (κ.symm x) =
              ∫ ξ, i ξ) := by
    obtain ⟨C,hC⟩ := hCollars v
    subst v
    have hK := angularChartSupport_isCompact C.pole η hηS
    obtain ⟨ζ,hζ,hζK,hζOne,_⟩ := exists_localizingAngularBump hK
      (L := (∅ : Set E)) isClosed_empty (disjoint_empty _)
    let ζ' (x : E) := (ζ x : ℂ)
    have hζ' : ContDiff ℝ ∞ ζ' := Complex.ofRealCLM.contDiff.comp hζ
    have hζ₀ (x : E) (hx : x ∉ tsupport ζ) : ζ' x = 0 := by
      have h : ζ x = 0 := by
        by_contra hn
        exact hx (subset_tsupport _ hn)
      simp [ζ',h]
    have hOne : EqOn ζ' 1 (angularChartSupport C.pole η) := by
      intro x hx
      change (ζ x : ℂ) = 1
      simp only [hζOne hx, Pi.one_apply, Complex.ofReal_one]
    exact C.exists_radius_velocity_chart_models A hY hρ hδ hJA inter_subset_left hχ hη hχS hηS
      hζ' hζK hζ₀ hOne (hPrincipal C (χ ∘ angularPoint C.pole) ζ')
  refine ⟨⟨?_,hOffTail⟩,⟨?_,hOffFirst⟩⟩
  · intro v κ χ η hχ hη hχS hηS
    obtain ⟨_,aT,_,hT,_,hEq⟩ := hChart v χ η hχ hη hχS hηS
    exact ⟨aT,hT,fun p hp u hu x _ => hEq p hp u hu x⟩
  · intro v κ χ η hχ hη hχS hηS
    obtain ⟨aF,_,hF,_,hEq,_⟩ := hChart v χ η hχ hη hχS hηS
    exact ⟨aF,hF,fun p hp u hu x _ => hEq p hp u hu x⟩

end CalderonPaper
