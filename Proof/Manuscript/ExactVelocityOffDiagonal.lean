module

public import Proof.Manuscript.VelocityRapidOffDiagonal
import Proof.Manuscript.MovingTrace.QuantizedVelocityChart
public import Proof.Manuscript.MovingTrace.MovingAdjointOperatorAssembly
public import Proof.Manuscript.SphereKernelRadiusTaylor

public section

noncomputable section

open Set Metric MeasureTheory CalderonN
open scoped ContDiff

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "E" => X n

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

local instance : Fact (Module.finrank ℝ Z = (n+1)-1+1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

/-- The exact collar quantization supplies all compact-local witnesses of
the literal velocity symbol. -/
theorem hasCompactVelocityRapidChart_of_signedPoissonCollar
    {G : BallPoissonTube P (n+1)} (A : SmoothRadialVelocity G) :
    HasCompactVelocityRapidChart A := by
  intro C χ η hχ hη hχS hηS ζ hζ Kζ hKζ hζ₀ hOne J hJ hJU
  obtain ⟨U,s,hU,hJU',hUA,H,hQuant,hExact,_,hCoeff,_,_⟩ :=
    C.exists_quantized_velocity_chart_symbol A hJ hJU hχ hη hχS hηS hζ hKζ hζ₀ hOne
  exact ⟨⟨U,s,hU,hJU',hUA,H,hExact,
    fun p hp u hu x => (hQuant p hp u hu x).2.2,hCoeff⟩⟩

/-- The actual normalized radial velocity adjoints have a
smooth sphere kernel for every disjoint pair of angular cutoffs. -/
theorem exists_exact_radialVelocity_offDiagonal_kernel
    (hn : 2 ≤ n+1) {G : BallPoissonTube P (n+1)} (A : SmoothRadialVelocity G)
    (hCollars : ∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v)
    (χ η : Z → ℂ) (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hDis : Disjoint (angularSupport χ) (angularSupport η)) :
    ∃ F : P × (Z × Z) → ℂ,
      ContDiffOn ℝ ∞ F (A.U ×ˢ univ) ∧
      ∀ p ∈ A.U, ∀ u : Z → ℂ, smoothNear u S → ∀ w : ↥S,
        χ w * A.operator p (fun z => η z*u z) w =
          ∫ z : ↥S, F (p,(w,z)) * u z ∂sphereProbability (n+1) :=
  exists_radialVelocity_offDiagonal_kernel hn A hCollars
    (hasCompactVelocityRapidChart_of_signedPoissonCollar A) χ η hχ hη hDis

local notation "GParam" => MovingSymbolGeometry (n+1)

/-- The exact first and remainder operators have their off-diagonal
kernels uniformly on the compact physical geometry, with the remainder
identity evaluated at positive radii. -/
theorem exact_radialVelocity_offDiagonal_radius_pair
    (hn : 2 ≤ n+1) {G : BallPoissonTube GParam (n+1)} (A : SmoothRadialVelocity G)
    (hCollars : ∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v)
    {Y : Set Z} {ρ B : ℝ} (hY : IsCompact (closure Y))
    (hJU : movingSymbolGeometryCompact Y ρ B ⊆ A.U) :
    (∀ χ η : Z → ℂ, smoothNear χ S → smoothNear η S →
      Disjoint (angularSupport χ) (angularSupport η) →
      ∃ K : GParam × Z → Z → ℂ,
        UniformGeometryAngularSmoothing univ (movingSymbolGeometryCompact Y ρ B) K ∧
        ∀ p ∈ movingSymbolGeometryCompact Y ρ B, ∀ u : Z → ℂ, smoothNear u S →
          ∀ w : ↥S, χ w * radiusFirstSphereOperator (movingSymbolSignedRadiusEquiv (n+1))
            A.operator p (fun z => η z * u z) w =
              ∫ z : ↥S, K (p,w) z * u z ∂sphereProbability (n+1)) ∧
    (∀ χ η : Z → ℂ, smoothNear χ S → smoothNear η S →
      Disjoint (angularSupport χ) (angularSupport η) →
      ∃ K : GParam × Z → Z → ℂ,
        UniformGeometryAngularSmoothing univ (movingSymbolPositiveLocus Y ρ B) K ∧
        ∀ p ∈ movingSymbolPositiveLocus Y ρ B, ∀ u : Z → ℂ, smoothNear u S →
          ∀ w : ↥S, χ w * radiusTaylorSphereOperator (movingSymbolSignedRadiusEquiv (n+1))
            A.operator p (fun z => η z * u z) w =
              ∫ z : ↥S, K (p,w) z * u z ∂sphereProbability (n+1)) := by
  let L := movingSymbolSignedRadiusEquiv (n+1)
  let J := movingSymbolGeometryCompact Y ρ B
  have hJ : IsCompact J := isCompact_movingSymbolGeometryCompact hY ρ B
  have hJSeg : J ⊆ sphereRadiusSegment L A.U :=
    movingSymbolGeometryCompact_subset_sphereRadiusSegment hJU
  have hPair (χ η : Z → ℂ) (hχ : smoothNear χ S) (hη : smoothNear η S)
      (hDis : Disjoint (angularSupport χ) (angularSupport η)) :
      ∃ K₀ K₁ : GParam × Z → Z → ℂ,
        UniformGeometryAngularSmoothing univ J K₀ ∧ UniformGeometryAngularSmoothing univ J K₁ ∧
        ∀ p ∈ J, ∀ u : Z → ℂ, smoothNear u S → ∀ w : ↥S,
          (χ w * radiusFirstSphereOperator L A.operator p (fun z => η z * u z) w =
            ∫ z : ↥S, K₀ (p,w) z * u z ∂sphereProbability (n+1)) ∧
          ((L.symm p).2 ≠ 0 →
            χ w * radiusTaylorSphereOperator L A.operator p (fun z => η z * u z) w =
              ∫ z : ↥S, K₁ (p,w) z * u z ∂sphereProbability (n+1)) := by
    obtain ⟨F,hF,hFE⟩ := exists_exact_radialVelocity_offDiagonal_kernel hn A hCollars χ η hχ hη hDis
    exact exists_global_offDiagonal_radiusTaylor_kernel L A.openU hJ hJSeg hF hFE
  constructor
  · intro χ η hχ hη hDis
    obtain ⟨K₀,_,hK₀,_,hE⟩ := hPair χ η hχ hη hDis
    exact ⟨K₀,hK₀,fun p hp u hu w => (hE p hp u hu w).1⟩
  · intro χ η hχ hη hDis
    obtain ⟨_,K₁,_,hK₁,hE⟩ := hPair χ η hχ hη hDis
    refine ⟨K₁,hK₁.restrict_geometry inter_subset_left,fun p hp u hu w => ?_⟩
    exact (hE p hp.1 u hu w).2 (show p.1.2.2 ≠ 0 from hp.2.ne')

end CalderonPaper
