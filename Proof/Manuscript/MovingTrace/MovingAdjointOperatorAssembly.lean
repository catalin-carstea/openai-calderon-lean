module

public import Proof.Manuscript.MovingTrace.AdmittedProfileAdjointAssembly
public import Proof.Manuscript.GeometryClassicalPrincipalRestriction
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric
open scoped ContDiff

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "d" => n+1
local notation "Z" => X (n+1)
local notation "P" => MovingSymbolGeometry (n+1)
local notation "S" => standardSphere (n+1)

/-- The precise geometric locus where principal-order cancellation is
needed for the pullback. The physical radius remains independent here. -/
def movingSymbolPhysicalLocus (Y : Set Z) (ρ B : ℝ) : Set P :=
  movingSymbolGeometryCompact Y ρ B ∩ {p | p.1.2.1 ∈ Y}

/-- The quadratic difference quotient is used only at positive physical
radii. Its smooth angular bounds extend to the radius-zero closure. -/
def movingSymbolPositiveLocus (Y : Set Z) (ρ B : ℝ) : Set P :=
  movingSymbolGeometryCompact Y ρ B ∩ {p | 0 < p.1.2.2}

/-- Restrict the two Taylor operator families to the admitted radius
profiles, preserving exact quantization and the physical trace formula. -/
theorem movingAdjoint_expansion_of_raw_radius_models
    [Fact (Module.finrank ℝ Z = d-1+1)]
    {Y Ω : Set Z} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g₁ g₂ : ℝ → MetricField d}
    (hγ : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (γ lam))
    (hg₁ : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (g₁ lam))
    {e : ℝ → Frame d} (he : ∀ j, ContDiff ℝ ∞ (fun q : ℝ × Z => e q.1 q.2 j))
    {E : ℝ → Z × Z → Z} (hE : ContDiff ℝ ∞ (fun q : ℝ × (Z × Z) => E q.1 q.2))
    {K : ℝ} (hK : 0 < K) {m : ℕ} {M : Fin (m+1) → ℝ}
    (hbg : ∀ lam ∈ Icc (0:ℝ) 1, Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (e lam))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hN : ∀ lam ∈ Icc (0:ℝ) 1, NormalCoordinates (closure Y) Ω (γ lam) (E lam) (fun _ => ρ))
    {B δ : ℝ} (hδ : 0 < δ) {U : Set P} (hJU : signedGeometryCompact Y ρ B δ ⊆ U)
    {G : BallPoissonTube P d} (A : I d → SmoothRadialVelocity G) (hAU : ∀ i, (A i).U = U)
    (hG : G.g = radializedNormalFamily (fun p => symmetrizedNormalMetric g₁ E e (p.1.1,p.2)))
    (hW : ∀ i q, (A i).weight q = sphereGaussWeight (fun z => G.g (q.1,z)) 1 q.2)
    (hV : ∀ i (q : P × Z), q.1.1.1 ∈ Icc 0 1 → q.1.1.2.1 ∈ closure Y →
      (A i).velocity q = physicalSignedVelocity γ E e i q)
    {O : Set P} (hO : IsOpen O) (hJO : movingSymbolGeometryCompact Y ρ B ⊆ O)
    (hTaylor : ∀ i : I d, UniformGeometryClassicalSphereOperator O (movingSymbolPositiveLocus Y ρ B) 1
      (radiusTaylorSphereOperator (movingSymbolSignedRadiusEquiv d) (A i).operator))
    (hFirst : ∀ i : I d, GeometryClassicalSphereOperatorPrincipalZero O (movingSymbolGeometryCompact Y ρ B)
      (movingSymbolPhysicalLocus Y ρ B) 1
      (radiusFirstSphereOperator (movingSymbolSignedRadiusEquiv d) (A i).operator))
    {floor c₀ ε : ℝ} {Cj : Fin 9 → ℝ} {D : ℝ} (hD : 1 ≤ D)
    (hβ : ∀ t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj, ∀ y ∈ Y, 1 ≤ movingTraceRadiusBeta t y)
    (hGeom : ∀ i : I d,
      (∀ t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj, ContDiff ℝ ∞ (movingTraceRadiusGeometry i t)) ∧
      (∀ t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj,
        MapsTo (movingTraceRadiusGeometry i t) Y (movingSymbolGeometryCompact Y ρ B)) ∧
      ∀ (t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj) y, y ∈ Y → ∀ j ≤ 6,
        ‖iteratedFDeriv ℝ j (movingTraceRadiusGeometry i t) y‖ ≤ D*(movingTraceRadiusBeta t y)^j) :
    let R := MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj
    ∃ (E₁ F₀ : I d → R → Z → SphereOperator d),
      (∀ i, UniformClassicalSphereOperator Y movingTraceRadiusBeta 1 (E₁ i) ∧
        UniformClassicalSphereOperator Y movingTraceRadiusBeta 0 (F₀ i)) ∧
      ∀ t : R,
        let lam := t.1.val
        let r := t.2.val
        ∀ i, ∀ y ∈ Y, ∀ φ : Z → ℂ, smoothNear φ S → ∀ w : ↥S,
          let a := (movingBallToFrame (γ lam) (e lam) (y,axis i)).2
          let fᵢ := coordDeriv i (fun z => Real.log (r z)) y
          actualMovingTraceAdjoint (γ lam) (g₁ lam) (E lam) (e lam) r i y
            (fun z => φ (movingBallToFrame (γ lam) (e lam) (y,z)).2) (frameVector (e lam) y w) =
            ((r y)⁻¹ : ℂ) * flatAngularVelocityAdjoint (fun _ => a) φ w +
            (fᵢ : ℂ) * flatAngularVelocityAdjoint id φ w +
            (r y : ℂ) * E₁ i t y φ w + F₀ i t y φ w := by
  let L := movingSymbolSignedRadiusEquiv d
  refine ⟨fun i t y => radiusTaylorSphereOperator L (A i).operator (movingTraceRadiusGeometry i t y),
    fun i t y => radiusFirstSphereOperator L (A i).operator (movingTraceRadiusGeometry i t y),?_,?_⟩
  · intro i
    obtain ⟨hs,hMap,hBounds⟩ := hGeom i
    have hZ (t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj) :
        MapsTo (movingTraceRadiusGeometry i t) Y (movingSymbolPhysicalLocus Y ρ B) :=
      fun y hy => ⟨hMap t hy,hy⟩
    have hPos (t : MovingTraceRadii Y γ g₂ e ρ floor c₀ ε Cj) :
        MapsTo (movingTraceRadiusGeometry i t) Y (movingSymbolPositiveLocus Y ρ B) :=
      fun y hy => ⟨hMap t hy,(t.2.property.2.1.2 y hy).1⟩
    exact ⟨(hTaylor i).pullback hO (inter_subset_left.trans hJO) hs hPos hβ hD hBounds,
      (hFirst i).pullback hY hO hJO hs hMap hZ hβ hD hBounds⟩
  · exact actualMovingTraceAdjoint_admitted_expansion hY hΩ hγ hg₁ he hE hK hbg hρ hN hδ hJU
      A hAU hG hW hV (fun i => (hGeom i).2.1)

end CalderonPaper
