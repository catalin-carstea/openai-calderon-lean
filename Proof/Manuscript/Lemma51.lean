module

public import Proof.Manuscript.MovingTraceSymbols

import Proof.Manuscript.MovingTraceStatementAssembly
import Proof.Manuscript.PhysicalVelocityPrincipalLocus
import Proof.Manuscript.MovingTraceRadiusClassAssembly
import Proof.Manuscript.ExactVelocityOffDiagonal

public section

set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

open CalderonN MeasureTheory Metric Set
open scoped ContDiff

namespace CalderonPaper

/-- Lemma 5.1 of the pinned manuscript, with the principal angular terms,
the uniform classical symbol estimates, and the equation for the actual
Green transfer density on the moving spheres. The compact parameter
interval models the fixed family of small spatial dilations. -/
theorem lemma51 {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
    [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hComp : IsCompact (closure Y)) (hSub : closure Y ⊆ Ω)
    {γ g₁ g₂ : ℝ → MetricField dim}
    (hγ : ∀ lam ∈ Icc (0 : ℝ) 1, SmoothMetric univ (γ lam))
    (hg₁ : ∀ lam ∈ Icc (0 : ℝ) 1, SmoothMetric univ (g₁ lam))
    (hg₂ : ∀ lam ∈ Icc (0 : ℝ) 1, SmoothMetric univ (g₂ lam))
    (hΓ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => γ q.1 q.2 i j))
    (hG₁ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => g₁ q.1 q.2 i j))
    (hG₂ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => g₂ q.1 q.2 i j))
    {e : ℝ → Frame dim} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X dim => e q.1 q.2 i))
    {K : ℝ} (hK : 0 < K)
    {m : ℕ} {M : Fin (m + 1) → ℝ}
    (hbg : ∀ lam ∈ Icc (0 : ℝ) 1, Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (e lam))
    {E : ℝ → X dim × X dim → X dim} (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hNormal : ∀ lam ∈ Icc (0 : ℝ) 1, NormalCoordinates (closure Y) Ω (γ lam) (E lam) (fun _ => ρ))
    {floor c₀ ε : ℝ} (hFloor : 1 ≤ floor) (hc₀ : 0 < c₀) (hε : 0 ≤ ε)
    (Cj : Fin 9 → ℝ) :
    let Radii := Σ lam : ↥(Icc (0 : ℝ) 1),
      {r : X dim → ℝ // AdmittedTraceRadius Y (γ lam) (g₂ lam) (e lam) ρ floor c₀ ε Cj r}
    let β (r : Radii) := beta (γ r.1) r.2.val
    let A (r : Radii) := actualMovingTraceAdjoint (γ r.1) (g₁ r.1) (E r.1) (e r.1) r.2.val
    ∃ (C : Radii → TraceAdjoint dim)
      (E₁ F₀ : I dim → Radii → X dim → SphereOperator dim),
      (∀ i, UniformClassicalSphereOperator Y β 1 (E₁ i) ∧
        UniformClassicalSphereOperator Y β 0 (F₀ i)) ∧
      ∀ r : Radii,
        let lam := r.1.val
        let γ' := γ lam
        let g₁' := g₁ lam
        let g₂' := g₂ lam
        let e' := e lam
        let E' := E lam
        let radius := r.2.val
        IsMovingTraceAdjoint Y γ' g₁' e' E' radius (A r) ∧
        (∀ y ∈ Y, ∀ i, |drift γ' g₂' y i| ≤ K) ∧
        (∀ y ∈ Y, ∀ u, HarmonicOnBall g₁' (closedBallImage γ' E' radius y) u →
          ∀ i, ∀ w ∈ sphereAt γ' y,
            let U := fun q => u (endpoint E' radius q)
            C r i y (fun v => (U (y,v) : ℂ)) w =
              ((show ℝ from horizontal γ' U y w (axis i)) : ℂ)) ∧
        (∀ i, ∀ y ∈ Y, ∀ φ : X dim → ℂ, smoothNear φ (standardSphere dim) →
          ∀ w : ↥(standardSphere dim),
            let a := (movingBallToFrame γ' e' (y, axis i)).2
            let fᵢ := coordDeriv i (fun z => Real.log (radius z)) y
            A r i y (fun z => φ (movingBallToFrame γ' e' (y,z)).2) (frameVector e' y w) =
              ((radius y)⁻¹ : ℂ) * flatAngularVelocityAdjoint (fun _ => a) φ w +
              (fᵢ : ℂ) * flatAngularVelocityAdjoint id φ w +
              (radius y : ℂ) * E₁ i r y φ w + F₀ i r y φ w) ∧
        ∀ (O : Set (X dim × X dim)) (G : X dim × X dim → ℝ),
          IsOpen O → ProductSolutionOn g₁' g₂' O G →
          (∀ y ∈ Y, ∀ w : ↥(standardSphere dim), (E' (y, radius y • frameVector e' y w), y) ∈ O) →
          let ψ := movingGreenFluxDensity γ' g₁' E' e' radius G
          ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
            movingTrace γ' g₂' radius (A r) (fun q => (ψ q : ℂ)) (y, frameVector e' y w) = 0 := by
  cases dim with
  | zero => omega
  | succ n =>
    let d := n+1
    obtain ⟨B,hB,D,hD,hβ,hGeom⟩ := exists_admittedTraceRadius_geometry_envelope
      (c₀ := c₀) hY hΩ hComp hSub hΓ hG₁ hK hbg hρ hFloor hε Cj
    have hFrame (lam : ℝ) (hlam : lam ∈ Icc (0:ℝ) 1) (y : X d) (hy : y ∈ closure Y)
        (j k : I d) : metricPair (γ lam) y (e lam y j) (e lam y k) = if j=k then 1 else 0 :=
      (hbg lam hlam).2.2.2.2.2.2.2 y (hSub hy) j k
    obtain ⟨G,A,U,δ,hU,hδ,hJU,hG,hCollars,hAU,hWeight,hVelocity⟩ :=
      exists_actual_radialVelocity_model hComp hρ hγ hg₁ hΓ hG₁ hE hNormal he hFrame B
    have hJA (i : I d) : signedGeometryCompact Y ρ B δ ⊆ (A i).U := by
      rw [hAU i]
      exact hJU
    have hJ (i : I d) : movingSymbolGeometryCompact Y ρ B ⊆ (A i).U :=
      (movingSymbolGeometryCompact_subset_signed hδ.le).trans (hJA i)
    let L := movingSymbolSignedRadiusEquiv d
    have hClasses (i : I d) :
        UniformGeometryClassicalSphereOperator (dim := n+1) univ (movingSymbolPositiveLocus Y ρ B) 1
          (radiusTaylorSphereOperator (dim := n+1) L (A i).operator) ∧
        GeometryClassicalSphereOperatorPrincipalZero (dim := n+1) univ (movingSymbolGeometryCompact Y ρ B)
          (movingSymbolPhysicalLocus Y ρ B) 1 (radiusFirstSphereOperator (dim := n+1) L (A i).operator) := by
      obtain ⟨hOffFirst,hOffTail⟩ := exact_radialVelocity_offDiagonal_radius_pair
        (by omega : 2 ≤ n+1) (A i) hCollars hComp (hJ i)
      have hPrincipal := velocityPrincipalSymbol_zero_on_physicalLocus hY hΩ hE hK hbg hρ hδ.le hNormal
        (A i) (hJA i) hG i (hVelocity i)
      exact movingTrace_radius_classes_of_exact_kernels (A i) hComp hρ hδ (hJA i) hCollars
        hPrincipal hOffFirst hOffTail
    have hOperator := movingAdjoint_expansion_of_raw_radius_models hY hΩ hγ hg₁ he hE hK hbg hρ hNormal
      hδ hJU A hAU hG hWeight hVelocity isOpen_univ (subset_univ _)
      (fun i => (hClasses i).1) (fun i => (hClasses i).2) hD hβ hGeom
    exact lemma51_of_adjoint_expansion hn hY hΩ hComp hSub hγ hg₁ hg₂ hΓ hG₁ hG₂ he hK hbg
      hE hρ hNormal hFloor hc₀ hε Cj hOperator

end CalderonPaper
