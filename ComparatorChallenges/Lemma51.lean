module

public import ComparatorChallenges.Frozen.Manuscript.MovingTraceSymbols

public section

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
  sorry

end CalderonPaper
