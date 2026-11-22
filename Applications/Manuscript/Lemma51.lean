module

public import Proof.Manuscript.Lemma51

public section

open CalderonN MeasureTheory Metric Set
open scoped ContDiff

namespace CalderonPaper

/-- Apply the equation to the conormal density of a single continued Green kernel. -/
theorem lemma51_green_trace_equation {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
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
    (Cj : Fin 9 → ℝ) 
    {lam : ℝ} (hLam : lam ∈ Icc (0 : ℝ) 1)
    {r : X dim → ℝ} (hr : AdmittedTraceRadius Y (γ lam) (g₂ lam) (e lam) ρ floor c₀ ε Cj r)
    {O : Set (X dim × X dim)} {G : X dim × X dim → ℝ}
    (hO : IsOpen O) (hG : ProductSolutionOn (g₁ lam) (g₂ lam) O G)
    (hSphere : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      (E lam (y, r y • frameVector (e lam) y w), y) ∈ O) :
    let ψ := movingGreenFluxDensity (γ lam) (g₁ lam) (E lam) (e lam) r G
    ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      movingTrace (γ lam) (g₂ lam) r (actualMovingTraceAdjoint (γ lam) (g₁ lam) (E lam) (e lam) r)
        (fun q => (ψ q : ℂ)) (y, frameVector (e lam) y w) = 0 := by
  obtain ⟨_, _, _, _, h⟩ := lemma51 hn hY hΩ hComp hSub hγ hg₁ hg₂ hΓ hG₁ hG₂
    he hK hbg hE hρ hNormal hFloor hc₀ hε Cj
  exact (h ⟨⟨lam, hLam⟩, ⟨r, hr⟩⟩).2.2.2.2 O G hO hG hSphere

end CalderonPaper
