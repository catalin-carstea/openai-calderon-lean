import Proof.Geometry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Ring

noncomputable section
open Set
namespace ShrinkingSpheres

/-- Horizontal derivative of a fixed physical function on the moving sphere, before
    replacing its radial component with the first-metric Dirichlet normal derivative. -/
theorem horizontal_endpoint (γ : MetricField) (expMap : X × X → X) (r u : X → ℝ)
    (y w a : X) (hr : DifferentiableAt ℝ r y)
    (he : DifferentiableAt ℝ expMap (y, r y • w))
    (hu : DifferentiableAt ℝ u (endpoint expMap r (y,w))) :
    horizontal γ (fun p => u (endpoint expMap r p)) y w a =
      fderiv ℝ u (endpoint expMap r (y,w))
        (fderiv ℝ expMap (y,r y • w)
          (a, r y • (-connection γ y a w) + (fderiv ℝ r y a) • w)) := by
  have h₁ := hasFDerivAt_fst (𝕜 := ℝ) (p := (y,w))
  have h₂ := hasFDerivAt_snd (𝕜 := ℝ) (p := (y,w))
  have hscaled := (hr.hasFDerivAt.comp (y,w) h₁).smul h₂
  have htrace := hu.hasFDerivAt.comp (y,w) (he.hasFDerivAt.comp (y,w) (h₁.prodMk hscaled))
  exact congrArg (fun L : X × X →L[ℝ] ℝ => L (a, -connection γ y a w)) htrace.fderiv

theorem scaled_unit_mem_disk (γ : MetricField) (y w : X) (s : ℝ)
    (hw : w ∈ sphereAt γ y) : s • w ∈ disk γ y s := by
  change metricPair γ y (s • w) (s • w) ≤ s^2
  change metricPair γ y w w = 1 at hw
  have scale : metricPair γ y (s • w) (s • w) = s^2 * metricPair γ y w w := by
    simp only [metricPair, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [scale, hw, mul_one]

/-- On an admissible normal ball all differentiability premises of the endpoint identity follow
    from geometry and smoothness of the chosen Dirichlet solution up to the boundary. -/
theorem dirichlet_differentiability (Y Ω : Set X) (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (y w : X) (hy : y ∈ Y)
    (hw : w ∈ sphereAt d.γ y) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    DifferentiableAt ℝ d.radius y ∧
    DifferentiableAt ℝ d.expMap (y,d.radius y • w) ∧
    DifferentiableAt ℝ u (endpoint d.expMap d.radius (y,w)) := by
  rcases hd with ⟨_, hn, _, _, hp, _⟩
  have hrad := (hp.2 y hy).1
  have hwd := scaled_unit_mem_disk d.γ y w (d.radius y) hw
  have ht : d.radius y • w ∈ disk d.γ y (max ρ (d.radius y)) :=
    hwd.trans ((sq_le_sq₀ hrad.le (hrad.le.trans (le_max_right ..))).2 (le_max_right ..))
  obtain ⟨U, hU, hsub, hsm⟩ := hn.1
  have hpnt := hsub (show (y, d.radius y • w) ∈
    {p : X × X | p.1 ∈ Y ∧ p.2 ∈ disk d.γ p.1 (max ρ (d.radius p.1))} from ⟨hy, ht⟩)
  obtain ⟨V, hV, hball, hreg⟩ := hu.1
  have hv : endpoint d.expMap d.radius (y,w) ∈ V :=
    hball ⟨d.radius y • w, hwd, rfl⟩
  exact ⟨((hp.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)),
    ((hsm.contDiffAt (hU.mem_nhds hpnt)).differentiableAt (by simp)),
    ((hreg.contDiffAt (hV.mem_nhds hv)).differentiableAt (by simp))⟩

/-- On an admissible normal ball all differentiability premises of the endpoint identity follow
    from geometry and smoothness of the chosen Dirichlet solution up to the boundary. -/
theorem horizontal_dirichlet_trace (Y Ω : Set X) (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (y w a : X) (hy : y ∈ Y)
    (hw : w ∈ sphereAt d.γ y) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y w a =
      fderiv ℝ u (endpoint d.expMap d.radius (y,w))
        (fderiv ℝ d.expMap (y,d.radius y • w)
          (a, d.radius y • (-connection d.γ y a w) + (fderiv ℝ d.radius y a) • w)) := by
  obtain ⟨hr,he,hu⟩ := dirichlet_differentiability Y Ω hY hd y w hy hw u hu
  exact horizontal_endpoint _ _ _ _ _ _ _ hr he hu

end ShrinkingSpheres
