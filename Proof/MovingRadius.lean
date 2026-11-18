import Proof.MovingTrace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set
namespace ShrinkingSpheres

/-- Pullback of a fixed physical function to the closed unit tangent ball. -/
def ballPullback (expMap : X × X → X) (r : X → ℝ) (y : X) (u : X → ℝ) : X → ℝ :=
  fun z => u (expMap (y,r y • z))

/-- Boundary radial derivative of the rescaled Dirichlet solution. -/
def radialTrace (expMap : X × X → X) (r : X → ℝ) (y w : X) (u : X → ℝ) : ℝ :=
  fderiv ℝ (ballPullback expMap r y u) w w

/-- The logarithmic derivative identity used in the supplied MovingRadiusChainRule proof,
    localized to the center where the radius is differentiable and positive. -/
theorem logRadius_derivative (r : X → ℝ) (y a : X)
    (hr : DifferentiableAt ℝ r y) (hpos : r y ≠ 0) :
    fderiv ℝ (fun x => Real.log (r x)) y a = (r y)⁻¹ * fderiv ℝ r y a := by
  rw [(hr.hasFDerivAt.log hpos).fderiv]
  rfl

theorem radialTrace_eq (expMap : X × X → X) (r u : X → ℝ) (y w : X)
    (he : DifferentiableAt ℝ expMap (y,r y • w))
    (hu : DifferentiableAt ℝ u (endpoint expMap r (y,w))) :
    radialTrace expMap r y w u =
      fderiv ℝ u (endpoint expMap r (y,w))
        (fderiv ℝ expMap (y,r y • w) (0,r y • w)) := by
  have hscale := (hasFDerivAt_const (𝕜 := ℝ) y w).prodMk ((hasFDerivAt_id (𝕜 := ℝ) w).const_smul (r y))
  have h := hu.hasFDerivAt.comp w (he.hasFDerivAt.comp w hscale)
  exact congrArg (fun L : X →L[ℝ] ℝ => L w) h.fderiv

/-- The center action at a fixed radius plus the logarithmic-radius coefficient times the
    radial boundary derivative. All quantities concern the same physical function. -/
theorem horizontal_endpoint_split (γ : MetricField) (expMap : X × X → X) (r u : X → ℝ)
    (y w a : X) (hr : DifferentiableAt ℝ r y) (hr0 : r y ≠ 0)
    (he : DifferentiableAt ℝ expMap (y,r y • w))
    (hu : DifferentiableAt ℝ u (endpoint expMap r (y,w))) :
    horizontal γ (fun p => u (endpoint expMap r p)) y w a =
      horizontal γ (fun p => u (endpoint expMap (fun _ => r y) p)) y w a +
        fderiv ℝ (fun x => Real.log (r x)) y a * radialTrace expMap r y w u := by
  rw [horizontal_endpoint γ expMap r u y w a hr he hu,
    horizontal_endpoint γ expMap (fun _ => r y) u y w a (differentiableAt_const _) he hu,
    logRadius_derivative r y a hr hr0, radialTrace_eq expMap r u y w he hu]
  have hv : (a,r y • (-connection γ y a w) + (fderiv ℝ r y a) • w) =
      (a,r y • (-connection γ y a w)) +
        ((r y)⁻¹ * fderiv ℝ r y a) • ((0:X),r y • w) := by
    simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, smul_smul]
    congr 2
    congr 1
    field_simp
  rw [hv, map_add, map_add, map_smul, map_smul]
  simp [endpoint, smul_eq_mul]

/-- The moving boundary formula for an arbitrary radius satisfying the frozen hypotheses. -/
theorem horizontal_dirichlet_trace_split (Y Ω : Set X) (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (y w a : X) (hy : y ∈ Y)
    (hw : w ∈ sphereAt d.γ y) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y w a =
      horizontal d.γ (fun p => u (endpoint d.expMap (fun _ => d.radius y) p)) y w a +
        fderiv ℝ (fun x => Real.log (d.radius x)) y a * radialTrace d.expMap d.radius y w u := by
  obtain ⟨hr,he,hu⟩ := dirichlet_differentiability Y Ω hY hd y w hy hw u hu
  exact horizontal_endpoint_split _ _ _ _ _ _ _ hr ((hd.2.2.2.2.1.2 y hy).1.ne') he hu

end ShrinkingSpheres
