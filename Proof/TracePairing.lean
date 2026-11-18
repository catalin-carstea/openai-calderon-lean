import Proof.MovingRadius
import Proof.MetricAlgebra

noncomputable section
open Set MeasureTheory
namespace ShrinkingSpheres

/-- The adjoint trace pairing splits into its fixed-radius center action and the radial
    Dirichlet action, with the actual logarithmic derivative of the chosen radius. -/
theorem adjoint_pairing_split (Y Ω : Set X) (hY : IsOpen Y) (hinc : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (i : I) (v : Field)
    (hv : smoothNear v (bundle Y d.γ)) (y : X) (hy : y ∈ Y) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    sphereAverage d.frame y (fun w => adjointField d.adjoint i v (y,w) *
      (u (endpoint d.expMap d.radius (y,w)) : ℂ)) =
    sphereAverage d.frame y (fun w => v (y,w) *
      ((horizontal d.γ (fun p => u (endpoint d.expMap (fun _ => d.radius y) p)) y w (axis i) +
        coordDeriv i (fun x => Real.log (d.radius x)) y * radialTrace d.expMap d.radius y w u : ℝ) : ℂ)) := by
  have hAdj := hd.2.2.2.1 i v hv
  rw [hAdj.2 y hy u hu]
  unfold sphereAverage
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  rcases hd.1 with ⟨_,_,_,_,_,_,_,hframe⟩
  have hz := frameVector_mem_sphere d.γ d.frame y (hframe y (hinc hy)) z
  change v (y,frameVector d.frame y z) *
      (horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y (frameVector d.frame y z) (axis i) : ℝ) = _
  rw [horizontal_dirichlet_trace_split Y Ω hY hd y _ (axis i) hy hz u hu]
  rfl

end ShrinkingSpheres
