import Proof.PhysicalStrongPoissonRealization
import Proof.BoundaryGradientRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Coordinate traces of a genuine smooth representative are the coordinate
    derivatives of its actual physical pullback, with the same normalization. -/
theorem strongCoordinateTrace_representative_ae (U : SmoothData) (f : X → ℝ)
    (hNear : ∀ z ∈ Metric.closedBall (0:X) 1,U.1 =ᶠ[𝓝 z] f) (j : I) :
    strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j (smoothBallSobolev 2 U)
      =ᵐ[sphereProbability] fun w : UnitSphere => fderiv ℝ f w.val (axis j) := by
  rw [strongCoordinateTraceL_smooth]
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ)
    (smoothSphereValue (smoothCoordinateDerivative U j))] with w hw
  have hClosed : w.val ∈ Metric.closedBall (0:X) 1 := by
    have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
    simpa [Metric.mem_closedBall,dist_zero_right,hn]
  exact hw.trans (congrArg (fun L : X →L[ℝ] ℝ => L (axis j)) (hNear w.val hClosed).fderiv_eq)

/-- The completed physical harmonic Dirichlet solution has exactly its genuine
    coordinate gradient on the boundary, uniformly over the admitted class. -/
theorem uniform_physical_coordinate_trace {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 3 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ F : SmoothCoefficientMatrix 2,
      (∀ x ∈ Metric.closedBall (0:X) 2,∀ i j,coefficientValue 2 (F i j) =ᶠ[𝓝 x]
        (fun z => principalCoefficient (framedNormalMetric d.g₁ d.frame d.expMap y (d.radius y)) z i j)) →
      (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible →
      ∀ u : X → ℝ,HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u →
      ∀ f : SphereSobolev (3/2:ℝ),
      (fixedBoundaryValueL f =ᵐ[sphereProbability] fun w : UnitSphere =>
        u (normalChart d.expMap d.frame y (d.radius y) w.val)) → ∀ j,
      strongCoordinateTraceL fixedSobolevCalculus fixedUnitBallValueTrace j (strongPoissonL F f)
        =ᵐ[sphereProbability] fun w : UnitSphere =>
          fderiv ℝ (u ∘ normalChart d.expMap d.frame y (d.radius y)) w.val (axis j) := by
  obtain ⟨η,hη,hPhysical⟩ := uniform_physical_strong_poisson_realization (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy F hRep hInv u hu f hBoundary j
  have hHere := hPhysical floor hf ε hε hSmall d hd y hy F hRep hInv u hu f hBoundary
  obtain ⟨U,hCompact,hNear,hIdent⟩ := hHere
  rw [← hIdent]
  exact strongCoordinateTrace_representative_ae U _ hNear j

end ShrinkingSpheres
