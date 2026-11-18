import Proof.UniformActualH2Comparison
import Proof.DirichletRadialUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

lemma normalChart_radial_derivative (expMap : X × X → X) (e : Frame) (r u : X → ℝ)
    (y w : X) (hB : DifferentiableAt ℝ (ballPullback expMap r y u) (frameVector e y w)) :
    fderiv ℝ (u ∘ normalChart expMap e y (r y)) w w =
      radialTrace expMap r y (frameVector e y w) u := by
  have h := hB.hasFDerivAt.comp w ((frameVectorLinear e y).hasFDerivAt)
  have hEval := congrArg (fun L : X →L[ℝ] ℝ => L w) h.fderiv
  simpa only [Function.comp_def,frameVectorLinear_apply,ContinuousLinearMap.comp_apply,
    ballPullback,normalChart,radialTrace] using hEval

/-- The native smooth radial trace is the frozen physical response, expressed
    in the chosen orthonormal frame; no change of radial normalization occurs. -/
theorem Admissible.smooth_radial_representative_eq {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (u : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (U : SmoothData)
    (hNear : ∀ z ∈ Metric.closedBall (0:X) 1,
      U.1 =ᶠ[𝓝 z] (u ∘ normalChart d.expMap d.frame y (d.radius y)))
    (w : UnitSphere) :
    smoothRadialSphere U w = radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hwSphere := frameVector_mem_sphere d.γ d.frame y hFrame w
  obtain ⟨_,hExp,hU⟩ := dirichlet_differentiability Y Ω hY hd y _ hy hwSphere u hu
  have hScale := (hasFDerivAt_const (𝕜:=ℝ) y (frameVector d.frame y w.val)).prodMk
    ((hasFDerivAt_id (𝕜:=ℝ) (frameVector d.frame y w.val)).const_smul (d.radius y))
  have hB : DifferentiableAt ℝ (ballPullback d.expMap d.radius y u) (frameVector d.frame y w.val) :=
    (hU.hasFDerivAt.comp (frameVector d.frame y w.val)
      (hExp.hasFDerivAt.comp (frameVector d.frame y w.val) hScale)).differentiableAt
  have hClosed : w.val ∈ Metric.closedBall (0:X) 1 := by
    have hn : ‖w.val‖ = 1 := by simpa [UnitSphere,Metric.sphere,dist_eq_norm] using w.property
    simpa [Metric.mem_closedBall,dist_zero_right,hn]
  change fderiv ℝ U.1 w.val w.val = _
  exact (congrArg (fun L : X →L[ℝ] ℝ => L w.val) (hNear w.val hClosed).fderiv_eq).trans
    (normalChart_radial_derivative d.expMap d.frame d.radius u y w.val hB)

/-- The actual smooth radial response is exactly the native L2 trace of its
    H2 representative. -/
theorem Admissible.outwardRadialTrace_representative_ae {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (u : X → ℝ) (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u)
    (U : SmoothData)
    (hNear : ∀ z ∈ Metric.closedBall (0:X) 1,
      U.1 =ᶠ[𝓝 z] (u ∘ normalChart d.expMap d.frame y (d.radius y))) :
    outwardRadialTraceL fixedSobolevCalculus fixedUnitBallValueTrace (smoothBallSobolev 2 U)
      =ᵐ[sphereProbability] fun w : UnitSphere =>
        radialTrace d.expMap d.radius y (frameVector d.frame y w.val) u := by
  rw [outwardRadialTraceL_smoothBallSobolev]
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (μ:=sphereProbability) (𝕜:=ℝ)
    (smoothRadialSphere U)] with w hw
  exact hw.trans (hd.smooth_radial_representative_eq hY hy u hu U hNear w)

end ShrinkingSpheres
