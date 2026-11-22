module

public import Proof.CalderonN.ConformalGreenDensity
public import Proof.CalderonN.ActualGreenTransfer

import Proof.CalderonN.FixedTube.DilatedGeometry
import Proof.CalderonN.SmoothMetricFrame
import Proof.CalderonN.ShrinkingRadiusParameter
import Mathlib.Tactic

/-! Adapted from `ConformalActualGreenTransfer` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}
open FixedTube MovingSphere

/-- The uniform estimate required of the continued kernel and its
specified conormal density, before any choice of either small parameter. -/
@[expose] def UniformActualCylinderGreenTraceBound (normal : I dim)
    (g₁ g₂ : (MetricField dim)) (W Y' : Set (X dim)) (G₁ G₂ : (X dim) × (X dim) → ℝ) (E : ℝ → (X dim) × (X dim) → (X dim))
    (p : ℕ) (ρ R ε tb : ℝ) : Prop :=
  let Y := interior (coordinateCylinder normal)
  let γ := conformalReference (depthScale normal 4) g₁
  let r := shrinkingRadius R p (conformalDepth normal 4)
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam →
    ∀ δ ∈ Ioc (0 : ℝ) 1, Small Y (γ lam) (dilatedMetric g₂ lam) (r δ) ε →
    ∃ (O : Set ((X dim) × (X dim))) (G : (X dim) × (X dim) → ℝ),
      let e (y : (X dim)) := smoothMetricFrame (γ lam y)
      let A := actualMovingTraceAdjoint (γ lam) (dilatedMetric g₁ lam) (E lam) e (r δ)
      let d := conformalSphereData normal g₁ g₂ E p R lam δ A
      let ψ := movingGreenFluxDensity (γ lam) (dilatedMetric g₁ lam) (E lam) e (r δ) G
      IsOpen O ∧ ProductSolutionOn d.g₁ d.g₂ O G ∧
      (∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        (endpoint d.expMap d.radius (y,frameVector d.frame y w),y) ∈ O) ∧
      EqOn G (dilatedInitialGreen W G₁ G₂ lam) (lowerNormalSeed normal (normalPairDomain Y' d.γ ρ d.expMap)) ∧
      traceNorm Y d (cutoffDensity (cylinderCutoff normal 4 tb) (complexDensity ψ)) ≤ B

set_option maxHeartbeats 1800000 in
theorem conformalCylinderGreenFluxDensity_of_actualTraceBound
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {W Y' : Set (X dim)} {G₁ G₂ : (X dim) × (X dim) → ℝ} {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {p : ℕ} {ρ R ε tb : ℝ}
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates (interior (coordinateCylinder normal))
      (ball (0 : (X dim)) 3) (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hR : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ interior (coordinateCylinder normal),
      0 < shrinkingRadius R p (conformalDepth normal 4) δ y ∧
      shrinkingRadius R p (conformalDepth normal 4) δ y < ρ)
    (hBound : UniformActualCylinderGreenTraceBound normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb) :
    UniformCylinderGreenFluxDensity normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb := by
  obtain ⟨B,hB,h⟩ := hBound
  let Y := interior (coordinateCylinder normal)
  have hI : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨B,hB,?_⟩
  filter_upwards [h,hI] with lam hLam hIlam hp δ hδ hSmall
  obtain ⟨O,G,hO,hG,hSphere,hKnown,hNorm⟩ := hLam hp δ hδ hSmall
  let γ := conformalReference (depthScale normal 4) g₁ lam
  let g := dilatedMetric g₁ lam
  let k := dilatedMetric g₂ lam
  let e (y : (X dim)) := smoothMetricFrame (γ y)
  let r := shrinkingRadius R p (conformalDepth normal 4) δ
  let A := actualMovingTraceAdjoint γ g (E lam) e r
  let ψ := movingGreenFluxDensity γ g (E lam) e r G
  have hγ : SmoothMetric univ γ :=
    ⟨fun i j => (contDiff_depthScale (normal := normal) 4).contDiffOn.mul ((smoothMetric_dilatedMetric hg₁ lam).1 i j),
      fun y _ => (hg₁.2 (lam • y) (mem_univ _)).smul (depthScale_pos (normal := normal) 4 y)⟩
  have he (i : (I dim)) : ContDiff ℝ ∞ (fun y => e y i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame hγ.1 hγ.2 i)
  have hFrame (y : (X dim)) (_ : y ∈ Y) (i j : (I dim)) :
      metricPair γ y (e y i) (e y j) = if i=j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hγ.2 y (mem_univ _)) i j
  have hE' : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hr : ContDiff ℝ ∞ r := contDiff_shrinkingRadius (contDiff_conformalDepth (normal := normal) 4) R p δ
  obtain ⟨hDir,hAdj,hψ,hFlux,_⟩ := actualGreenTransfer (isOpen_interior : IsOpen Y)
    isOpen_ball hγ (smoothMetric_dilatedMetric hg₁ lam) (smoothMetric_dilatedMetric hg₂ lam)
    hE' (hNormal lam hIlam) he hFrame hr (hR δ hδ) hO hG hSphere
  refine ⟨O,G,A,ψ,hO,hG,hSphere,hKnown,hDir,hAdj,hψ,?_,hNorm⟩
  intro y hy u hu
  change (∫ w : ↥(standardSphere dim), (complexDensity ψ (y,frameVector e y w)).re *
    u (endpoint (E lam) r (y,frameVector e y w)) ∂(sphereProbability dim)) =
    normalSphereGreenFlux g (E lam) e r G y u
  simpa only [complexDensity,Complex.ofReal_re] using hFlux y hy u hu

end CalderonN
