module

public import Proof.CalderonN.MovingGreenFluxDensity
public import Proof.CalderonN.MovingGreenConormalComparison

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.ScaledGreenDatumJets
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

/-- The same framed density already has constant radial extension in
the released moving Green field. -/
theorem movingGreenFluxDensity_radial_frame
    {γ g : MetricField n} {E : X n × X n → X n} {e : Frame n} {r : X n → ℝ}
    {G : X n × X n → ℝ} {y z : X n} (hz : z ≠ 0)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    movingGreenFluxDensity γ g E e r G (y,frameVector e y z) =
      movingGreenFluxDensity γ g E e r G (y,frameVector e y (sphereNormalize z)) := by
  have hFrame (w : X n) : movingBallToFrame γ e (y,frameVector e y w) = (y,w) := by
    change movingBallToFrame γ e (movingBallFromFrame e (y,w)) = _
    exact movingBallToFrame_fromFrame he
  rw [movingGreenFluxDensity,movingGreenFluxDensity,hFrame,hFrame]
  simp only [parametricBallConormal,sphereNormalize_eq_of_sphere (sphereNormalize_mem_sphere hz)]

/-- A single global smooth test function may represent the germ of the
actual framed density at any one sphere point. -/
theorem exists_framedGreenDensity_germ
    {Y : Set (X n)} {γ : MetricField n} {e : Frame n} {ψ : X n × X n → ℝ}
    (hψ : smoothNear ψ (bundle Y γ)) (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    {y : X n} (hy : y ∈ Y)
    (hFrame : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {w : ↥(standardSphere n)} :
    ∃ H : X n × X n → ℝ, ContDiff ℝ ∞ H ∧
      H =ᶠ[𝓝 (y,(w : X n))] fun q => ψ (q.1,frameVector e q.1 q.2) := by
  obtain ⟨W,hW,hSub,hSmooth⟩ := hψ
  let a (q : X n × X n) := (q.1,frameVector e q.1 q.2)
  have ha : ContDiff ℝ ∞ a := contDiff_fst.prodMk (contDiff_family_frameVector
    (fun i => (he i).comp contDiff_fst) contDiff_snd)
  have hYw : a (y,w) ∈ W := hSub ⟨hy,frameVector_mem_sphere γ e y hFrame w⟩
  have hOpen : IsOpen (a ⁻¹' W) := hW.preimage ha.continuous
  have hComp : ContDiffOn ℝ ∞ (ψ ∘ a) (a ⁻¹' W) :=
    hSmooth.comp ha.contDiffOn (fun _ hz => hz)
  obtain ⟨H,hH,_,U,hU,hC,_,hEq⟩ := exists_contDiff_extension_near_compact hOpen
    (isCompact_singleton (x := (y,(w : X n)))) (singleton_subset_iff.mpr hYw) hComp
  refine ⟨H,hH,?_⟩
  filter_upwards [hU.mem_nhds (hC (mem_singleton _))] with q hq
  exact hEq hq

variable {X Q : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem framedJet_eq_of_germ {f g : X × Q → ℝ} {x : X} {w : Q}
    (he : f =ᶠ[𝓝 (x,w)] g) (k : ℕ) :
    iteratedFDeriv ℝ k (fun z => f (x,z)) w = iteratedFDeriv ℝ k (fun z => g (x,z)) w ∧
      iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun y => f (y,z)) x) w =
      iteratedFDeriv ℝ k (fun z => fderiv ℝ (fun y => g (y,z)) x) w := by
  have h₁ : (fun z => f (x,z)) =ᶠ[𝓝 w] (fun z => g (x,z)) :=
    he.comp_tendsto ((continuous_const.prodMk continuous_id).continuousAt.tendsto :
      Tendsto (fun z : Q => (x,z)) (𝓝 w) (𝓝 (x,w)))
  have h₂ : (fun z => fderiv ℝ (fun y => f (y,z)) x) =ᶠ[𝓝 w]
      (fun z => fderiv ℝ (fun y => g (y,z)) x) := by
    obtain ⟨A,hA,B,hB,hAB⟩ := mem_nhds_prod_iff.mp he
    filter_upwards [hB] with z hz
    have h : (fun y => f (y,z)) =ᶠ[𝓝 x] (fun y => g (y,z)) :=
      Filter.mem_of_superset hA (fun y hy => hAB ⟨hy,hz⟩)
    exact h.fderiv_eq
  exact ⟨(h₁.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds,(h₂.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds⟩

end CalderonPaper.LowerGreen

end
