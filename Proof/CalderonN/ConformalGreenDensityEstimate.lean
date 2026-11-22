module

public import Proof.CalderonN.ConformalGreenDensityJets
public import Proof.CalderonN.ConformalScaledGreenDataJets

import Proof.CalderonN.UniformMovingGreenDensity
import Proof.CalderonN.MovingTraceBackgroundBounds
import Proof.CalderonN.ProfileBounds
import Proof.CalderonN.SmoothMetricFrame
import Proof.CalderonN.ShrinkingRadiusParameter
import Mathlib.Tactic

/-! Adapted from `ConformalGreenDensityEstimate` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 3900000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- The uniform estimates for the normalized Dirichlet problem apply to
the conformal shrinking profile on the differential support of the cutoff. -/
theorem uniformCylinderGreenDensityJets_of_scaledData
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {W Y' Ω : Set (X dim)} {G₁ G₂ : (X dim) × (X dim) → ℝ} {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (hCY' : (coordinateCylinder normal) ⊆ Y')
    {p : ℕ} (hp : 1 ≤ p) {ρ R ε tb : ℝ}
    (hρ : 0 < ρ) (hR : 0 < R) (hε : 0 ≤ ε)
    (hNormal : ∀ lam ∈ Icc (-1 : ℝ) 1, NormalCoordinates Y' Ω
      (conformalReference (depthScale normal 4) g₁ lam) (E lam) (fun _ => ρ))
    (hRadius : ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ y ∈ interior (coordinateCylinder normal),
      shrinkingRadius R p (conformalDepth normal 4) δ y ≤ ρ/2)
    (hData : UniformCylinderScaledGreenDataJets normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb (2*dim+8)) :
    UniformCylinderGreenDensityJets normal g₁ g₂ W Y' G₁ G₂ E p ρ R ε tb := by
  let S := Icc (-1 : ℝ) 1
  let K := (coordinateCylinder normal)
  let Y := interior K
  let γ := conformalReference (depthScale normal 4) g₁
  let g := dilatedMetric g₁
  let k := dilatedMetric g₂
  let e (lam : ℝ) (y : (X dim)) := smoothMetricFrame (γ lam y)
  let depth := conformalDepth normal 4
  have hK : IsCompact K := isCompact_coordinateCylinder
  have hγ (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) := by
    apply contDiffOn_univ.mp
    simpa only [mem_univ,ofPred_true] using
      contDiffOn_conformalReference_family_entry hg₁ (contDiff_depthScale (normal := normal) 4) i j
  have hg (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j) :=
    (contDiffOn_univ.mp (hg₁.1 i j)).comp (contDiff_fst.smul contDiff_snd)
  have hgp (lam : ℝ) (y : (X dim)) : (g lam y).PosDef := hg₁.2 _ (mem_univ _)
  have hγp (lam : ℝ) (y : (X dim)) : (γ lam y).PosDef := (hgp lam y).smul (depthScale_pos (normal := normal) 4 y)
  have he (i : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i) :=
    contDiffOn_univ.mp (contDiffOn_smoothMetricFrame
      (fun i j => (hγ i j).contDiffOn) (fun q _ => hγp q.1 q.2) i)
  have hFrame (lam : ℝ) (_ : lam ∈ S) (y : (X dim)) (_ : y ∈ K) (i j : (I dim)) :
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0 :=
    smoothMetricFrame_orthonormal (hγp lam y) i j
  obtain ⟨m,_,hm,_,hCov⟩ := exists_uniform_conformalDepth_covector_bounds (normal := normal) isOpen_univ (mem_univ _)
    hK hg₁ (by norm_num : 0 < (4 : ℝ))
  have hd : ContDiff ℝ ∞ depth := contDiff_conformalDepth (normal := normal) 4
  obtain ⟨D,hD,hJet⟩ := exists_shrinkingRadius_coordinate_derivative_bounds hd hK hm (half_pos hρ).le hε
  obtain ⟨M,hM,hGeom⟩ := exists_uniform_movingTrace_frame_geometry (S := S) isCompact_Icc hK hγ hγp he
  obtain ⟨L,hL,hData⟩ := hData
  obtain ⟨B,hB,hDensity⟩ := exists_uniform_movingGreenDensity_jet_bounds hγ hγp hg hgp hE he
    isCompact_Icc hK isOpen_interior interior_subset hCY' hρ hD hM hL hNormal hFrame hGeom
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  refine ⟨B,hB,?_⟩
  filter_upwards [hS,hCov,hData] with lam hlam hCov hData hpos δ hδ hSmall
  obtain ⟨O,G,hO,hG,hSphere,hEq,hDJ⟩ := hData hpos δ hδ hSmall
  let r := shrinkingRadius R p depth δ
  have hr : ContDiff ℝ ∞ r := contDiff_shrinkingRadius hd R p δ
  have hrad (y : (X dim)) (hy : y ∈ Y) : r y ∈ Ioc 0 (ρ/2) :=
    ⟨shrinkingRadius_pos hR hδ.1 p depth y,hRadius δ hδ y hy⟩
  have hJ (y : (X dim)) (hy : y ∈ Y) :=
    hJet (interior_subset hy) (γ lam) (hCov y (interior_subset hy)).2.1 hR hδ hp (hrad y hy).2 (hSmall y hy).2
  refine ⟨O,G,hO,hG,hSphere,hEq,?_⟩
  intro y hy hχ w
  have hD₀ : ScaledSphereDatumJets (2*dim+8) (scaledNormalGreenDatum E e G) (lam,(y,r y)) (r y) L :=
    fun z hz => hDJ y hy hχ ⟨z,hz⟩
  exact hDensity lam hlam r hr hrad (fun y hy => (hJ y hy).1)
    hO G hG.1 hSphere y hy hD₀ w

end CalderonN
