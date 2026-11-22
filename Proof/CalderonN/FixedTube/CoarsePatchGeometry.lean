module

public import Proof.CalderonN.ProductAffineChart
public import Proof.CalderonN.LowerCrossGreen
public import Proof.CalderonN.FixedTube.CoarseReferenceCross

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

theorem isOpen_lowerCross (B η : ℝ) : IsOpen (lowerCross normal B η) :=
  isOpen_knownCross isOpen_ball
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) normal).continuous continuous_const)

@[expose] def coarsePatch (normal : I dim) (c : (X dim)) (s δ : ℝ) : Set ((X dim) × (X dim)) :=
  ball (affineChartMap c s (planeCenter normal)) (s*(planeDepth+δ)) ×ˢ openAnnulus c (4*s/5) (6*s/5)

@[expose] def retainedPatch (c : (X dim)) (s κ : ℝ) : Set ((X dim) × (X dim)) :=
  ball c (κ*s) ×ˢ openAnnulus c (9*s/10) (11*s/10)

theorem isOpen_coarsePatch (c : (X dim)) (s δ : ℝ) : IsOpen (coarsePatch normal c s δ) :=
  isOpen_ball.prod (isOpen_openAnnulus _ _ _)

theorem isOpen_retainedPatch (c : (X dim)) (s κ : ℝ) : IsOpen (retainedPatch c s κ) :=
  isOpen_ball.prod (isOpen_openAnnulus _ _ _)

theorem dist_affineChartMap (c : (X dim)) {s : ℝ} (hs : 0 ≤ s) (x y : (X dim)) :
    dist (affineChartMap c s x) (affineChartMap c s y) = s * dist x y := by
  rw [dist_eq_norm,dist_eq_norm]
  have hsub : affineChartMap c s x-affineChartMap c s y = s • (x-y) := by
    simp only [affineChartMap,smul_sub]
    abel
  rw [hsub,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]

theorem dist_affineChartMap_center (c : (X dim)) {s : ℝ} (hs : 0 ≤ s) (x : (X dim)) :
    dist (affineChartMap c s x) c = s * ‖x‖ := by
  simpa only [dist_zero_right,show affineChartMap c s 0 = c by simp [affineChartMap]] using
    dist_affineChartMap c hs x 0

theorem affineChartProduct_image_planeOutput (c : (X dim)) {s : ℝ} (hs : 0 < s) (δ : ℝ) :
    affineChartProduct c s '' (planeBall normal (planeDepth+δ) ×ˢ (planeAnnulusOutput (dim := dim))) = coarsePatch normal c s δ := by
  have hmem (x : (X dim) × (X dim)) :
      affineChartProduct c s x ∈ coarsePatch normal c s δ ↔
        x ∈ planeBall normal (planeDepth+δ) ×ˢ (planeAnnulusOutput (dim := dim)) := by
    change (dist (affineChartMap c s x.1) (affineChartMap c s (planeCenter normal)) < s*(planeDepth+δ) ∧
      4*s/5 < ‖affineChartMap c s x.2-c‖ ∧ ‖affineChartMap c s x.2-c‖ < 6*s/5) ↔
      (dist x.1 (planeCenter normal) < planeDepth+δ ∧ 4/5 < ‖x.2-0‖ ∧ ‖x.2-0‖ < 6/5)
    have hsecond : ‖affineChartMap c s x.2-c‖ = s*‖x.2‖ := by
      simpa only [dist_eq_norm] using dist_affineChartMap_center c hs.le x.2
    rw [dist_affineChartMap c hs.le,hsecond,sub_zero,
      show 4*s/5 = s*(4/5) by ring, show 6*s/5 = s*(6/5) by ring]
    simp only [mul_lt_mul_iff_of_pos_left hs]
  ext q
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hmem x).mpr hx
  · intro hq
    let x := affineChartProduct (-(s⁻¹ • c)) s⁻¹ q
    have hx : affineChartProduct c s x = q := affineChartProduct_inverse_right c hs.ne' q
    exact ⟨x,(hmem x).mp (hx ▸ hq),hx⟩

theorem norm_planeCenter : ‖(planeCenter normal)‖ = planeDepth := by
  simp [planeCenter,planeDepth,norm_smul,axis]

theorem retainedPatch_subset_coarsePatch (c : (X dim)) {s κ δ : ℝ} (hs : 0 < s) (hκδ : κ ≤ δ) :
    retainedPatch c s κ ⊆ coarsePatch normal c s δ := by
  intro q hq
  have hNear := mem_ball.mp hq.1
  have hDist := dist_triangle q.1 c (affineChartMap c s (planeCenter normal))
  rw [dist_comm c,dist_affineChartMap_center c hs.le,(norm_planeCenter (normal := normal))] at hDist
  refine ⟨mem_ball.mpr ?_,?_⟩
  · exact (hDist.trans_lt (add_lt_add_of_lt_of_le hNear le_rfl)).trans_le (by
      rw [mul_add]
      linarith [mul_le_mul_of_nonneg_right hκδ hs.le])
  · change 4*s/5 < ‖q.2-c‖ ∧ ‖q.2-c‖ < 6*s/5
    have hAway : 9*s/10 < ‖q.2-c‖ ∧ ‖q.2-c‖ < 11*s/10 := hq.2
    exact ⟨by linarith [hAway.1],by linarith [hAway.2]⟩

theorem affineChartMap_height {c : (X dim)} (hc : c normal = 0) (s : ℝ) (x : (X dim)) :
    affineChartMap c s x normal = s * x normal := by
  simp [affineChartMap,PiLp.add_apply,PiLp.smul_apply,hc]

theorem norm_affineChartMap_le (c : (X dim)) {s : ℝ} (hs : 0 ≤ s) (x : (X dim)) :
    ‖affineChartMap c s x‖ ≤ ‖c‖ + s*‖x‖ := by
  have h := norm_add_le c (s • x)
  simpa only [affineChartMap,norm_smul,Real.norm_eq_abs,abs_of_nonneg hs] using h

end CalderonN.FixedTube
