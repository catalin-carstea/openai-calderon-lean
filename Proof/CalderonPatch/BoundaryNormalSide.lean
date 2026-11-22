module

public import Proof.CalderonPatch.BoundaryNormalChart

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis GeodesicPhase GeodesicFlowOn geodesicEndpoint)

variable {n : ℕ}

theorem boundaryFoot_coord (i : I n) (x : X n) : boundaryFoot i x i = 0 := by
  rw [boundaryFoot_apply]
  simp [axis]

theorem boundaryFoot_add_axis (i : I n) (x : X n) : boundaryFoot i x + x i • axis i = x := by
  rw [boundaryFoot_apply, sub_add_cancel]

theorem boundaryNormalEndpoint_rest {g : MetricField n} {p q : X n} {i : I n} {r : ℝ}
    {F : GeodesicPhase n → ℝ → GeodesicPhase n}
    (hF : GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F)
    (hq : q ∈ ball p 1) (hq₀ : q i = 0) : boundaryNormalEndpoint g i F q = q := by
  rw [boundaryNormalEndpoint, boundaryFoot_on_face i hq₀, hq₀, zero_smul]
  exact hF.endpoint_rest ⟨mem_singleton _, ball_subset_closedBall hq⟩

/-- Close to a seam point, the signed normal endpoint has the same
strict and weak height sign as its input. -/
theorem boundaryNormalEndpoint_side {g : MetricField n} {p : X n} {i : I n} {r : ℝ}
    {F : GeodesicPhase n → ℝ → GeodesicPhase n}
    (hF : GeodesicFlowOn (fun _ => g) ({(0 : ℝ)} ×ˢ closedBall p 1) r F)
    (hr : 0 < r) (hg : CalderonN.SmoothMetric univ g) (hp : p i = 0) :
    ∀ᶠ x in 𝓝 p,
      (0 < boundaryNormalEndpoint g i F x i ↔ 0 < x i) ∧
      (0 ≤ boundaryNormalEndpoint g i F x i ↔ 0 ≤ x i) := by
  let f := boundaryNormalEndpoint g i F
  let ν := positiveCoordinateNormal g i
  have hf := boundaryNormalEndpoint_smooth hF hg i
  let D := fderiv ℝ f
  have hDp : D p (axis i) = ν p := by
    change fderiv ℝ f p (axis i) = _
    rw [(boundaryNormalEndpoint_hasFDerivAt hF hr hg hp (mem_ball_self (by norm_num : (0 : ℝ) < 1))).fderiv]
    change boundaryFoot i (axis i) + axis i i • ν p = _
    have hi : axis i i = 1 := by simp [axis]
    rw [boundaryFoot_apply, hi, one_smul, sub_self, zero_add, one_smul]
  have hD : Continuous (fun x => D x (axis i) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hPos : 0 < D p (axis i) i := by
    rw [hDp]
    exact positiveCoordinateNormal_transverse g (hg.2 p (mem_univ p)) i
  obtain ⟨ε, hε, hB⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_lt continuous_const hD).mem_nhds hPos)
  have hFoot : ∀ᶠ x in 𝓝 p, boundaryFoot i x ∈ ball p (min 1 (ε / 2)) := by
    apply (boundaryFoot i).continuous.continuousAt.eventually_mem
    rw [boundaryFoot_on_face i hp]
    exact isOpen_ball.mem_nhds (mem_ball_self (lt_min (by norm_num) (by positivity)))
  have hT : ∀ᶠ x in 𝓝 p, |x i| * ‖axis i‖ < ε / 2 := by
    have hc : Continuous (fun x : X n => |x i| * ‖axis i‖) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.abs.mul continuous_const
    apply (isOpen_lt hc continuous_const).mem_nhds
    simp [hp, hε]
  filter_upwards [hFoot, hT] with x hx ht
  let z := boundaryFoot i x
  let φ : ℝ → ℝ := fun t => f (z + t • axis i) i
  have hφ' (t : ℝ) : HasDerivAt φ (D (z + t • axis i) (axis i) i) t := by
    have hA : HasDerivAt (fun s : ℝ => z + s • axis i) (axis i) t := by
      simpa only [one_smul, id_eq, zero_add] using
        HasDerivAt.fun_add (hasDerivAt_const t z) ((hasDerivAt_id t).smul_const (axis i))
    have hF' : HasFDerivAt f (D (z + t • axis i)) (z + t • axis i) :=
      (hf.differentiable (by simp) _).hasFDerivAt
    let proj : X n →L[ℝ] ℝ := EuclideanSpace.proj i
    have hcomp : HasDerivAt (f ∘ fun s => z + s • axis i) (D (z + t • axis i) (axis i)) t :=
      hF'.comp_hasDerivAt t hA
    change HasDerivAt (proj ∘ (f ∘ fun s => z + s • axis i)) _ t
    exact proj.hasFDerivAt.comp_hasDerivAt _ hcomp
  have hDeriv (t : ℝ) (h : |t| ≤ |x i|) : 0 < deriv φ t := by
    rw [(hφ' t).deriv]
    apply hB
    rw [mem_ball, dist_eq_norm] at hx ⊢
    calc
      ‖z + t • axis i - p‖ = ‖z - p + t • axis i‖ := by rw [add_sub_right_comm]
      _ ≤ ‖z - p‖ + ‖t • axis i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hx.trans_le (min_le_right _ _)) (by
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_lt ht)
      _ = ε := by ring
  have hMono : StrictMonoOn φ (Icc (-|x i|) |x i|) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hφ' t).continuousAt.continuousWithinAt) ?_
    intro t ht'
    have ht'' : t ∈ Icc (-|x i|) |x i| := interior_subset ht'
    exact hDeriv t (abs_le.mpr ht'')
  have h0 : (0 : ℝ) ∈ Icc (-|x i|) |x i| := ⟨neg_nonpos.mpr (abs_nonneg _), abs_nonneg _⟩
  have htx : x i ∈ Icc (-|x i|) |x i| := ⟨neg_abs_le _, le_abs_self _⟩
  have hz₀ : φ 0 = 0 := by
    have hz : z ∈ ball p 1 := mem_ball.mpr ((mem_ball.mp hx).trans_le (min_le_left _ _))
    change f (z + (0 : ℝ) • axis i) i = 0
    rw [zero_smul, add_zero]
    change boundaryNormalEndpoint g i F z i = 0
    rw [boundaryNormalEndpoint_rest hF hz (boundaryFoot_coord i x)]
    exact boundaryFoot_coord i x
  have hxfe : φ (x i) = f x i := by
    change f (boundaryFoot i x + x i • axis i) i = _
    rw [boundaryFoot_add_axis]
  change (0 < f x i ↔ 0 < x i) ∧ (0 ≤ f x i ↔ 0 ≤ x i)
  rw [← hxfe]
  exact ⟨by simpa only [hz₀] using hMono.lt_iff_lt h0 htx,
    by simpa only [hz₀] using hMono.le_iff_le h0 htx⟩

end CalderonPatch
