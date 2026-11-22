module

public import Proof.CalderonPatch.SmoothHeightPreserving

import Mathlib.Tactic.Linarith

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis metricPair)

variable {n : ℕ} {i j : I n}

theorem eventually_normalHeight_le_of_local_isometry
    {p : X n} (hp : p i = 0) {U V : Set (X n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    {g h : MetricField n}
    (hN : HasNormalMetricBlock i g U) (hN' : HasNormalMetricBlock j h V)
    (hPos : ∀ x ∈ V, (h x).PosDef)
    {f : X n → X n} (hf : ContDiffOn ℝ ∞ f (U ∩ {x | 0 < x i}))
    (hc : ContinuousOn f (U ∩ {x | 0 ≤ x i}))
    (hMaps : MapsTo f (U ∩ {x | 0 < x i}) V)
    (hBoundary : ∀ x ∈ U ∩ {x | x i = 0}, f x j = 0)
    (hIsom : ∀ x ∈ U ∩ {x | 0 < x i}, ∀ v w, metricPair g x v w =
      metricPair h (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)) :
    ∀ᶠ x in 𝓝[{x | 0 ≤ x i}] p, f x j ≤ x i := by
  obtain ⟨ε,hε,hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  have hBFoot : ∀ᶠ x in 𝓝 p, boundaryFoot i x ∈ ball p (ε / 2) := by
    apply (boundaryFoot i).continuous.continuousAt.eventually_mem
    rw [boundaryFoot_on_face i hp]
    exact ball_mem_nhds _ (by positivity)
  have hBHeight : ∀ᶠ x in 𝓝 p, |x i| * ‖axis i‖ < ε / 2 := by
    have hc : Continuous (fun x : X n => |x i| * ‖axis i‖) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.abs.mul continuous_const
    apply (isOpen_lt hc continuous_const).mem_nhds
    simp [hp,hε]
  filter_upwards [hBFoot.filter_mono nhdsWithin_le_nhds, hBHeight.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hxFoot hxHeight hx
  let t := x i
  let z := boundaryFoot i x
  let path (s : ℝ) := z + s • axis i
  have ht : 0 ≤ t := hx
  have hAxis : axis i i = 1 := by simp [axis]
  have hPathHeight (s : ℝ) : path s i = s := by simp [path,z,boundaryFoot_coord,hAxis]
  have hPathAt (s : ℝ) (hs : s ∈ Icc 0 t) : path s ∈ U := by
    apply hB
    rw [mem_ball, dist_eq_norm] at hxFoot ⊢
    change ‖z + s • axis i - p‖ < ε
    calc
      _ = ‖z - p + s • axis i‖ := by rw [add_sub_right_comm]
      _ ≤ ‖z - p‖ + ‖s • axis i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hxFoot (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        change |t| * ‖axis i‖ < ε / 2 at hxHeight
        rw [abs_of_nonneg ht] at hxHeight
        exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans_lt hxHeight)
      _ = ε := by ring
  have hP₀ : path 0 = z := by simp [path]
  have hPt : path t = x := boundaryFoot_add_axis i x
  have hZ : f z j = 0 :=
    hBoundary z ⟨hP₀ ▸ hPathAt 0 ⟨le_rfl,ht⟩,boundaryFoot_coord i x⟩
  by_cases hPosT : 0 < t
  · let S := U ∩ {x | 0 < x i}
    have hSo : IsOpen S := hU.inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
    have hPath : MapsTo path (Icc 0 t) (U ∩ {x | 0 ≤ x i}) := by
      intro s hs
      refine ⟨hPathAt s hs,?_⟩
      change 0 ≤ path s i
      rw [hPathHeight]
      exact hs.1
    have hPathC : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
    have hφC := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn
      (hc.comp hPathC.continuousOn hPath)
    have hInterior (s : ℝ) (hs : s ∈ Ioo 0 t) : path s ∈ S := by
      refine ⟨hPathAt s ⟨hs.1.le,hs.2.le⟩,?_⟩
      change 0 < path s i
      rw [hPathHeight]
      exact hs.1
    have hle := normalHeight_le_of_isometry_on_segment hPosT (fun y hy => hN y hy.1)
      hN' hPos hZ hφC hInterior hMaps
      (fun y hy => (hf.contDiffAt (hSo.mem_nhds hy)).differentiableAt (by simp)) hIsom
    change f (path t) j ≤ t at hle
    rwa [hPt] at hle
  · have hz : t = 0 := le_antisymm (le_of_not_gt hPosT) ht
    have hzx : z = x := boundaryFoot_on_face i hz
    change f x j ≤ t
    rw [hz, ← hzx, hZ]

/-- Comparing an isometry with its inverse on the respective
one-sided neighborhoods forces equality of the normal heights. -/
theorem eventually_normalHeight_eq_of_inverse_comparison
    {p : X n} {f g : X n → X n}
    (hf : Tendsto f (𝓝[{x | 0 ≤ x i}] p) (𝓝[{y | 0 ≤ y j}] (f p)))
    (hg : (g ∘ f) =ᶠ[𝓝[{x | 0 ≤ x i}] p] id)
    (hle : ∀ᶠ x in 𝓝[{x | 0 ≤ x i}] p, f x j ≤ x i)
    (hleInv : ∀ᶠ y in 𝓝[{y | 0 ≤ y j}] (f p), g y i ≤ y j) :
    ∀ᶠ x in 𝓝[{x | 0 ≤ x i}] p, f x j = x i := by
  filter_upwards [hg, hle, hf.eventually hleInv] with x hx h₁ h₂
  change g (f x) = x at hx
  change g (f x) i ≤ f x j at h₂
  rw [hx] at h₂
  exact le_antisymm h₁ h₂

/-- A one-sided germ of normal-height preservation gives the smooth
continuation of the interior isometry to the boundary chart. -/
theorem exists_smooth_boundaryGerm_of_local_isometry
    {p : X n} (hp : p i = 0) {U V : Set (X n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    {g h : MetricField n}
    (hN : HasNormalMetricBlock i g U) (hN' : HasNormalMetricBlock j h V)
    (hPos : ∀ x ∈ V, (h x).PosDef)
    {f : X n → X n} (hf : ContDiffOn ℝ ∞ f (U ∩ {x | 0 < x i}))
    (hc : ContinuousOn f (U ∩ {x | 0 ≤ x i}))
    (hMaps : MapsTo f (U ∩ {x | 0 < x i}) V)
    (hHeight : ∀ᶠ x in 𝓝[{x | 0 ≤ x i}] p, f x j = x i)
    (hIsom : ∀ x ∈ U ∩ {x | 0 < x i}, ∀ v w, metricPair g x v w =
      metricPair h (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)) :
    ∃ F : X n → X n, ContDiffAt ℝ ∞ F p ∧ f =ᶠ[𝓝[{x | 0 ≤ x i}] p] F := by
  obtain ⟨U',hHeight',hU',hp'⟩ := _root_.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hHeight)
  let W := U ∩ U'
  have hOp : IsOpen W := hU.inter hU'
  have hpW : p ∈ W := ⟨hpU,hp'⟩
  have hSmall {s : Set (X n)} : W ∩ s ⊆ U ∩ s := fun _ hx => ⟨hx.1.1,hx.2⟩
  obtain ⟨V',hV',hpV',F,hF,hEq,_⟩ := exists_smooth_germ_of_height_preserving_isometry hp hOp hpW
    (fun x hx => hN x hx.1) hN' hPos (hf.mono hSmall) (hc.mono hSmall) (hMaps.mono_left hSmall)
    (fun x hx => hHeight' x hx.1.2 (show 0 ≤ x i from (show 0 < x i from hx.2).le)) (fun x hx => hIsom x (hSmall hx))
  refine ⟨F,hF.contDiffAt (hV'.mem_nhds hpV'),?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV'.mem_nhds hpV'), self_mem_nhdsWithin] with y hy hy'
  exact hEq ⟨hy,hy'⟩

/-- A local isometry that preserves normal height and fixes the boundary
face is the identity in the common signed coordinates. -/
theorem eventually_eq_id_of_normalHeight_eq_and_fixes_face
    {p : X n} (hp : p i = 0) {U V : Set (X n)} (hU : IsOpen U) (hpU : p ∈ U)
    {g h : MetricField n} (hN : HasNormalMetricBlock i g U) (hN' : HasNormalMetricBlock i h V)
    (hPos : ∀ x ∈ V, (h x).PosDef)
    {f : X n → X n} (hf : ContDiffOn ℝ ∞ f (U ∩ {x | 0 < x i}))
    (hc : ContinuousOn f (U ∩ {x | 0 ≤ x i}))
    (hMaps : MapsTo f (U ∩ {x | 0 < x i}) V)
    (hFace : EqOn f id (U ∩ {x | x i = 0}))
    (hHeight : ∀ᶠ x in 𝓝[{x | 0 ≤ x i}] p, f x i = x i)
    (hIsom : ∀ x ∈ U ∩ {x | 0 < x i}, ∀ v w, metricPair g x v w =
      metricPair h (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)) :
    f =ᶠ[𝓝[{x | 0 ≤ x i}] p] id := by
  obtain ⟨U',hHeight',hU',hp'⟩ := _root_.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hHeight)
  let W := U ∩ U'
  have hOp : IsOpen W := hU.inter hU'
  have hpW : p ∈ W := ⟨hpU,hp'⟩
  have hSmall {s : Set (X n)} : W ∩ s ⊆ U ∩ s := fun _ hx => ⟨hx.1.1,hx.2⟩
  obtain ⟨V',hV',hpV',_,_,_,hNormal⟩ := exists_smooth_germ_of_height_preserving_isometry hp hOp hpW
    (fun x hx => hN x hx.1) hN' hPos (hf.mono hSmall) (hc.mono hSmall) (hMaps.mono_left hSmall)
    (fun x hx => hHeight' x hx.1.2 (show 0 ≤ x i from (show 0 < x i from hx.2).le))
    (fun x hx => hIsom x (hSmall hx))
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV'.mem_nhds hpV'), self_mem_nhdsWithin] with x hx hx'
  obtain ⟨hFoot,hF⟩ := hNormal x ⟨hx,hx'⟩
  rw [hF, hFace ⟨hFoot.1,boundaryFoot_coord i x⟩]
  exact boundaryFoot_add_axis i x

end CalderonPatch
