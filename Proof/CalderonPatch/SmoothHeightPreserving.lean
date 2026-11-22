module

public import Proof.CalderonPatch.NormalHeightIsometry

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis metricPair)

variable {n : ℕ} {i j : I n}

/-- A height-preserving smooth interior isometry extends smoothly
across a face where both coordinate metrics have their normal block.
Its tangential part at every small height is read on one interior slice. -/
theorem exists_smooth_germ_of_height_preserving_isometry
    {p : X n} (hp : p i = 0) {U V : Set (X n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    {g h : MetricField n}
    (hN : HasNormalMetricBlock i g U) (hN' : HasNormalMetricBlock j h V)
    (hPos : ∀ x ∈ V, (h x).PosDef)
    {f : X n → X n} (hf : ContDiffOn ℝ ∞ f (U ∩ {x | 0 < x i}))
    (hc : ContinuousOn f (U ∩ {x | 0 ≤ x i}))
    (hMaps : MapsTo f (U ∩ {x | 0 < x i}) V)
    (hHeight : ∀ x ∈ U ∩ {x | 0 < x i}, f x j = x i)
    (hIsom : ∀ x ∈ U ∩ {x | 0 < x i}, ∀ v w, metricPair g x v w =
      metricPair h (f x) (fderiv ℝ f x v) (fderiv ℝ f x w)) :
    ∃ W : Set (X n), IsOpen W ∧ p ∈ W ∧ ∃ F : X n → X n, ContDiffOn ℝ ∞ F W ∧
      EqOn f F (W ∩ {x | 0 ≤ x i}) ∧
      ∀ x ∈ W ∩ {x | 0 ≤ x i},
        boundaryFoot i x ∈ U ∧ f x = f (boundaryFoot i x) + x i • axis j := by
  obtain ⟨ε,hε,hB⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hpU)
  let a := ε / (4 * (‖axis i‖ + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have haε : a * ‖axis i‖ < ε / 2 := by
    have hR : ε / 2 * (4 * (‖axis i‖ + 1)) > ε * ‖axis i‖ := by
      nlinarith [mul_nonneg hε.le (norm_nonneg (axis i))]
    dsimp [a]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ (by positivity)).mpr hR
  let W := (boundaryFoot i) ⁻¹' ball p (ε / 2) ∩ {x | |x i| < a}
  have hW : IsOpen W := (isOpen_ball.preimage (boundaryFoot i).continuous).inter
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.abs continuous_const)
  have hpW : p ∈ W := by
    change boundaryFoot i p ∈ ball p (ε / 2) ∧ |p i| < a
    rw [boundaryFoot_on_face i hp, hp, abs_zero]
    exact ⟨mem_ball_self (by positivity),ha⟩
  let level (x : X n) := boundaryFoot i x + a • axis i
  let F (x : X n) := f (level x) + (x i - a) • axis j
  have hSlice (x : X n) (hx : x ∈ W) (s : ℝ) (hs : s ∈ Icc 0 a) :
      boundaryFoot i x + s • axis i ∈ U := by
    apply hB
    have hFoot : dist (boundaryFoot i x) p < ε / 2 := mem_ball.mp hx.1
    rw [mem_ball, dist_eq_norm]
    rw [dist_eq_norm] at hFoot
    calc
      ‖boundaryFoot i x + s • axis i - p‖ = ‖(boundaryFoot i x - p) + s • axis i‖ := by
        rw [add_sub_right_comm]
      _ ≤ ‖boundaryFoot i x - p‖ + ‖s • axis i‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hFoot (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
        exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans_lt haε)
      _ = ε := by ring
  have hAxis : axis i i = 1 := by simp [axis]
  have hHeightSlice (x : X n) (s : ℝ) : (boundaryFoot i x + s • axis i) i = s := by
    simp [boundaryFoot_coord, hAxis]
  have hLevel : MapsTo level W (U ∩ {x | 0 < x i}) := by
    intro x hx
    refine ⟨hSlice x hx a ⟨ha.le,le_rfl⟩,?_⟩
    change 0 < (boundaryFoot i x + a • axis i) i
    rwa [hHeightSlice]
  have hF : ContDiffOn ℝ ∞ F W := by
    have hl : ContDiff ℝ ∞ level := (boundaryFoot i).contDiff.add contDiff_const
    exact (hf.comp hl.contDiffOn hLevel).add
      ((((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.sub contDiff_const).smul contDiff_const).contDiffOn)
  have hEq : EqOn f F (W ∩ {x | 0 ≤ x i}) := by
    intro x hx
    let z := boundaryFoot i x
    let t := x i
    let path (s : ℝ) := z + s • axis i
    have hta : t < a := (le_abs_self _).trans_lt hx.1.2
    have ht₀ : 0 ≤ t := hx.2
    have hU' : IsOpen (U ∩ {x | 0 < x i}) :=
      hU.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
    have hPathDiff (s : ℝ) : HasDerivAt path (axis i) s := by
      simpa only [id_eq, one_smul, zero_add] using
        HasDerivAt.fun_add (hasDerivAt_const s z) ((hasDerivAt_id s).smul_const (axis i))
    have hPathPoint (s : ℝ) (hs : s ∈ Ioo t a) : path s ∈ U ∩ {x | 0 < x i} := by
      refine ⟨hSlice x hx.1 s ⟨ht₀.trans hs.1.le,hs.2.le⟩,?_⟩
      change 0 < (boundaryFoot i x + s • axis i) i
      rw [hHeightSlice]
      exact ht₀.trans_lt hs.1
    have hPathOn : MapsTo path (Icc t a) (U ∩ {x | 0 ≤ x i}) := by
      intro s hs
      refine ⟨hSlice x hx.1 s ⟨ht₀.trans hs.1,hs.2⟩,?_⟩
      change 0 ≤ (boundaryFoot i x + s • axis i) i
      rw [hHeightSlice]
      exact ht₀.trans hs.1
    ext k
    let φ (s : ℝ) := f (path s) k - s * axis j k
    have hC : ContinuousOn φ (Icc t a) := by
      let π : X n →L[ℝ] ℝ := EuclideanSpace.proj k
      have hPathC : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
      exact (π.continuous.comp_continuousOn (hc.comp hPathC.continuousOn hPathOn)).sub
        ((continuous_id.mul continuous_const).continuousOn)
    have hD (s : ℝ) (hs : s ∈ Ioo t a) : HasDerivAt φ 0 s := by
      have hs' := hPathPoint s hs
      have hfd := (hf.contDiffAt (hU'.mem_nhds hs')).differentiableAt (by simp)
      have hMapAxis := maps_normal_axis_of_height_eq hU'
        (fun x hx => hN x hx.1) hN' hPos hMaps hs' hfd hHeight (hIsom _ hs')
      have hh : HasDerivAt (f ∘ path) (axis j) s :=
        hMapAxis ▸ hfd.hasFDerivAt.comp_hasDerivAt s (hPathDiff s)
      let π : X n →L[ℝ] ℝ := EuclideanSpace.proj k
      have he : HasDerivAt (π ∘ f ∘ path) (axis j k) s := π.hasFDerivAt.comp_hasDerivAt s hh
      have he' : HasDerivAt (fun s => f (path s) k) (axis j k) s := he
      simpa only [φ, one_mul, id_eq, sub_self] using
        HasDerivAt.fun_sub he' ((hasDerivAt_id s).mul_const (axis j k))
    obtain ⟨s,hs,hMean⟩ := exists_hasDerivAt_eq_slope φ (fun _ => 0) hta hC hD
    have hEqual : φ t = φ a := by
      have hNE : a - t ≠ 0 := sub_ne_zero.mpr hta.ne'
      exact sub_eq_zero.mp ((div_eq_zero_iff.mp hMean.symm).resolve_right hNE) |>.symm
    have hT : path t = x := boundaryFoot_add_axis i x
    have hL : path a = level x := rfl
    change f (path t) k - t * axis j k = f (path a) k - a * axis j k at hEqual
    rw [hT, hL] at hEqual
    change f x k = (f (level x) + (t - a) • axis j) k
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    linarith

  refine ⟨W,hW,hpW,F,hF,hEq,?_⟩
  intro x hx
  let z := boundaryFoot i x
  refine ⟨?_,?_⟩
  · simpa only [zero_smul,add_zero] using hSlice x hx.1 0 ⟨le_rfl,ha.le⟩
  have hz₀ : z i = 0 := boundaryFoot_coord i x
  have hzW : z ∈ W := by
    change boundaryFoot i z ∈ ball p (ε / 2) ∧ |z i| < a
    rw [boundaryFoot_on_face i hz₀, hz₀, abs_zero]
    exact ⟨hx.1.1,ha⟩
  have he₁ := hEq hx
  have he₀ := hEq (show z ∈ W ∩ {x | 0 ≤ x i} from ⟨hzW,hz₀.ge⟩)
  change f z = f (boundaryFoot i z + a • axis i) + (z i - a) • axis j at he₀
  rw [boundaryFoot_on_face i hz₀, hz₀, zero_sub] at he₀
  change f x = f (z + a • axis i) + (x i - a) • axis j at he₁
  rw [he₁, he₀, sub_eq_add_neg, add_smul]
  abel

end CalderonPatch
