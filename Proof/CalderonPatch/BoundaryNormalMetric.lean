module

public import Proof.CalderonPatch.BoundaryNormalGauss
public import Proof.CalderonPatch.BoundaryNormalSide
public import Proof.CalderonPatch.ChartChange

import Proof.CalderonN.MetricPullback

public section

noncomputable section
open Filter Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField axis pullbackMetric coordinateJacobian_det_ne_zero)

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem fderiv_bijective_of_smoothOpenPartialHomeomorph {e : OpenPartialHomeomorph (X n) (X n)}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {x : X n} (hx : x ∈ e.source) : Function.Bijective (fderiv ℝ e x) := by
  have h := ((hei.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)).hasFDerivAt.comp x
    ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
  have hid : (e.symm : X n → X n) ∘ e =ᶠ[𝓝 x] id :=
    Filter.mem_of_superset (e.open_source.mem_nhds hx) (fun y hy => e.left_inv hy)
  have hι := (h.congr_of_eventuallyEq hid.symm).unique (hasFDerivAt_id x)
  have hInj : Function.Injective (fderiv ℝ e x) := by
    intro a b hab
    have hh := congrArg (fderiv ℝ e.symm (e x)) hab
    change ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) a =
      ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) b at hh
    rwa [hι] at hh
  exact ⟨hInj, LinearMap.injective_iff_surjective.mp hInj⟩

/-- The normal coordinates preserve the inward half space and put the
metric in the exact block form used in the boundary factorization. -/
theorem exists_boundaryNormalMetric {g : MetricField n} (hg : CalderonN.SmoothMetric univ g)
    {p : X n} {i : I n} (hp : p i = 0) {V : Set (X n)} (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ e : OpenPartialHomeomorph (X n) (X n),
      p ∈ e.source ∧ EqOn e id (e.source ∩ {x | x i = 0}) ∧ e.target ⊆ V ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x ∈ e.source, (0 < e x i ↔ 0 < x i) ∧ (0 ≤ e x i ↔ 0 ≤ x i)) ∧
      CalderonN.SmoothMetric e.source (pullbackMetric g e) ∧
      ∀ x ∈ e.source, pullbackMetric g e x i i = 1 ∧ ∀ j ≠ i, pullbackMetric g e x i j = 0 := by
  obtain ⟨r,F,e,hr,hF,hpE,he,hEs,hEi,hRest⟩ := exists_boundaryNormalChart hg hp
  let f := boundaryNormalEndpoint g i F
  let ν := positiveCoordinateNormal g i
  have hf := boundaryNormalEndpoint_smooth hF hg i
  have hν : ContDiff ℝ ∞ ν := contDiffOn_univ.mp (contDiffOn_positiveCoordinateNormal hg i)
  have hp0 : f p = p := boundaryNormalEndpoint_rest hF (mem_ball_self (by norm_num : (0 : ℝ) < 1)) hp
  have hCp : Continuous (fun x : X n => x i • ν (boundaryFoot i x)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.smul (hν.continuous.comp (boundaryFoot i).continuous)
  have hSize : ∀ᶠ x in 𝓝 p, ‖x i • ν (boundaryFoot i x)‖ < r := by
    apply (isOpen_lt hCp.norm continuous_const).mem_nhds
    change ‖p i • ν (boundaryFoot i p)‖ < r
    rwa [hp, zero_smul, norm_zero]
  have hFoot : ∀ᶠ x in 𝓝 p, boundaryFoot i x ∈ ball p 1 := by
    apply (boundaryFoot i).continuous.continuousAt.eventually_mem
    rw [boundaryFoot_on_face i hp]
    exact isOpen_ball.mem_nhds (mem_ball_self (by norm_num))
  have hTarget : ∀ᶠ x in 𝓝 p, f x ∈ V := by
    have hcp : ContinuousAt f p := hf.continuous.continuousAt
    exact hcp.eventually_mem (hV.mem_nhds (show f p ∈ V by rwa [hp0]))
  obtain ⟨U, hUgood, hU, hpU⟩ := _root_.eventually_nhds_iff.mp
    ((boundaryNormalEndpoint_side hF hr hg hp).and (hSize.and (hFoot.and hTarget)))
  let e' := e.restr U
  have hS : e'.source = e.source ∩ U := e.restr_source' U hU
  have hts : e'.target ⊆ e.target := fun _ hx => hx.1
  have hFine : (e' : X n → X n) = f := he
  have hSep : ∀ x ∈ e'.source, x ∈ e.source ∧ x ∈ U := fun x hx => (Set.ext_iff.mp hS x).mp hx
  have hG : CalderonN.SmoothMetric e'.source (pullbackMetric g e') := by
    apply CalderonN.smoothMetric_pullbackMetric hg
    · exact hFine.symm ▸ hf
    · exact fun _ _ => mem_univ _
    · intro x hx
      exact coordinateJacobian_det_ne_zero (fderiv_bijective_of_smoothOpenPartialHomeomorph hEs hEi (hSep x hx).1)
  refine ⟨e', hS.symm ▸ ⟨hpE,hpU⟩, fun x hx => hRest ⟨(hSep x hx.1).1,hx.2⟩,
    ?_, hEs.mono (fun x hx => (hSep x hx).1), hEi.mono hts, ?_, hG, ?_⟩
  · intro y hy
    have hh := (hUgood (e'.symm y) (hSep _ (e'.map_target hy)).2).2.2.2
    rwa [← hFine, e'.right_inv hy] at hh
  · intro x hx
    rw [hFine]
    exact (hUgood x (hSep x hx).2).1
  · intro x hx
    have hh := hUgood x (hSep x hx).2
    have hN := boundaryNormalEndpoint_unit_orthogonal hg hF hr hh.2.2.1 (boundaryFoot_coord i x) (x i) hh.2.1
    have hX := boundaryFoot_add_axis i x
    change CalderonN.metricPair g (f (boundaryFoot i x + x i • axis i))
      (fderiv ℝ f (boundaryFoot i x + x i • axis i) (axis i))
      (fderiv ℝ f (boundaryFoot i x + x i • axis i) (axis i)) = 1 ∧
      (∀ v : X n, v i = 0 → CalderonN.metricPair g (f (boundaryFoot i x + x i • axis i))
        (fderiv ℝ f (boundaryFoot i x + x i • axis i) (axis i))
        (fderiv ℝ f (boundaryFoot i x + x i • axis i) v) = 0) at hN
    rw [hX, ← hFine] at hN
    refine ⟨(pullbackMetric_apply _ _ _ _ _).trans hN.1, fun j hj =>
      (pullbackMetric_apply _ _ _ _ _).trans (hN.2 (axis j) (by simp [axis, hj]))⟩

end CalderonPatch
