module

public import Proof.CalderonN.NormalChartFamilies
public import Proof.CalderonN.ParametricBallVelocityAdjoint
public import Proof.CalderonN.ConstantMetricScale

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ScaledGreenDatumJets
import Mathlib.Tactic

/-! Adapted from `MovingBallFamilies` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000
noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The normalized pullback on the fixed unit ball at its actual radius. -/
@[expose] def movingBallMetric (g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (r : (X dim) → ℝ) (q : (X dim) × (X dim)) : (Mat dim) :=
  normalizedBallMetric g E e q.1 (r q.1) q.2

/-- The same normalization keeps one explicit power of the physical radius
outside the velocity. -/
@[expose] def movingBallScaledVelocity (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (r : (X dim) → ℝ) (i : (I dim)) (q : (X dim) × (X dim)) : (X dim) :=
  scaledNormalTraceVelocity γ E e q.1 (r q.1) (coordDeriv i r q.1) q.2 (axis i)

theorem contDiff_movingNormalEndpoint
    {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E) {e : (Frame dim)}
    (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => normalBallChartMap E e q.1 (r q.1) q.2) := by
  have hW : ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => frameVector e q.1 q.2) :=
    contDiff_family_frameVector (fun i => (he i).comp contDiff_fst) contDiff_snd
  exact hE.comp (contDiff_fst.prodMk ((hr.comp contDiff_fst).smul hW))

theorem normalizedBallMetric_posDef
    {g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {e : (Frame dim)} {y z : (X dim)} {r : ℝ}
    (hg : (g (normalBallChartMap E e y r z)).PosDef)
    (hD : (coordinateMatrix (normalizedBallDerivative E e y r z)).det ≠ 0) :
    (normalizedBallMetric g E e y r z).PosDef := by
  let A := coordinateMatrix (normalizedBallDerivative E e y r z)
  change (Aᵀ * g (normalBallChartMap E e y r z) * A).PosDef
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hg.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hD)))

set_option maxHeartbeats 3200000 in
/-- One common open neighborhood of the moving fixed balls makes the
actual normalized metrics and scaled velocities smooth. -/
theorem exists_smooth_movingBallFamilies
    {Y Ω : Set (X dim)} {γ g : (MetricField dim)} (hγ : SmoothMetric univ γ) (hg : SmoothMetric univ g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hFrame : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y ∧ r y < ρ) :
    ∃ U : Set ((X dim) × (X dim)), IsOpen U ∧ Y ×ˢ closedBall (0 : (X dim)) 1 ⊆ U ∧
      (∀ q ∈ U, (coordinateMatrix (normalizedBallDerivative E e q.1 (r q.1) q.2)).det ≠ 0) ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun q => movingBallMetric g E e r q i j) U) ∧
      (∀ q ∈ U, (movingBallMetric g E e r q).PosDef) ∧
      ∀ i, ContDiffOn ℝ ∞ (movingBallScaledVelocity γ E e r i) U := by
  let D (q : (X dim) × (X dim)) := coordinateMatrix (normalizedBallDerivative E e q.1 (r q.1) q.2)
  let U : Set ((X dim) × (X dim)) := {q | (D q).det ≠ 0}
  let J (q : (X dim) × (X dim)) : ℝ × ((X dim) × (ℝ × (X dim))) := (0,(q.1,(r q.1,q.2)))
  have hJ : ContDiff ℝ ∞ J :=
    contDiff_const.prodMk (contDiff_fst.prodMk ((hr.comp contDiff_fst).prodMk contDiff_snd))
  have he' (i : (I dim)) : ContDiff ℝ ∞ (fun p : ℝ × (X dim) => e p.2 i) := (he i).comp contDiff_snd
  have hE' : ContDiff ℝ ∞ (fun p : ℝ × ((X dim) × (X dim)) => E p.2) := hE.comp contDiff_snd
  have hD (i j : (I dim)) : ContDiff ℝ ∞ (fun q => D q i j) := by
    have h := (contDiff_normalizedBallDerivative_family_entry
      (E := fun _ => E) (e := fun _ => e) hE' he' i j).comp hJ
    exact h
  have hU : IsOpen U :=
    isOpen_ne_fun ((contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j => (hD i j).contDiffOn))).continuous)
      continuous_const
  have hUsub : Y ×ˢ closedBall (0 : (X dim)) 1 ⊆ U := by
    intro q hq
    have hPos := hR q.1 hq.1
    obtain ⟨_,_,hBij⟩ := normalBallChartMap_on_openBall hE hN hq.1 (hFrame q.1 hq.1) hPos.1
    have hC : closedBall (0 : (X dim)) 1 ⊆ ball (0 : (X dim)) (ρ/(r q.1)) :=
      closedBall_subset_ball ((lt_div_iff₀ hPos.1).mpr (by simpa using hPos.2))
    exact normalizedBallDerivative_det_ne_zero hE e q.1 (hBij q.2 (hC hq.2))
  have hM (i j : (I dim)) : ContDiff ℝ ∞ (fun q => movingBallMetric g E e r q i j) := by
    have hg' (a b : (I dim)) : ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.2 a b) :=
      (contDiffOn_univ.mp (hg.1 a b)).comp contDiff_snd
    have h := (contDiff_normalizedBallMetric_family_entry (E := fun _ => E) (e := fun _ => e)
      (g := fun _ => g) hE' he' hg' i j).comp hJ
    change ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => normalizedBallMetric g E e q.1 (r q.1) q.2 i j) at h
    exact h
  have hPos (q : (X dim) × (X dim)) (hq : q ∈ U) : (movingBallMetric g E e r q).PosDef :=
    normalizedBallMetric_posDef (hg.2 _ (mem_univ _)) hq
  refine ⟨U,hU,hUsub,fun _ hq => hq,fun i j => (hM i j).contDiffOn,hPos,fun i => ?_⟩
  let f (q : (X dim) × (X dim)) : (NormalVelocityParameter dim) := (0,(q.1,(r q.1,(coordDeriv i r q.1,q.2))))
  have hDr : ContDiff ℝ ∞ (coordDeriv i r) :=
    (hr.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hf : ContDiff ℝ ∞ f :=
    contDiff_const.prodMk (contDiff_fst.prodMk ((hr.comp contDiff_fst).prodMk
      ((hDr.comp contDiff_fst).prodMk contDiff_snd)))
  let U' : Set (NormalVelocityParameter dim) := {q | (coordinateMatrix (normalizedBallDerivative E e
    q.2.1 q.2.2.1 q.2.2.2.2)).det ≠ 0}
  have hγ' (a b : (I dim)) : ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.2 a b) :=
    (contDiffOn_univ.mp (hγ.1 a b)).comp contDiff_snd
  have h := (contDiffOn_scaledNormalTraceVelocity_family (γ := fun _ => γ) hγ'
    (fun _ x => hγ.2 x (mem_univ _)) (E := fun _ => E) hE' (e := fun _ => e) he' (axis i)
    (U := U') (fun _ hq => hq)).comp hf.contDiffOn (fun _ hq => hq)
  change ContDiffOn ℝ ∞ (movingBallScaledVelocity γ E e r i) U at h
  exact h

/-- Convert between physical tangent vectors and Euclidean angular coordinates. -/
@[expose] def movingBallToFrame (γ : (MetricField dim)) (e : (Frame dim)) (q : (X dim) × (X dim)) : (X dim) × (X dim) :=
  (q.1,frameCoordinates γ q.1 (e q.1) q.2)

@[expose] def movingBallFromFrame (e : (Frame dim)) (q : (X dim) × (X dim)) : (X dim) × (X dim) :=
  (q.1,frameVector e q.1 q.2)

theorem contDiff_movingBallToFrame {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {e : (Frame dim)}
    (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) : ContDiff ℝ ∞ (movingBallToFrame γ e) := by
  have h := contDiff_family_frameCoordinates (γ := fun _ => γ)
    (fun i j => (contDiffOn_univ.mp (hγ.1 i j)).comp contDiff_snd)
    (e := fun _ => e) (fun i => (he i).comp contDiff_snd)
  have hv := h.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun q : (X dim) × (X dim) => ((0:ℝ),q)))
  exact contDiff_fst.prodMk hv

theorem contDiff_movingBallFromFrame {e : (Frame dim)}
    (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i)) : ContDiff ℝ ∞ (movingBallFromFrame e) :=
  contDiff_fst.prodMk (contDiff_family_frameVector (fun i => (he i).comp contDiff_fst) contDiff_snd)

theorem movingBallToFrame_fromFrame {γ : (MetricField dim)} {e : (Frame dim)} {y : (X dim)} {w : (X dim)}
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    movingBallToFrame γ e (movingBallFromFrame e (y,w)) = (y,w) := by
  change (y,frameCoordinates γ y (e y) (frameVector e y w)) = (y,w)
  exact congrArg (Prod.mk y) (frameCoordinates_frameVector γ y w (e y) he)

theorem movingBallToFrame_bundle {Y : Set (X dim)} {γ : (MetricField dim)} {e : (Frame dim)}
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    MapsTo (movingBallToFrame γ e) (bundle Y γ) (Y ×ˢ (standardSphere dim)) := by
  intro q hq
  have hz := norm_frameCoordinates_sq γ q.1 q.2 (e q.1) (he q.1 hq.1)
  rw [show metricPair γ q.1 q.2 q.2 = 1 from hq.2] at hz
  refine ⟨hq.1,mem_sphere_zero_iff_norm.mpr ?_⟩
  change ‖frameCoordinates γ q.1 (e q.1) q.2‖ = 1
  nlinarith [norm_nonneg (frameCoordinates γ q.1 (e q.1) q.2)]

theorem movingBallFromFrame_sphere {Y : Set (X dim)} {γ : (MetricField dim)} {e : (Frame dim)}
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0) :
    MapsTo (movingBallFromFrame e) (Y ×ˢ (standardSphere dim)) (bundle Y γ) :=
  fun q hq => ⟨hq.1,frameVector_mem_sphere γ e q.1 (he q.1 hq.1) ⟨q.2,hq.2⟩⟩

/-- An open set in the joint variables induces a smooth metric on every slice. -/
theorem smoothMetric_movingBall_slice {U : Set ((X dim) × (X dim))} {g : (X dim) × (X dim) → (Mat dim)}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) (y : (X dim)) :
    SmoothMetric ((Prod.mk y) ⁻¹' U) (fun z => g (y,z)) :=
  ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz),
    fun z hz => hPos (y,z) hz⟩

theorem smoothNear_of_open_cover {B F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : B → F} {S : Set B}
    (h : ∀ q ∈ S, ∃ U, IsOpen U ∧ q ∈ U ∧ ContDiffOn ℝ ∞ f U) : smoothNear f S := by
  let C : Set (Set B) := {U | IsOpen U ∧ ContDiffOn ℝ ∞ f U}
  have hOpen : IsOpen (⋃₀ C) := isOpen_sUnion fun _ hU => hU.1
  refine ⟨⋃₀ C,hOpen,?_,hOpen.contDiffOn_iff.mpr ?_⟩
  · intro q hq
    obtain ⟨U,hU,hqU,hf⟩ := h q hq
    exact mem_sUnion.mpr ⟨U,⟨hU,hf⟩,hqU⟩
  · intro q hq
    obtain ⟨U,⟨hU,hf⟩,hqU⟩ := mem_sUnion.mp hq
    exact hf.contDiffAt (hU.mem_nhds hqU)

theorem laplace_pullback_normalizedBall {g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ E) {e : (Frame dim)} {r : (X dim) → ℝ} {y z : (X dim)} (hr : 0 < r y)
    {U : Set (X dim)} (hU : IsOpen U) (hz : z ∈ U)
    (hg : SmoothMetric U (fun w => movingBallMetric g E e r (y,w))) (u : (X dim) → ℝ) :
    laplace (pullbackMetric g (normalBallChartMap E e y (r y))) u z =
      ((r y)^2)⁻¹ * laplace (fun w => movingBallMetric g E e r (y,w)) u z := by
  have h := laplace_const_smul (pow_ne_zero 2 hr.ne') (hg.2 z hz).det_pos.ne'
    (fun i j => ((hg.1 i j).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) u
  rw [pullbackMetric_normalBallChartMap hE]
  exact h

end CalderonN
