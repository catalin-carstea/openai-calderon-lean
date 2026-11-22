module

public import Proof.CalderonN.NormalBallRooms

import Proof.CalderonN.SphereCoordinates
import Proof.CalderonN.FrameOperators
import Proof.CalderonN.FramePullback
import Proof.CalderonN.MetricPair
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem continuousAt_frameEndpoint {T : Type*} [TopologicalSpace T]
    {E : (X dim) × (X dim) → (X dim)} (hE : Continuous E) {e : (Frame dim)} {t : T}
    {y w : T → (X dim)} (hy : ContinuousAt y t) (hw : ContinuousAt w t)
    (he : ∀ i, ContinuousAt (fun z => e z i) (y t))
    {s : T → ℝ} (hs : ContinuousAt s t) :
    ContinuousAt (fun z => (E (y z,s z • frameVector e (y z) (w z)),y z)) t := by
  have hFrame : ContinuousAt (fun z => frameVector e (y z) (w z)) t := by
    unfold frameVector ContinuousAt
    exact tendsto_finsetSum _ (fun i _ =>
      (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.comp hw).smul ((he i).comp hy)))
  exact (hE.continuousAt.comp (hy.prodMk (hs.smul hFrame))).prodMk hy

theorem closedBallImage_eq_scaledFrameImage (γ : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : ℝ} (hr : 0 < r) :
    closedBallImage γ E (fun _ => r) y =
      (fun w => E (y,r • frameVector e y w)) '' closedBall (0 : (X dim)) 1 := by
  rw [closedBallImage_eq_frameImage γ E e y he hr.le]
  ext x
  have hlin (a : ℝ) (w : (X dim)) : frameVector e y (a • w) = a • frameVector e y w :=
    by simp only [← frameVectorLinear_apply, map_smul]
  constructor
  · rintro ⟨w,hw,rfl⟩
    refine ⟨r⁻¹ • w,mem_closedBall_zero_iff.mpr ?_,?_⟩
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      calc
        r⁻¹ * ‖w‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hw) (by positivity)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · dsimp only
      rw [hlin,smul_inv_smul₀ hr.ne']
  · rintro ⟨w,hw,rfl⟩
    refine ⟨r • w,mem_closedBall_zero_iff.mpr ?_,?_⟩
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
      exact mul_le_of_le_one_right hr.le (mem_closedBall_zero_iff.mp hw)
    · dsimp only
      rw [hlin]

/-- A compact normal ball that lies in an open region stays in that
region for nearby centers and continuously varying positive radius. -/
theorem eventually_closedBallImage_subset
    {E : (X dim) × (X dim) → (X dim)} (hE : Continuous E) {γ : (MetricField dim)} {e : (Frame dim)} {Y U : Set (X dim)}
    (hU : IsOpen U) {y₀ : (X dim)} (hY : Y ∈ 𝓝 y₀)
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousAt (fun y => e y i) y₀) {r : (X dim) → ℝ}
    (hrc : ContinuousAt r y₀) (hr : 0 < r y₀)
    (hsub : closedBallImage γ E r y₀ ⊆ U) :
    ∀ᶠ y in 𝓝 y₀, closedBallImage γ E r y ⊆ U := by
  have h₀ := mem_of_mem_nhds hY
  have hImage := (isCompact_closedBall (0 : (X dim)) 1).eventually_forall_of_forall_eventually
    (P := fun y w => E (y,r y • frameVector e y w) ∈ U) (x₀ := y₀) (fun w hw => by
      have hm : E (y₀,r y₀ • frameVector e y₀ w) ∈ U := by
        apply hsub
        change _ ∈ closedBallImage γ E (fun _ => r y₀) y₀
        rw [closedBallImage_eq_scaledFrameImage γ E e y₀ (he y₀ h₀) hr]
        exact ⟨w,hw,rfl⟩
      have hF := (continuousAt_frameEndpoint hE continuous_fst.continuousAt
        continuous_snd.continuousAt (t := (y₀,w)) hec (hrc.comp continuous_fst.continuousAt)).fst
      exact hF.preimage_mem_nhds (hU.mem_nhds hm))
  filter_upwards [hY,hrc.eventually (lt_mem_nhds hr),hImage] with y hy hry hIm
  change closedBallImage γ E (fun _ => r y) y ⊆ U
  rw [closedBallImage_eq_scaledFrameImage γ E e y (he y hy) hry]
  exact image_subset_iff.mpr hIm

/-- The open physical kernel region contains a shell of positive width
about the literal sphere, uniformly for centers in a neighborhood. -/
theorem exists_eventually_normalShellRoom_subset
    {Y : Set (X dim)} {γ : (MetricField dim)} {ρ : ℝ} {E V : (X dim) × (X dim) → (X dim)}
    (hE : Continuous E)
    (hInv : ∀ q ∈ normalPairDomain Y γ ρ E,
      (q.2,V q) ∈ normalVelocityDomain Y γ ρ ∧ E (q.2,V q) = q.1)
    {O : Set ((X dim) × (X dim))} (hO : IsOpen O) {y₀ : (X dim)}
    {e : (Frame dim)} (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (hec : ∀ i, ContinuousAt (fun y => e y i) y₀) {r : (X dim) → ℝ}
    (hrc : ContinuousAt r y₀) (hr : 0 < r y₀) (hρ : r y₀ < ρ)
    (hSphere : ∀ w : ↥(standardSphere dim), (E (y₀,r y₀ • frameVector e y₀ w),y₀) ∈ O) :
    ∃ η > 0, η < r y₀ ∧ r y₀ + η < ρ ∧
      ∀ᶠ y in 𝓝 y₀, 0 < r y - η ∧ r y + η < ρ ∧
        ∀ x ∈ normalShellRoom (normalPairDomain Y γ ρ E) γ V y (r y-η) (r y+η), (x,y) ∈ O := by
  let F (p : (X dim) × ℝ) (w : (X dim)) := (E (p.1,(r p.1+p.2) • frameVector e p.1 w),p.1)
  have hUniform := (isCompact_sphere (0 : (X dim)) 1).eventually_forall_of_forall_eventually
    (P := fun p w => F p w ∈ O) (x₀ := (y₀,(0 : ℝ))) (fun w hw => by
      have hy : ContinuousAt (fun p : ((X dim) × ℝ) × (X dim) => p.1.1) ((y₀,0),w) :=
        continuous_fst.fst.continuousAt
      have hR : ContinuousAt (fun p : ((X dim) × ℝ) × (X dim) => r p.1.1+p.1.2) ((y₀,0),w) :=
        (hrc.comp hy).add continuous_fst.snd.continuousAt
      have hF : ContinuousAt (fun p => F p.1 p.2) ((y₀,0),w) :=
        continuousAt_frameEndpoint hE hy continuous_snd.continuousAt hec hR
      exact hF.preimage_mem_nhds (hO.mem_nhds (by simpa only [F,add_zero] using hSphere ⟨w,hw⟩)))
  change {p : (X dim) × ℝ | ∀ w ∈ sphere (0 : (X dim)) 1, F p w ∈ O} ∈ 𝓝 (y₀,0) at hUniform
  rw [nhds_prod_eq,Filter.mem_prod_iff] at hUniform
  obtain ⟨U,hU,J,hJ,hIn⟩ := hUniform
  obtain ⟨c,hc,hcJ⟩ := Metric.mem_nhds_iff.mp hJ
  let η := min (c/2) (min (r y₀/2) ((ρ-r y₀)/2))
  have hη : 0 < η := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hηc : η < c := (min_le_left _ _).trans_lt (by linarith)
  have hηr : η < r y₀ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hηρ : r y₀+η < ρ := by
    have he : η ≤ (ρ-r y₀)/2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨η,hη,hηr,hηρ,?_⟩
  have hl : ∀ᶠ y in 𝓝 y₀, 0 < r y - η :=
    (hrc.sub continuousAt_const).eventually (lt_mem_nhds (sub_pos.mpr hηr))
  have hu : ∀ᶠ y in 𝓝 y₀, r y + η < ρ :=
    (hrc.add continuousAt_const).eventually (gt_mem_nhds hηρ)
  filter_upwards [hU,hl,hu] with y hy hpos hcap
  refine ⟨hpos,hcap,?_⟩
  rintro x ⟨hpair,hmin,hmax⟩
  obtain ⟨hvel,hend⟩ := hInv (x,y) hpair
  let u := frameCoordinates γ y (e y) (V (x,y))
  have hsq : ‖u‖^2 = normalRadialSq γ V (x,y) := norm_frameCoordinates_sq _ _ _ _ (he y hvel.1)
  have hlow : r y-η < ‖u‖ := (sq_lt_sq₀ hpos.le (norm_nonneg _)).mp (by rw [hsq]; exact hmin)
  have hhigh : ‖u‖ < r y+η := (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp (by rw [hsq]; exact hmax)
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (hpos.trans hlow).ne'
  let t := ‖u‖-r y
  have ht : t ∈ J := hcJ (mem_ball_zero_iff.mpr (by
    rw [Real.norm_eq_abs]
    exact abs_lt.mpr ⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩))
  let w := sphereDirection u
  have hKnown := hIn (show (y,t) ∈ U ×ˢ J from ⟨hy,ht⟩) (w : (X dim)) w.property
  have hF : F (y,t) w = (x,y) := by
    change (E (y,(r y+t) • frameVector e y (w : (X dim))),y) = (x,y)
    congr 1
    change E (y,(r y+(‖u‖-r y)) • frameVector e y (sphereDirection u : (X dim))) = x
    rw [show r y+(‖u‖-r y) = ‖u‖ by ring,sphereDirection_val hu0]
    have hlin : frameVector e y (‖u‖⁻¹ • u) = ‖u‖⁻¹ • frameVector e y u :=
      by simp only [← frameVectorLinear_apply, map_smul]
    rw [hlin,smul_inv_smul₀ (norm_ne_zero_iff.mpr hu0)]
    rw [show frameVector e y u = V (x,y) from frameVector_frameCoordinates _ _ _ _ (he y hvel.1)]
    exact hend
  exact hF ▸ hKnown

/-- A fixed compact support in the open moving normal ball remains in
the open moving ball for nearby centers. -/
theorem eventually_subset_normalBallRoom {N : Set ((X dim) × (X dim))} (hN : IsOpen N)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {V : (X dim) × (X dim) → (X dim)} (hV : ContinuousOn V N)
    {K : Set (X dim)} (hK : IsCompact K) {r : (X dim) → ℝ} {y₀ : (X dim)} (hr : ContinuousAt r y₀)
    (hsub : K ⊆ normalBallRoom N γ V y₀ (r y₀)) :
    ∀ᶠ y in 𝓝 y₀, K ⊆ normalBallRoom N γ V y (r y) := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hc : Continuous (fun q : (X dim) × (X dim) => (q.2,q.1)) := continuous_snd.prodMk continuous_fst
  have hPair : ∀ᶠ q : (X dim) × (X dim) in 𝓝 (y₀,x), (q.2,q.1) ∈ N :=
    hc.continuousAt.preimage_mem_nhds (hN.mem_nhds (hsub hx).1)
  have hc' : ContinuousAt (fun q : (X dim) × (X dim) => (q.2,q.1)) (y₀,x) := hc.continuousAt
  have hcN : ContinuousAt (normalRadialSq γ V) (x,y₀) :=
    (continuousOn_normalRadialSq hγ hV).continuousAt (hN.mem_nhds (hsub hx).1)
  have hRad : ContinuousAt (fun q : (X dim) × (X dim) => normalRadialSq γ V (q.2,q.1)) (y₀,x) :=
    hcN.comp_of_eq hc' rfl
  have hLt : ∀ᶠ q : (X dim) × (X dim) in 𝓝 (y₀,x), normalRadialSq γ V (q.2,q.1) - (r q.1)^2 < 0 :=
    (hRad.sub ((hr.comp continuous_fst.continuousAt).pow 2)).eventually (gt_mem_nhds (sub_neg.mpr (hsub hx).2))
  exact (hPair.and hLt).mono fun q hq => (show q.2 ∈ normalBallRoom N γ V q.1 (r q.1) from
    ⟨hq.1,sub_neg.mp hq.2⟩)

end CalderonN
