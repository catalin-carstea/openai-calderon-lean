module

public import Proof.CalderonN.MovingBallFamilies
public import Proof.CalderonN.NormalBallHarmonic

import Proof.CalderonN.CrossProductWeak
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Adapted from `ActualMovingTraceAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Apply the fixed-ball real adjoint to the two components of the datum
in the angular frame, and restore the physical velocity's radius factor. -/
@[expose] def actualMovingTraceAdjoint
    (γ g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ) : (TraceAdjoint dim) :=
  fun i y φ w =>
    let m := movingBallMetric g E e r
    let V := movingBallScaledVelocity γ E e r i
    let p := movingBallToFrame γ e (y,w)
    let a := parametricBallVelocityAdjoint m V (fun z => (φ (frameVector e y z.2)).re) p
    let b := parametricBallVelocityAdjoint m V (fun z => (φ (frameVector e y z.2)).im) p
    ⟨(r y)⁻¹*a,(r y)⁻¹*b⟩

@[expose] def realMovingVelocityDatum (e : (Frame dim)) (v : (Field dim)) (q : (X dim) × (X dim)) : ℝ :=
  (v (movingBallFromFrame e q)).re

@[expose] def imagMovingVelocityDatum (e : (Frame dim)) (v : (Field dim)) (q : (X dim) × (X dim)) : ℝ :=
  (v (movingBallFromFrame e q)).im

theorem adjointField_actualMovingTraceAdjoint
    (γ g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (r : (X dim) → ℝ)
    (i : (I dim)) (v : (Field dim)) (q : (X dim) × (X dim)) :
    adjointField (actualMovingTraceAdjoint γ g E e r) i v q =
      ⟨(r q.1)⁻¹ * parametricBallVelocityAdjoint (movingBallMetric g E e r)
          (movingBallScaledVelocity γ E e r i) (realMovingVelocityDatum e v) (movingBallToFrame γ e q),
        (r q.1)⁻¹ * parametricBallVelocityAdjoint (movingBallMetric g E e r)
          (movingBallScaledVelocity γ E e r i) (imagMovingVelocityDatum e v) (movingBallToFrame γ e q)⟩ := by
  unfold adjointField actualMovingTraceAdjoint
  congr 2

private theorem contDiffOn_complex_mk {S : Set ((X dim) × (X dim))} {a b : (X dim) × (X dim) → ℝ}
    (ha : ContDiffOn ℝ ∞ a S) (hb : ContDiffOn ℝ ∞ b S) :
    ContDiffOn ℝ ∞ (fun q => (⟨a q,b q⟩ : ℂ)) S := by
  have h := (Complex.ofRealCLM.contDiff.comp_contDiffOn ha).add
    (contDiffOn_const (c := Complex.I) |>.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hb))
  refine h.congr ?_
  intro q _
  apply Complex.ext <;> simp

set_option maxHeartbeats 1700000 in
theorem smoothNear_actualMovingTraceAdjoint
    {Y : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {e : (Frame dim)} {r : (X dim) → ℝ}
    (hγ : SmoothMetric univ γ) (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hFrame : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y)
    {U : Set ((X dim) × (X dim))} (hU : IsOpen U) (hCU : Y ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => movingBallMetric g E e r q i j) U)
    (hPos : ∀ q ∈ U, (movingBallMetric g E e r q).PosDef)
    {i : (I dim)} (hVelocity : ContDiffOn ℝ ∞ (movingBallScaledVelocity γ E e r i) U)
    {v : (Field dim)} (hv : smoothNear v (bundle Y γ)) :
    smoothNear (adjointField (actualMovingTraceAdjoint γ g E e r) i v) (bundle Y γ) := by
  let P := movingBallToFrame γ e
  let F := movingBallFromFrame e
  let m := movingBallMetric g E e r
  let V := movingBallScaledVelocity γ E e r i
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hP : ContDiff ℝ ∞ P := contDiff_movingBallToFrame hγ he
  have hF : ContDiff ℝ ∞ F := contDiff_movingBallFromFrame he
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  obtain ⟨S,hS,hBS,hvS⟩ := hv
  let T := U ∩ F ⁻¹' S
  have hT : IsOpen T := hU.inter (hS.preimage hF.continuous)
  have hST : Y ×ˢ (standardSphere dim) ⊆ T := fun _ hq =>
    ⟨hCU ⟨hq.1,sphere_subset_closedBall hq.2⟩,hBS (movingBallFromFrame_sphere hFrame hq)⟩
  have hSliced : ContDiffOn ℝ ∞ (v ∘ F) T := hvS.comp hF.contDiffOn (fun _ hq => hq.2)
  have hRe : ContDiffOn ℝ ∞ (realMovingVelocityDatum e v) T :=
    Complex.reCLM.contDiff.comp_contDiffOn hSliced
  have hIm : ContDiffOn ℝ ∞ (imagMovingVelocityDatum e v) T :=
    Complex.imCLM.contDiff.comp_contDiffOn hSliced
  refine smoothNear_of_open_cover fun q hq => ?_
  have hq' := movingBallToFrame_bundle hFrame hq
  have hCq : {q.1} ×ˢ closedBall (0 : (X dim)) 1 ⊆ U := fun _ hp =>
    hCU ⟨mem_singleton_iff.mp hp.1 ▸ hq.1,hp.2⟩
  have hSq : {q.1} ×ˢ (standardSphere dim) ⊆ T := fun _ hp =>
    hST ⟨mem_singleton_iff.mp hp.1 ▸ hq.1,hp.2⟩
  obtain ⟨J,hJ,hqJ,ha⟩ := exists_contDiffOn_parametricBallVelocityAdjoint hU hT q.1 hCq hSq hg hPos
    (hVelocity.mono inter_subset_left) hRe
  obtain ⟨K,hK,hqK,hb⟩ := exists_contDiffOn_parametricBallVelocityAdjoint hU hT q.1 hCq hSq hg hPos
    (hVelocity.mono inter_subset_left) hIm
  let L := (J ∩ K) ×ˢ N
  let W := P ⁻¹' L ∩ {q | 0 < r q.1}
  have hW : IsOpen W := ((hJ.inter hK).prod hN |>.preimage hP.continuous).inter
    (isOpen_lt continuous_const (hr.continuous.comp continuous_fst))
  have hqN : (P q).2 ∈ N := by
    change (P q).2 ≠ 0
    intro hz
    have hn := mem_sphere_zero_iff_norm.mp hq'.2
    change ‖(P q).2‖ = 1 at hn
    simp [hz] at hn
  have hMap₁ : MapsTo P W (J ×ˢ N) := fun _ hp => ⟨hp.1.1.1,hp.1.2⟩
  have hMap₂ : MapsTo P W (K ×ˢ N) := fun _ hp => ⟨hp.1.1.2,hp.1.2⟩
  have hR' : ContDiffOn ℝ ∞ (fun q : (X dim) × (X dim) => (r q.1)⁻¹) W :=
    ((hr.comp contDiff_fst).contDiffOn.inv (fun _ h => h.2.ne'))
  refine ⟨W,hW,⟨⟨⟨hqJ,hqK⟩,hqN⟩,hR q.1 hq.1⟩,?_⟩
  exact (contDiffOn_complex_mk (hR'.mul (ha.comp hP.contDiffOn hMap₁))
    (hR'.mul (hb.comp hP.contDiffOn hMap₂))).congr
      (fun p _ => adjointField_actualMovingTraceAdjoint γ g E e r i v p)

private theorem integral_complex_trace_eq
    {a b : ↥(standardSphere dim) → ℂ} {u v : ↥(standardSphere dim) → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hu : Continuous u) (hv : Continuous v)
    (hre : (∫ w, (a w).re * u w ∂(sphereProbability dim)) = ∫ w, (b w).re * v w ∂(sphereProbability dim))
    (him : (∫ w, (a w).im * u w ∂(sphereProbability dim)) = ∫ w, (b w).im * v w ∂(sphereProbability dim)) :
    (∫ w, a w * (u w : ℂ) ∂(sphereProbability dim)) = ∫ w, b w * (v w : ℂ) ∂(sphereProbability dim) := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  have hA : Integrable (fun w => a w * (u w : ℂ)) (sphereProbability dim) :=
    (ha.mul (Complex.continuous_ofReal.comp hu)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (fun w => b w * (v w : ℂ)) (sphereProbability dim) :=
    (hb.mul (Complex.continuous_ofReal.comp hv)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _
    rw [← integral_re hA,← integral_re hB]
    simpa only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,Function.comp_apply] using hre
  · change (RCLike.im : ℂ → ℝ) _ = (RCLike.im : ℂ → ℝ) _
    rw [← integral_im hA,← integral_im hB]
    simpa only [RCLike.im_eq_complex_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_add,Function.comp_apply] using him

set_option maxHeartbeats 2400000 in
/-- The literal fixed-ball velocity adjoints implement the protected
moving-boundary pairing for every classical harmonic test. -/
theorem isMovingTraceAdjoint_actual
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {γ g : (MetricField dim)}
    (hγ : SmoothMetric univ γ) (hg : SmoothMetric univ g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hNormal : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun y => e y i))
    (hFrame : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) (hR : ∀ y ∈ Y, 0 < r y ∧ r y < ρ) :
    IsMovingTraceAdjoint Y γ g e E r (actualMovingTraceAdjoint γ g E e r) := by
  obtain ⟨U,hU,hCU,hDet,hm,hPos,hVel⟩ :=
    exists_smooth_movingBallFamilies hγ hg hE hNormal he hFrame hr hR
  intro i v hv
  let A := actualMovingTraceAdjoint γ g E e r
  have hA := smoothNear_actualMovingTraceAdjoint hγ he hFrame hr (fun y hy => (hR y hy).1)
    hU hCU hm hPos (hVel i) hv
  refine ⟨hA,?_⟩
  intro y hy u hu
  let F := normalBallChartMap E e y (r y)
  let m := movingBallMetric g E e r
  let V := movingBallScaledVelocity γ E e r i
  let ζ (w : ↥(standardSphere dim)) : (X dim) × (X dim) := (y,frameVector e y w)
  let B : Set (X dim) := (Prod.mk y) ⁻¹' U
  have hB : IsOpen B := hU.preimage (continuous_const.prodMk continuous_id)
  have hCB : closedBall (0 : (X dim)) 1 ⊆ B := fun _ hz => hCU ⟨hy,hz⟩
  obtain ⟨D,hD,hCD,_,huD,hLap⟩ := harmonicOnBall_normalBallChartMap hΩ
    (smoothMetric_restrict hg (subset_univ Ω)) hE hNormal hy (hFrame y hy) (hR y hy).1 (hR y hy).2 hu
  let J := D ∩ B
  have hJ : IsOpen J := hD.inter hB
  have hCJ : closedBall (0 : (X dim)) 1 ⊆ J := fun _ hz => ⟨hCD hz,hCB hz⟩
  have hM : SmoothMetric J (fun z => m (y,z)) :=
    smoothMetric_restrict (smoothMetric_movingBall_slice hm hPos y) inter_subset_right
  have huJ : ContDiffOn ℝ ∞ (u ∘ F) J := huD.mono inter_subset_left
  have hLapM (z : (X dim)) (hz : z ∈ ball (0 : (X dim)) 1) : laplace (fun z => m (y,z)) (u ∘ F) z = 0 := by
    have h := hLap z hz
    change laplace (pullbackMetric g F) (u ∘ F) z = 0 at h
    rw [laplace_pullback_normalizedBall hE (hR y hy).1 hJ (hCJ (ball_subset_closedBall hz)) hM] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (pow_ne_zero _ (hR y hy).1.ne'))
  obtain ⟨S,hS,hVS,hvS⟩ := hv
  let Q (z : (X dim)) : (X dim) × (X dim) := (y,frameVector e y z)
  have hcQ : ContDiff ℝ ∞ Q := by
    simpa only [Q,frameVectorL_apply_frame] using
      contDiff_const.prodMk (frameVectorL (e y)).contDiff
  let T := J ∩ (Q ⁻¹' S ∩ ({0}ᶜ : Set (X dim)))
  have hT : IsOpen T := hJ.inter ((hS.preimage hcQ.continuous).inter isClosed_singleton.isOpen_compl)
  have hST : (standardSphere dim) ⊆ T := by
    intro z hz
    refine ⟨hCJ (sphere_subset_closedBall hz),hVS ⟨hy,frameVector_mem_sphere γ e y (hFrame y hy) ⟨z,hz⟩⟩,?_⟩
    change z ≠ 0
    intro heq
    have hn := mem_sphere_zero_iff_norm.mp hz
    simp [heq] at hn
  have hT₀ : (0 : (X dim)) ∉ T := fun h => h.2.2 rfl
  have hVT : ContDiffOn ℝ ∞ (fun z => V (y,z)) T :=
    (hVel i).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz.1.2)
  have hvT : ContDiffOn ℝ ∞ (fun z => v (Q z)) T :=
    hvS.comp hcQ.contDiffOn (fun _ hz => hz.2.1)
  have hHor (w : ↥(standardSphere dim)) :
      fderiv ℝ (u ∘ F) w (V (y,w)) =
        r y * horizontal γ (fun q => u (endpoint E r q)) y (frameVector e y w) (axis i) := by
    obtain ⟨Ju,hJu,hBu,huu⟩ := hu.1
    have hx : F w ∈ closedBallImage γ E r y := by
      change F w ∈ closedBallImage γ E (fun _ => r y) y
      rw [closedBallImage_eq_scaledFrameImage γ E e y (hFrame y hy) (hR y hy).1]
      exact mem_image_of_mem _ (sphere_subset_closedBall w.property)
    exact fderiv_scaledNormalTraceVelocity hE e (hr.differentiable (by simp) y)
      ((huu.contDiffAt (hJu.mem_nhds (hBu hx))).differentiableAt (by simp))
      (axis i) (hDet (y,w) (hCU ⟨hy,sphere_subset_closedBall w.property⟩))
  let a (w : ↥(standardSphere dim)) := adjointField A i v (ζ w)
  let b (w : ↥(standardSphere dim)) := v (ζ w)
  let d (w : ↥(standardSphere dim)) := u (F w)
  let k (w : ↥(standardSphere dim)) := horizontal γ (fun q => u (endpoint E r q)) y (frameVector e y w) (axis i)
  have hζ : Continuous ζ := hcQ.continuous.comp continuous_subtype_val
  have hζB (w : ↥(standardSphere dim)) : ζ w ∈ bundle Y γ :=
    ⟨hy,frameVector_mem_sphere γ e y (hFrame y hy) w⟩
  have ha : Continuous a := by
    obtain ⟨Z,_,hZ,hAZ⟩ := hA
    exact hAZ.continuousOn.comp_continuous hζ (fun w => hZ (hζB w))
  have hb : Continuous b := hvS.continuousOn.comp_continuous hζ (fun w => hVS (hζB w))
  have hd : Continuous d := huJ.continuousOn.comp_continuous continuous_subtype_val
    (fun w => hCJ (sphere_subset_closedBall w.property))
  have hk : Continuous k := by
    have hk' : Continuous (fun w : ↥(standardSphere dim) => fderiv ℝ (u ∘ F) w (V (y,w))) :=
      (((huJ.fderiv_of_isOpen (m := ∞) hJ (by simp)).mono (show T ⊆ J from inter_subset_left)).clm_apply hVT)
        |>.continuousOn.comp_continuous continuous_subtype_val (fun w => hST w.property)
    have heq (w : ↥(standardSphere dim)) : k w = (r y)⁻¹ * fderiv ℝ (u ∘ F) w (V (y,w)) := by
      rw [hHor,← mul_assoc,inv_mul_cancel₀ (hR y hy).1.ne',one_mul]
    exact (continuous_const.mul hk').congr (by intro w; exact (heq w).symm)
  change (∫ w, a w * (d w : ℂ) ∂(sphereProbability dim)) =
    ∫ w, b w * (k w : ℂ) ∂(sphereProbability dim)
  have hReal {ψ : (X dim) × (X dim) → ℝ} {c l : ↥(standardSphere dim) → ℝ}
      (hψ : ContDiffOn ℝ ∞ (fun z => ψ (y,z)) T)
      (hc : ∀ w : ↥(standardSphere dim), c w = (r y)⁻¹ * parametricBallVelocityAdjoint m V ψ (y,w))
      (hl : ∀ w : ↥(standardSphere dim), l w = ψ (y,w)) :
      (∫ w, c w * d w ∂(sphereProbability dim)) = ∫ w, l w * k w ∂(sphereProbability dim) := by
    simp_rw [hc,hl,mul_assoc,integral_const_mul]
    change (r y)⁻¹ * (∫ w : ↥(standardSphere dim),
      parametricBallVelocityAdjoint m V ψ (y,w) * (u ∘ F) w ∂(sphereProbability dim)) = _
    rw [integral_parametricBallVelocityAdjoint y hJ hT hCJ hST inter_subset_left hT₀ hM hVT hψ huJ hLapM]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    rw [hHor]
    change (r y)⁻¹ * (ψ (y,w) * (r y * k w)) = _
    rw [mul_left_comm (ψ (y,w)),← mul_assoc,inv_mul_cancel₀ (hR y hy).1.ne',one_mul]
  have hPoint (w : ↥(standardSphere dim)) :
      a w = ⟨(r y)⁻¹ * parametricBallVelocityAdjoint m V (realMovingVelocityDatum e v) (y,w),
        (r y)⁻¹ * parametricBallVelocityAdjoint m V (imagMovingVelocityDatum e v) (y,w)⟩ := by
    change adjointField (actualMovingTraceAdjoint γ g E e r) i v (ζ w) = _
    rw [adjointField_actualMovingTraceAdjoint]
    have h := movingBallToFrame_fromFrame (γ := γ) (e := e) (w := (w : (X dim))) (hFrame y hy)
    change movingBallToFrame γ e (ζ w) = (y,(w : (X dim))) at h
    rw [h]
  apply integral_complex_trace_eq ha hb hd hk
  · exact hReal (ψ := realMovingVelocityDatum e v) (Complex.reCLM.contDiff.comp_contDiffOn hvT)
      (fun w => congrArg Complex.re (hPoint w)) (fun _ => rfl)
  · exact hReal (ψ := imagMovingVelocityDatum e v) (Complex.imCLM.contDiff.comp_contDiffOn hvT)
      (fun w => congrArg Complex.im (hPoint w)) (fun _ => rfl)

end CalderonN
