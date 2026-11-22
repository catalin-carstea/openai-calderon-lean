module

public import Proof.CalderonN.HorizontalBundleDerivative
public import Proof.CalderonN.TracePairUniqueness
public import Proof.CalderonN.TraceCutoffAlgebra
public import Proof.CalderonN.MovingTraceDuality

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Adapted from `BundleTraceLinearity` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem eqOn_bundle_of_eqOn_frames
    {Y : Set (X dim)} {γ : (MetricField dim)} {e : (Frame dim)}
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {F : Type*} {u v : (X dim) × (X dim) → F}
    (h : ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
      u (y,frameVector e y w) = v (y,frameVector e y w)) : EqOn u v (bundle Y γ) := by
  intro q hq
  let w := frameCoordinates γ q.1 (e q.1) q.2
  have hN : ‖w‖^2 = 1 := (norm_frameCoordinates_sq γ q.1 q.2 (e q.1) (he q.1 hq.1)).trans hq.2
  have hS : w ∈ (standardSphere dim) := mem_sphere_zero_iff_norm.mpr (by nlinarith [norm_nonneg w])
  have hw : frameVector e q.1 w = q.2 :=
    frameVector_frameCoordinates γ q.1 q.2 (e q.1) (he q.1 hq.1)
  have hf := h q.1 hq.1 ⟨w,hS⟩
  change u (q.1,frameVector e q.1 w) = v (q.1,frameVector e q.1 w) at hf
  rwa [hw] at hf

theorem smoothNear_bundle_slice
    {Y : Set (X dim)} {γ : (MetricField dim)} {v : (Field dim)} (hv : smoothNear v (bundle Y γ))
    {y : (X dim)} (hy : y ∈ Y) : smoothNear (fun w => v (y,w)) (sphereAt γ y) := by
  obtain ⟨U,hU,hSub,hvU⟩ := hv
  have hh : ContDiff ℝ ∞ (Prod.mk y : (X dim) → (X dim) × (X dim)) := contDiff_const.prodMk contDiff_id
  exact ⟨(Prod.mk y) ⁻¹' U,hU.preimage hh.continuous,fun _ hw => hSub ⟨hy,hw⟩,
    hvU.comp hh.contDiffOn (fun _ h => h)⟩

theorem differentiableAt_of_smoothNear_bundle
    {Y : Set (X dim)} {γ : (MetricField dim)} {v : (Field dim)} (hv : smoothNear v (bundle Y γ))
    {q : (X dim) × (X dim)} (hq : q ∈ bundle Y γ) : DifferentiableAt ℝ v q := by
  obtain ⟨U,hU,hSub,hvU⟩ := hv
  exact (hvU.contDiffAt (hU.mem_nhds (hSub hq))).differentiableAt (by simp)

theorem continuous_framed_slice {γ : (MetricField dim)} {e : (Frame dim)} {y : (X dim)}
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {v : (X dim) → ℂ} (hv : smoothNear v (sphereAt γ y)) :
    Continuous (fun w : ↥(standardSphere dim) => v (frameVector e y w)) := by
  obtain ⟨S,_,hS,hvS⟩ := hv
  exact hvS.continuousOn.comp_continuous ((continuous_frameVector e y).comp continuous_subtype_val)
    (fun w => hS (frameVector_mem_sphere γ e y he w))

private theorem continuous_framed_harmonic_trace
    {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} (hE : Continuous E)
    {e : (Frame dim)} {r : (X dim) → ℝ} {y : (X dim)}
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {u : (X dim) → ℝ} (hu : HarmonicOnBall g (closedBallImage γ E r y) u) :
    Continuous (fun w : ↥(standardSphere dim) => u (endpoint E r (y,frameVector e y w))) := by
  obtain ⟨S,_,hS,huS⟩ := hu.1
  have hFrame : Continuous (fun w : ↥(standardSphere dim) => frameVector e y w) :=
    (continuous_frameVector e y).comp continuous_subtype_val
  apply huS.continuousOn.comp_continuous (hE.comp (continuous_const.prodMk (hFrame.const_smul (r y))))
  intro w
  exact hS (endpoint_mem_closedBallImage (frameVector_mem_sphere γ e y he w))

/-- The protected adjoint is linear on smooth sphere data. This follows
from the adjoint identity and Dirichlet solvability on the same sphere. -/
theorem adjointField_linear_combo_on_bundle
    {Y : Set (X dim)} {γ g : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    {e : (Frame dim)} {r : (X dim) → ℝ} (hr : ContDiff ℝ ∞ r) (hDir : Dirichlet Y γ g E r)
    (he : ∀ y ∈ Y, ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {A : (TraceAdjoint dim)} (hA : IsMovingTraceAdjoint Y γ g e E r A)
    (i : (I dim)) {F U V : (Field dim)}
    (hF : smoothNear F (bundle Y γ)) (hU : smoothNear U (bundle Y γ))
    (hV : smoothNear V (bundle Y γ))
    (a b : (X dim) → ℂ) (hEq : EqOn F (fun p => a p.1*U p+b p.1*V p) (bundle Y γ)) :
    EqOn (adjointField A i F)
      (fun p => a p.1*adjointField A i U p+b p.1*adjointField A i V p) (bundle Y γ) := by
  apply eqOn_bundle_of_eqOn_frames he
  intro y hy
  let J (w : (X dim)) := adjointField A i F (y,w)
  let K (w : (X dim)) := adjointField A i U (y,w)
  let L (w : (X dim)) := adjointField A i V (y,w)
  let M (w : (X dim)) := J w-(a y*K w+b y*L w)
  have hJ : smoothNear J (sphereAt γ y) := smoothNear_bundle_slice (hA i F hF).1 hy
  have hK : smoothNear K (sphereAt γ y) := smoothNear_bundle_slice (hA i U hU).1 hy
  have hL : smoothNear L (sphereAt γ y) := smoothNear_bundle_slice (hA i V hV).1 hy
  have hM : smoothNear M (sphereAt γ y) := by
    obtain ⟨S,hS,hSJ,hJS⟩ := hJ
    obtain ⟨T,hT,hTK,hKT⟩ := hK
    obtain ⟨P,hP,hPL,hLP⟩ := hL
    refine ⟨S ∩ (T ∩ P),hS.inter (hT.inter hP),fun z hz => ⟨hSJ hz,hTK hz,hPL hz⟩,?_⟩
    exact (hJS.mono inter_subset_left).sub
      ((contDiffOn_const.mul (hKT.mono (inter_subset_right.trans inter_subset_left))).add
        (contDiffOn_const.mul (hLP.mono (inter_subset_right.trans inter_subset_right))))
  have hZero := complex_eq_zero_on_frame_of_dirichlet_pairings hy hDir e (he y hy) hM (by
    intro u hu
    let f (w : ↥(standardSphere dim)) := endpoint E r (y,frameVector e y w)
    let c (w : ↥(standardSphere dim)) := (u (f w) : ℂ)
    let d (w : ↥(standardSphere dim)) := Complex.ofReal
      (horizontal γ (fun q => u (endpoint E r q)) y (frameVector e y w) (axis i))
    let j (w : ↥(standardSphere dim)) := J (frameVector e y w)*c w
    let k (w : ↥(standardSphere dim)) := K (frameVector e y w)*c w
    let l (w : ↥(standardSphere dim)) := L (frameVector e y w)*c w
    let f' (w : ↥(standardSphere dim)) := F (y,frameVector e y w)*d w
    let u' (w : ↥(standardSphere dim)) := U (y,frameVector e y w)*d w
    let v' (w : ↥(standardSphere dim)) := V (y,frameVector e y w)*d w
    have hc : Continuous c := Complex.continuous_ofReal.comp
      (continuous_framed_harmonic_trace hE.continuous (he y hy) hu)
    let : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp (isCompact_sphere (0:(X dim)) 1)
    have hJint : Integrable j (sphereProbability dim) :=
      ((continuous_framed_slice (he y hy) hJ).mul hc).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hKint : Integrable k (sphereProbability dim) :=
      ((continuous_framed_slice (he y hy) hK).mul hc).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hLint : Integrable l (sphereProbability dim) :=
      ((continuous_framed_slice (he y hy) hL).mul hc).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hPair (H : (Field dim)) (hH : smoothNear H (bundle Y γ)) :
        (∫ w : ↥(standardSphere dim), adjointField A i H (y,frameVector e y w)*c w ∂(sphereProbability dim)) =
          ∫ w : ↥(standardSphere dim), H (y,frameVector e y w)*d w ∂(sphereProbability dim) := by
      have h := (hA i H hH).2 y hy u hu
      change (∫ w : ↥(standardSphere dim), adjointField A i H (y,frameVector e y w)*c w ∂(sphereProbability dim)) =
        ∫ w : ↥(standardSphere dim), H (y,frameVector e y w)*d w ∂(sphereProbability dim) at h
      exact h
    have hP₁ : (∫ w, j w ∂(sphereProbability dim)) = ∫ w, f' w ∂(sphereProbability dim) := hPair F hF
    have hP₂ : (∫ w, k w ∂(sphereProbability dim)) = ∫ w, u' w ∂(sphereProbability dim) := hPair U hU
    have hP₃ : (∫ w, l w ∂(sphereProbability dim)) = ∫ w, v' w ∂(sphereProbability dim) := hPair V hV
    have he' (w : ↥(standardSphere dim)) : f' w = a y*u' w+b y*v' w := by
      have hw : (y,frameVector e y w) ∈ bundle Y γ := ⟨hy,frameVector_mem_sphere γ e y (he y hy) w⟩
      change F (y,frameVector e y w)*d w = _
      rw [hEq hw,add_mul,mul_assoc,mul_assoc]
    have hd : Continuous d := by
      obtain ⟨S,hS,hCover,huS⟩ := hu.1
      have hEnd : ContDiff ℝ ∞ (endpoint E r) :=
        hE.comp (contDiff_fst.prodMk ((hr.comp contDiff_fst).smul contDiff_snd))
      let T := (endpoint E r) ⁻¹' S
      have hT : IsOpen T := hS.preimage hEnd.continuous
      have htr : ContDiffOn ℝ ∞ (fun q => u (endpoint E r q)) T :=
        huS.comp hEnd.contDiffOn (fun _ hq => hq)
      have hH := (htr.fderiv_of_isOpen (m := ∞) hT (by simp)).clm_apply
        ((contDiffOn_horizontalDirection isOpen_univ hγ i).mono (fun _ _ => ⟨mem_univ _,mem_univ _⟩))
      let P (w : ↥(standardSphere dim)) := (y,frameVector e y w)
      have hP : Continuous P := continuous_const.prodMk ((continuous_frameVector e y).comp continuous_subtype_val)
      have hPT (w : ↥(standardSphere dim)) : P w ∈ T :=
        hCover (endpoint_mem_closedBallImage (frameVector_mem_sphere γ e y (he y hy) w))
      have hRC : Continuous (fun w : ↥(standardSphere dim) => horizontal γ (fun q => u (endpoint E r q))
          y (frameVector e y w) (axis i)) := hH.continuousOn.comp_continuous hP hPT
      exact Complex.continuous_ofReal.comp hRC
    have hUi : Integrable u' (sphereProbability dim) :=
      (((continuous_framed_slice (he y hy) (smoothNear_bundle_slice hU hy)).mul hd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hVi : Integrable v' (sphereProbability dim) :=
      (((continuous_framed_slice (he y hy) (smoothNear_bundle_slice hV hy)).mul hd)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have heq : (∫ w : ↥(standardSphere dim), M (frameVector e y w)*c w ∂(sphereProbability dim)) =
        (∫ w, j w ∂(sphereProbability dim)) -
          (a y * (∫ w, k w ∂(sphereProbability dim)) + b y * (∫ w, l w ∂(sphereProbability dim))) := by
      have hh : (fun w : ↥(standardSphere dim) => M (frameVector e y w)*c w) =
          j - (fun w => a y*k w+b y*l w) := by
        funext w
        simp only [M,j,k,l,Pi.sub_apply]
        ring
      rw [hh]
      change (∫ w, j w - (a y*k w+b y*l w) ∂(sphereProbability dim)) = _
      have hKi := hKint.const_mul (a y)
      have hLi := hLint.const_mul (b y)
      calc
        _ = (∫ w, j w ∂(sphereProbability dim)) - ∫ w, (a y*k w+b y*l w) ∂(sphereProbability dim) :=
          integral_sub hJint (hKi.add hLi)
        _ = _ := by rw [integral_add hKi hLi,integral_const_mul,integral_const_mul]
    change (∫ w : ↥(standardSphere dim), M (frameVector e y w)*c w ∂(sphereProbability dim)) = 0
    rw [heq,hP₁,hP₂,hP₃]
    simp_rw [he']
    rw [integral_add (hUi.const_mul _) (hVi.const_mul _),integral_const_mul,integral_const_mul,sub_self])
  intro w
  exact sub_eq_zero.mp (hZero w)

end CalderonN
