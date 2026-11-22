module

public import Proof.CalderonN.FramePullback
public import Proof.CalderonN.TestRepresentative
public import Proof.CalderonN.Curvature

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 10
open Set Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ}
open OAI.AnisotropicCalderon.SphereHarmonic

lemma smoothNear.differentiableAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (X N) × (X N) → E} {S : Set ((X N) × (X N))} (hF : smoothNear F S) {p : (X N) × (X N)} (hp : p ∈ S) :
    DifferentiableAt ℝ F p := by
  obtain ⟨V,hV,hSV,hFV⟩ := hF
  exact (hFV.contDiffAt (hV.mem_nhds (hSV hp))).differentiableAt (by simp)

/-- Agreement with a smooth standard representative preserves the actual horizontal
    derivative, because the connection is tangent to the sphere bundle. -/
theorem horizontal_eq_standard_representative {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : (X N) × (X N) → E) (hφ : smoothNear φ (bundle Y g)) (G : (X N) × (X N) → E) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : (UnitSphere N),G (y,v.val) = φ (y,frameVector e y v.val))
    {y : (X N)} (hy : y ∈ Y) (z : (UnitSphere N)) (a : (X N)) :
    horizontal g φ y (frameVector e y z.val) a =
      fderiv ℝ G (y,z.val) (a,frameAngularVector (frameConnectionCoefficient g e y a) z.val) := by
  have he' (i : (I N)) := ((he i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hdφ := hφ.differentiableAt (show (y,frameVector e y z.val) ∈ bundle Y g from
    ⟨hy,frameVector_mem_sphere g e y (hframe y hy) z⟩)
  rw [horizontal_eq_frame_pullback g e φ y z.val a he' (hframe y hy) hdφ]
  exact fderiv_covariant_eq_of_eqOn_spheres hY hy z _ G
    (differentiableAt_frame_pullback e φ y z.val he' hdφ) (hG.differentiable (by simp) _)
    (fun x hx v => (hrep x hx v).symm) _ (frameConnection_skew hY h hK e he hframe hy a) a

def horizontalField (g : (MetricField N)) (e : (Frame N)) (φ : (Field N)) (i : (I N)) : (Field N) :=
  fun p => horizontal g φ p.1 p.2 (e p.1 i)

lemma smoothNear_horizontalField {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {φ : (Field N)} (hφ : smoothNear φ (bundle Y g)) (i : (I N)) :
    smoothNear (horizontalField g e φ i) (bundle Y g) := by
  obtain ⟨V,hV,hb,hφV⟩ := hφ
  let W : Set ((X N) × (X N)) := V ∩ Prod.fst ⁻¹' Y
  have hW : IsOpen W := hV.inter (hY.preimage continuous_fst)
  refine ⟨W,hW,fun p hp => ⟨hb hp,hp.1⟩,?_⟩
  intro p hp
  have hφp := hφV.contDiffAt (hV.mem_nhds hp.1)
  have hEp : ContDiffAt ℝ ∞ (fun q : (X N) × (X N) => e q.1 i) p :=
    ((he i).contDiffAt (hY.mem_nhds hp.2)).comp p contDiffAt_fst
  have hC : ContDiffAt ℝ ∞ (fun q : (X N) × (X N) => connection g q.1 (e q.1 i) q.2) p := by
    have hc := ((h.contDiffOn_connectionBilinear hY hK).contDiffAt (hY.mem_nhds hp.2)).comp p contDiffAt_fst
    simpa only [Function.comp_apply,connectionBilinear_apply] using (hc.clm_apply hEp).clm_apply contDiffAt_snd
  exact ((hφp.fderiv_right (m:=∞) (by simp)).clm_apply (hEp.prodMk hC.neg)).contDiffWithinAt

lemma exists_unitSphere_frameVector (g : (MetricField N)) (e : (Frame N)) (y : (X N))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (w : (X N)) (hw : w ∈ sphereAt g y) : ∃ z : (UnitSphere N),frameVector e y z.val = w := by
  let z : (X N) := WithLp.toLp 2 (fun i => metricPair g y w (e y i))
  have hrec : frameVector e y z = w := by
    exact frameVector_frameCoordinates g y w (e y) hframe
  have hn : ‖z‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [pow_two]
    rw [← metricPair_frameVector g e y z z hframe,hrec]
    exact hw
  have hnorm : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
  exact ⟨⟨z,by simpa only [Metric.mem_sphere,dist_zero_right] using hnorm⟩,hrec⟩

lemma horizontal_zero_of_sphere_support {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field N)} (hφ : smoothNear φ (bundle Y g)) (S : Set (X N)) (hS : IsClosed S)
    (hzero : ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,φ (y,w) = 0)
    {y : (X N)} (hy : y ∈ Y \ S) (w : (X N)) (hw : w ∈ sphereAt g y) (a : (X N)) :
    horizontal g φ y w a = 0 := by
  obtain ⟨z,hzw⟩ := exists_unitSphere_frameVector g e y (hframe y hy.1) w hw
  rw [← hzw]
  have he' (i : (I N)) := ((he i).contDiffAt (hY.mem_nhds hy.1)).differentiableAt (by simp)
  have hdφ := hφ.differentiableAt (show (y,frameVector e y z.val) ∈ bundle Y g from
    ⟨hy.1,frameVector_mem_sphere g e y (hframe y hy.1) z⟩)
  rw [horizontal_eq_frame_pullback g e φ y z.val a he' (hframe y hy.1) hdφ]
  have hEq : ∀ x ∈ Y \ S,∀ v : (UnitSphere N),φ (x,frameVector e x v.val) = (0 : ℂ) := by
    intro x hx v
    exact hzero x hx _ (frameVector_mem_sphere g e x (hframe x hx.1) v)
  have hh := fderiv_covariant_eq_of_eqOn_spheres (hY.sdiff hS) hy z
    (fun q : (X N) × (X N) => φ (q.1,frameVector e q.1 q.2)) (fun _ => (0 : ℂ))
    (differentiableAt_frame_pullback e φ y z.val he' hdφ) (differentiableAt_const 0)
    hEq _ (frameConnection_skew hY h hK e he hframe hy.1 a) a
  simpa only [fderiv_const_apply,zero_apply] using hh

/-- Actual horizontal derivatives retain the test's compact center support. -/
theorem Test.exists_smooth_horizontal_representative {Y : Set (X N)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField N)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame N))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field N)} (hφ : Test Y g e φ) (i : (I N)) :
    ∃ S : Set (X N),IsCompact S ∧ S ⊆ Y ∧ ∃ G : (X N) × (X N) → ℂ,ContDiff ℝ ∞ G ∧
      (∀ y ∈ Y,∀ v : (UnitSphere N),G (y,v.val) = horizontal g φ y (frameVector e y v.val) (e y i)) ∧
      (∀ y ∉ S,∀ v : (UnitSphere N),G (y,v.val) = 0) := by
  obtain ⟨S,hS,hSY,hzero⟩ := hφ.2.1
  apply exists_smooth_standard_representative_of_support hY e he hframe
    (smoothNear_horizontalField hY h hK e he hφ.1 i)
  refine ⟨S,hS,hSY,?_⟩
  intro y hy w hw
  exact horizontal_zero_of_sphere_support hY h hK e he hframe hφ.1 S hS.isClosed hzero hy w hw (e y i)

end CalderonN
