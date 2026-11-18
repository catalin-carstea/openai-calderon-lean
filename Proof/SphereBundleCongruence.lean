import Proof.HorizontalRepresentative
import Proof.AngularEnergyDensity

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma degreePart_congr_frameVector (g : MetricField) (e : Frame) (k : ℕ) (y : X) (u v : X → ℂ)
    (h : ∀ z : UnitSphere,u (frameVector e y z.val) = v (frameVector e y z.val)) (w : X) :
    degreePart g e k y u w = degreePart g e k y v w := by
  unfold degreePart
  congr 1
  apply sphereAverage_congr_frameVector
  intro z
  rw [h z]

lemma sobolevSq_congr_frameVector (g : MetricField) (e : Frame) (s : ℝ) (y : X) (u v : X → ℂ)
    (h : ∀ z : UnitSphere,u (frameVector e y z.val) = v (frameVector e y z.val)) :
    sobolevSq g e s y u = sobolevSq g e s y v := by
  unfold sobolevSq
  apply tsum_congr
  intro k
  congr 1
  apply fiberSq_congr_frameVector
  intro w
  exact degreePart_congr_frameVector g e k y u v h _

/-- Horizontal derivatives of smooth physical fields depend only on their restrictions
    to the open family of metric unit spheres. -/
theorem horizontal_eq_of_eqOn_frame_spheres {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (φ ψ : Field) (hφ : smoothNear φ (bundle Y g)) (hψ : smoothNear ψ (bundle Y g))
    (hEq : ∀ y ∈ Y,∀ v : UnitSphere,φ (y,frameVector e y v.val) = ψ (y,frameVector e y v.val))
    {y : X} (hy : y ∈ Y) (z : UnitSphere) (a : X) :
    horizontal g φ y (frameVector e y z.val) a = horizontal g ψ y (frameVector e y z.val) a := by
  have he' (i : I) := ((he i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hpoint : (y,frameVector e y z.val) ∈ bundle Y g :=
    ⟨hy,frameVector_mem_sphere g e y (hframe y hy) z⟩
  have hdφ := hφ.differentiableAt hpoint
  have hdψ := hψ.differentiableAt hpoint
  rw [horizontal_eq_frame_pullback g e φ y z.val a he' (hframe y hy) hdφ,
    horizontal_eq_frame_pullback g e ψ y z.val a he' (hframe y hy) hdψ]
  exact fderiv_covariant_eq_of_eqOn_spheres hY hy z _ _
    (differentiableAt_frame_pullback e φ y z.val he' hdφ)
    (differentiableAt_frame_pullback e ψ y z.val he' hdψ) hEq _
    (frameConnection_skew hY h hK e he hframe hy a) a

theorem energySq_congr_smooth_frame_spheres {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (r : X → ℝ) (φ ψ : Field) (hφ : smoothNear φ (bundle Y g)) (hψ : smoothNear ψ (bundle Y g))
    (hEq : ∀ y ∈ Y,∀ v : UnitSphere,φ (y,frameVector e y v.val) = ψ (y,frameVector e y v.val)) :
    energySq Y g e r φ = energySq Y g e r ψ := by
  rw [energySq_eq_integral_density,energySq_eq_integral_density]
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  have hH (i : I) (v : UnitSphere) := horizontal_eq_of_eqOn_frame_spheres hY h hK e he hframe φ ψ hφ hψ hEq hy v (e y i)
  have hf (i : I) := fiberSq_congr_frameVector e y
    (fun w => horizontal g φ y w (e y i)) (fun w => horizontal g ψ y w (e y i)) (hH i)
  have hs (i : I) := sobolevSq_congr_frameVector g e (1/2) y
    (fun w => horizontal g φ y w (e y i)) (fun w => horizontal g ψ y w (e y i)) (hH i)
  unfold physicalEnergyDensity
  simp_rw [hf,hs,sobolevSq_congr_frameVector g e 1 y (fun w => φ (y,w)) (fun w => ψ (y,w)) (hEq y hy),
    sobolevSq_congr_frameVector g e (3/2) y (fun w => φ (y,w)) (fun w => ψ (y,w)) (hEq y hy)]

end ShrinkingSpheres
