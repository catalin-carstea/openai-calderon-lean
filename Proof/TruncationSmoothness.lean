import Proof.SmoothSphereKernel
import Proof.HarmonicTruncation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The literal kernel projection is locally smooth in both physical variables. A cutoff
    only supplies a global representative near the point where the derivative is taken. -/
theorem contDiffAt_degreePart {Y : Set X} (hY : IsOpen Y) (g : MetricField)
    (hg : ∀ i j,ContDiffOn ℝ ∞ (fun y => g y i j) Y) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (φ : Field) (G : X × X → ℂ) (hG : ContDiff ℝ ∞ G)
    (hrep : ∀ y ∈ Y,∀ v : UnitSphere,G (y,v.val) = φ (y,frameVector e y v.val))
    (k : ℕ) {y : X} (hy : y ∈ Y) (w : X) :
    ContDiffAt ℝ ∞ (fun p : X × X => degreePart g e k p.1 (fun v => φ (p.1,v)) p.2) (y,w) := by
  obtain ⟨η,hη,_,hone,hcomp,hsupp⟩ := (isCompact_singleton (x:=y)).exists_contDiff_cutoff hY
    (singleton_subset_iff.mpr hy)
  let g' : MetricField := fun x i j => η x*g x i j
  let e' : Frame := fun x i => η x • e x i
  have hg' (i j : I) : ContDiff ℝ ∞ (fun x => g' x i j) := by
    exact contDiff_cutoff_smul hY η (fun x => g x i j) hη (hg i j) hsupp
  have he' (i : I) : ContDiff ℝ ∞ (fun x => e' x i) :=
    contDiff_cutoff_smul hY η (fun x => e x i) hη (he i) hsupp
  let H : X × X → ℂ := fun p => ((2*(k:ℝ)+1 : ℝ) : ℂ)*
    ∫ v : UnitSphere,(legendre (metricPair g' p.1 p.2 (frameVector e' p.1 v.val)) k : ℂ)*G (p.1,v.val) ∂sphereProbability
  have hH : ContDiff ℝ ∞ H := contDiff_integrated_legendre_kernel g' hg' e' he' G hG k
  apply hH.contDiffAt.congr_of_eventuallyEq
  have hbase : ∀ᶠ x in nhds y,x ∈ Y ∧ η x = 1 := by
    filter_upwards [hY.mem_nhds hy,isOpen_interior.mem_nhds (hone (mem_singleton y))] with x hx hηx
    have hh := interior_subset hηx
    exact ⟨hx,hh⟩
  filter_upwards [(continuous_fst.tendsto (y,w)).eventually hbase] with p hp
  have hgeq : g' p.1 = g p.1 := by funext i j; simp only [g',hp.2,one_mul]
  have heeq : e' p.1 = e p.1 := by funext i; simp only [e',hp.2,one_smul]
  change (((2*(k:ℝ)+1 : ℝ) : ℂ)*∫ v : UnitSphere,
    (legendre (metricPair g p.1 p.2 (frameVector e p.1 v.val)) k : ℂ)*φ (p.1,frameVector e p.1 v.val) ∂sphereProbability) = H p
  change _ = ((2*(k:ℝ)+1 : ℝ) : ℂ)*∫ v : UnitSphere,
    (legendre (metricPair g' p.1 p.2 (frameVector e' p.1 v.val)) k : ℂ)*G (p.1,v.val) ∂sphereProbability
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [hrep p.1 hp.1 v]
  have hfv : frameVector e' p.1 v.val = frameVector e p.1 v.val := by simp only [frameVector,heeq]
  rw [hfv]
  have hmetric : metricPair g' p.1 p.2 (frameVector e p.1 v.val) =
      metricPair g p.1 p.2 (frameVector e p.1 v.val) := by simp only [metricPair,hgeq]
  rw [hmetric]

theorem Test.smoothNear_harmonicTruncation {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hg : ∀ i j,ContDiffOn ℝ ∞ (fun y => g y i j) Y) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (n : ℕ) :
    smoothNear (harmonicTruncation g e φ n) (bundle Y g) := by
  obtain ⟨K,hK,hKY,G,hG,hrep,hzero⟩ := hφ.exists_smooth_standard_representative hY e he hframe
  refine ⟨Prod.fst ⁻¹' Y,hY.preimage continuous_fst,fun p hp => hp.1,?_⟩
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  exact ContDiffAt.sum (fun k _ => contDiffAt_degreePart hY g hg e he φ G hG hrep k hp p.2)

end ShrinkingSpheres
