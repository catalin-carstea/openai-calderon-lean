import Proof.AngularOutputSections
import Proof.ProfileFischerBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

namespace HarmonicTestExpansion
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}

lemma zero_off_support_sphere (E : HarmonicTestExpansion Y g e φ)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) :
    ∀ y ∈ Y \ E.supportSet,∀ w ∈ sphereAt g y,φ (y,w) = 0 := by
  intro y hy w hw
  obtain ⟨v,hv⟩ := exists_unitSphere_frameVector g e y (hframe y hy.1) w hw
  rw [← hv,← E.representativeEq y hy.1 v,E.representativeZero y hy.2 v]

lemma exists_horizontal_component_representative (E : HarmonicTestExpansion Y g e φ)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hφ : smoothNear φ (bundle Y g)) (i : I) (L : ℂ →L[ℝ] ℝ) :
    ∃ H : X × X → ℝ,ContDiff ℝ ∞ H ∧
      (∀ y ∈ Y,∀ v : UnitSphere,H (y,v.val) = L (horizontal g φ y (frameVector e y v.val) (e y i))) ∧
      ∀ y ∉ E.supportSet,∀ v : UnitSphere,H (y,v.val) = 0 := by
  have hz := E.zero_off_support_sphere hframe
  have hzero : ∀ y ∈ Y \ E.supportSet,∀ w ∈ sphereAt g y,horizontalField g e φ i (y,w) = 0 := by
    intro y hy w hw
    exact horizontal_zero_of_sphere_support hY h hK e he hframe hφ E.supportSet E.compactSupportSet.isClosed
      hz hy w hw (e y i)
  obtain ⟨S,hS,hSY,G,hG,hrep,hGz⟩ := exists_smooth_standard_representative_of_support hY e he hframe
    (smoothNear_horizontalField hY h hK e he hφ i) ⟨E.supportSet,E.compactSupportSet,E.supportSubset,hzero⟩
  refine ⟨fun p => L (G p),L.contDiff.comp hG,?_,?_⟩
  · intro y hy v
    exact congrArg L (hrep y hy v)
  · intro y hy v
    change L (G (y,v.val)) = 0
    by_cases hyy : y ∈ Y
    · rw [hrep y hyy v,hzero y ⟨hyy,hy⟩ _ (frameVector_mem_sphere g e y (hframe y hyy) v),map_zero]
    · have hn : y ∉ S := fun hs => hyy (hSY hs)
      rw [hGz y hn v,map_zero]

lemma exists_logRadiusCoefficient (E : HarmonicTestExpansion Y g e φ) (hY : IsOpen Y)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y) (r : X → ℝ)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y) (i : I) :
    ∃ b : X → ℝ,ContDiff ℝ ∞ b ∧
      ∀ y ∈ E.supportSet,b y = fderiv ℝ (fun x => Real.log (r x)) y (e y i) := by
  have hb : ContDiffOn ℝ ∞ (fun y => fderiv ℝ (fun x => Real.log (r x)) y (e y i)) Y :=
    (hlog.fderiv_of_isOpen hY (by simp)).clm_apply (he i)
  obtain ⟨b,hb,hcomp,hEq⟩ := exists_smooth_localization hY E.compactSupportSet E.supportSubset _ hb
  exact ⟨b,hb,fun y hy => (hEq y hy).self_of_nhds⟩

end HarmonicTestExpansion

/-- Shared smooth real and imaginary horizontal representatives and localized logarithmic
    radius coefficients for one canonical test expansion. They use its one compact support. -/
structure AngularModelData {Y : Set X} {g : MetricField} {e : Frame} {φ : Field}
    (E : HarmonicTestExpansion Y g e φ) (r : X → ℝ) where
  realHorizontal : I → X × X → ℝ
  imagHorizontal : I → X × X → ℝ
  realSmooth : ∀ i,ContDiff ℝ ∞ (realHorizontal i)
  imagSmooth : ∀ i,ContDiff ℝ ∞ (imagHorizontal i)
  realEq : ∀ i,∀ y ∈ Y,∀ v : UnitSphere,realHorizontal i (y,v.val) = (horizontal g φ y (frameVector e y v.val) (e y i)).re
  imagEq : ∀ i,∀ y ∈ Y,∀ v : UnitSphere,imagHorizontal i (y,v.val) = (horizontal g φ y (frameVector e y v.val) (e y i)).im
  realZero : ∀ i,∀ y ∉ E.supportSet,∀ v : UnitSphere,realHorizontal i (y,v.val) = 0
  imagZero : ∀ i,∀ y ∉ E.supportSet,∀ v : UnitSphere,imagHorizontal i (y,v.val) = 0
  coefficient : I → X → ℝ
  coefficientSmooth : ∀ i,ContDiff ℝ ∞ (coefficient i)
  coefficientEq : ∀ i,∀ y ∈ E.supportSet,coefficient i y = fderiv ℝ (fun x => Real.log (r x)) y (e y i)

theorem exists_angularModelData {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) (E : HarmonicTestExpansion Y g e φ)
    (r : X → ℝ) (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y) : Nonempty (AngularModelData E r) := by
  classical
  have hre := fun i => E.exists_horizontal_component_representative hY h hK he hframe hφ i Complex.reCLM
  have him := fun i => E.exists_horizontal_component_representative hY h hK he hframe hφ i Complex.imCLM
  choose Hr hHr hReq hRz using hre
  choose Hi hHi hIeq hIz using him
  choose b hb hbeq using fun i => E.exists_logRadiusCoefficient hY he r hlog i
  exact ⟨{
    realHorizontal := Hr
    imagHorizontal := Hi
    realSmooth := hHr
    imagSmooth := hHi
    realEq := hReq
    imagEq := hIeq
    realZero := hRz
    imagZero := hIz
    coefficient := b
    coefficientSmooth := hb
    coefficientEq := hbeq }⟩

end ShrinkingSpheres
