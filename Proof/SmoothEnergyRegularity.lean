import Proof.ComplexBesselSections
import Proof.HorizontalRepresentative
import Proof.LocalWeightedIntegration

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres

lemma Test.horizontal_support {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (i : I) :
    ∃ S,IsCompact S ∧ S ⊆ Y ∧ ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,horizontalField g e φ i (y,w) = 0 := by
  obtain ⟨S,hS,hSY,hzero⟩ := hφ.2.1
  refine ⟨S,hS,hSY,?_⟩
  intro y hy w hw
  exact horizontal_zero_of_sphere_support hY h hK e he hframe hφ.1 S hS.isClosed hzero hy w hw (e y i)

/-- Every actual horizontal Sobolev square in the frozen energy has a continuous compact
    representative supported strictly inside the domain of the geometric data. -/
theorem Test.exists_horizontal_sobolev_square_representative {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (i : I) (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : X → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = sobolevSq g e s y (fun w => horizontal g φ y w (e y i)) :=
  exists_sobolev_square_representative_of_support hY e he hframe
    (smoothNear_horizontalField hY h hK e he hφ.1 i) (hφ.horizontal_support hY h hK e he hframe i) s hs

lemma integrableOn_weighted_of_representative {Y : Set X} (hY : IsOpen Y) (weight u : X → ℝ)
    (hw : ContinuousOn weight Y)
    (hrep : ∃ Q : X → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = u y) :
    IntegrableOn (fun y => weight y*u y) Y := by
  obtain ⟨Q,hQ,hc,hs,hpos,hEq⟩ := hrep
  apply ((integrable_local_weighted hY weight Q hw hQ hc hs).restrict (s:=Y)).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  rw [hEq y hy]

lemma Test.integrableOn_weighted_sobolev {Y : Set X} (hY : IsOpen Y) {g : MetricField} (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (s : ℝ) (hs : s ≤ 2) (weight : X → ℝ) (hw : ContinuousOn weight Y) :
    IntegrableOn (fun y => weight y*sobolevSq g e s y (fun w => φ (y,w))) Y :=
  integrableOn_weighted_of_representative hY weight _ hw
    (hφ.exists_sobolev_square_representative hY e he hframe s hs)

lemma Test.integrableOn_weighted_horizontal_sobolev {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (i : I) (s : ℝ) (hs : s ≤ 2)
    (weight : X → ℝ) (hw : ContinuousOn weight Y) :
    IntegrableOn (fun y => weight y*sobolevSq g e s y (fun w => horizontal g φ y w (e y i))) Y :=
  integrableOn_weighted_of_representative hY weight _ hw
    (hφ.exists_horizontal_sobolev_square_representative hY h hK e he hframe i s hs)

lemma Test.integrableOn_weighted_horizontal_fiber {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field} (hφ : Test Y g e φ) (i : I) (weight : X → ℝ) (hw : ContinuousOn weight Y) :
    IntegrableOn (fun y => weight y*fiberSq e y (fun w => horizontal g φ y w (e y i))) Y :=
  integrableOn_weighted_of_representative hY weight _ hw
    (exists_fiber_square_representative_of_support hY e he hframe
      (smoothNear_horizontalField hY h hK e he hφ.1 i) (hφ.horizontal_support hY h hK e he hframe i))

/-- All four actual terms of the frozen energy are integrable for every admitted smooth
    compact test and arbitrary admissible profile. No finite angular cutoff is assumed. -/
theorem Profile.integrableOn_physicalEnergyDensity {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hfloor : 1 ≤ floor) {φ : Field} (hφ : Test Y g e φ) :
    IntegrableOn (physicalEnergyDensity g e r φ) Y := by
  have hρ := (h.contDiffOn_density hK).continuousOn
  have hβ := (hp.contDiffOn_beta hY h hK hfloor).continuousOn
  have hiβ := (hp.contDiffOn_beta_inv hY h hK hfloor).continuousOn
  have h1 := integrable_finsetSum Finset.univ (fun i _ =>
    hφ.integrableOn_weighted_horizontal_fiber hY h hK e he hframe i _ hρ)
  have h2 := hφ.integrableOn_weighted_sobolev hY e he hframe 1 (by norm_num) _ (hρ.mul (hβ.pow 2))
  have h3 := integrable_finsetSum Finset.univ (fun i _ =>
    hφ.integrableOn_weighted_horizontal_sobolev hY h hK e he hframe i (1/2) (by norm_num) _ (hρ.mul hiβ))
  have h4 := hφ.integrableOn_weighted_sobolev hY e he hframe (3/2) (by norm_num) _ (hρ.mul hβ)
  apply (((h1.add h2).add h3).add h4).congr
  filter_upwards [] with y
  change ((∑ i,metricDensity g y*fiberSq e y (fun w => horizontal g φ y w (e y i)))+
    (metricDensity g y*(beta g r y)^2)*sobolevSq g e 1 y (fun w => φ (y,w)))+
    (∑ i,(metricDensity g y*(beta g r y)⁻¹)*sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
    (metricDensity g y*beta g r y)*sobolevSq g e (3/2) y (fun w => φ (y,w)) = _
  simp only [physicalEnergyDensity,Finset.mul_sum,mul_add,mul_assoc]

end ShrinkingSpheres
