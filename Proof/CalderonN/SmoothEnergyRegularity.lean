module

public import Proof.CalderonN.SmoothBesselSections
public import Proof.CalderonN.HorizontalRepresentative
public import Proof.CalderonN.AngularEnergyDensity

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff

namespace CalderonN

variable {n : ℕ} [NeZero n]

lemma continuous_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    {Y : Set (X n)} (hY : IsOpen Y) (f : (X n) → E) (hf : ContinuousOn f Y) (hsupp : tsupport f ⊆ Y) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y ∈ Y
  · exact hf.continuousAt (hY.mem_nhds hy)
  · have hout : y ∉ tsupport f := fun ht => hy (hsupp ht)
    apply (show ContinuousAt (fun _ : (X n) => (0:E)) y from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hout] with x hx
    exact image_eq_zero_of_notMem_tsupport hx

/-- A locally continuous integration weight is sufficient when the other factor has
    compact closed support inside its domain. Exterior values do not affect the integral. -/
lemma integrable_local_weighted {Y : Set (X n)} (hY : IsOpen Y) (weight Q : (X n) → ℝ)
    (hw : ContinuousOn weight Y) (hQ : Continuous Q) (hc : HasCompactSupport Q)
    (hsupp : tsupport Q ⊆ Y) : Integrable (fun y => weight y*Q y) := by
  have hs : tsupport (fun y => weight y*Q y) ⊆ tsupport Q := by
    apply closure_minimal _ (isClosed_tsupport Q)
    intro y hy
    by_contra hn
    exact hy (by simp only [image_eq_zero_of_notMem_tsupport hn,mul_zero])
  exact (continuous_of_tsupport_subset hY _ (hw.mul hQ.continuousOn) (hs.trans hsupp)).integrable_of_hasCompactSupport
    hc.mul_left

lemma Test.horizontal_support {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field n)} (hφ : Test Y g e φ) (i : (I n)) :
    ∃ S,IsCompact S ∧ S ⊆ Y ∧ ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,horizontalField g e φ i (y,w) = 0 := by
  obtain ⟨S,hS,hSY,hzero⟩ := hφ.2.1
  refine ⟨S,hS,hSY,?_⟩
  intro y hy w hw
  exact horizontal_zero_of_sphere_support hY h hK e he hframe hφ.1 S hS.isClosed hzero hy w hw (e y i)

/-- Every actual horizontal Sobolev square in the frozen energy has a continuous compact
    representative supported strictly inside the domain of the geometric data. -/
theorem Test.exists_horizontal_sobolev_square_representative (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field n)} (hφ : Test Y g e φ) (i : (I n)) (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : (X n) → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = sobolevSq g e s y (fun w => horizontal g φ y w (e y i)) :=
  exists_sobolev_square_representative_of_support hn hY e he hframe
    (smoothNear_horizontalField hY h hK e he hφ.1 i) (hφ.horizontal_support hY h hK e he hframe i) s hs

lemma integrableOn_weighted_of_representative {Y : Set (X n)} (hY : IsOpen Y) (weight u : (X n) → ℝ)
    (hw : ContinuousOn weight Y)
    (hrep : ∃ Q : (X n) → ℝ,Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y,0 ≤ Q y) ∧ ∀ y ∈ Y,Q y = u y) :
    IntegrableOn (fun y => weight y*u y) Y := by
  obtain ⟨Q,hQ,hc,hs,hpos,hEq⟩ := hrep
  apply ((integrable_local_weighted hY weight Q hw hQ hc hs).restrict (s:=Y)).congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  rw [hEq y hy]

lemma Test.integrableOn_weighted_sobolev (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {g : (MetricField n)} (e : (Frame n))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field n)} (hφ : Test Y g e φ) (s : ℝ) (hs : s ≤ 2) (weight : (X n) → ℝ) (hw : ContinuousOn weight Y) :
    IntegrableOn (fun y => weight y*sobolevSq g e s y (fun w => φ (y,w))) Y :=
  integrableOn_weighted_of_representative hY weight _ hw
    (hφ.exists_sobolev_square_representative hn hY e he hframe s hs)

lemma Test.integrableOn_weighted_horizontal_sobolev (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field n)} (hφ : Test Y g e φ) (i : (I n)) (s : ℝ) (hs : s ≤ 2)
    (weight : (X n) → ℝ) (hw : ContinuousOn weight Y) :
    IntegrableOn (fun y => weight y*sobolevSq g e s y (fun w => horizontal g φ y w (e y i))) Y :=
  integrableOn_weighted_of_representative hY weight _ hw
    (hφ.exists_horizontal_sobolev_square_representative hn hY h hK e he hframe i s hs)

lemma Test.integrableOn_weighted_horizontal_fiber (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : (Field n)} (hφ : Test Y g e φ) (i : (I n)) (weight : (X n) → ℝ) (hw : ContinuousOn weight Y) :
    IntegrableOn (fun y => weight y*fiberSq e y (fun w => horizontal g φ y w (e y i))) Y :=
  integrableOn_weighted_of_representative hY weight _ hw
    (exists_fiber_square_representative_of_support hn hY e he hframe
      (smoothNear_horizontalField hY h hK e he hφ.1 i) (hφ.horizontal_support hY h hK e he hframe i))

/-- All four actual terms of the frozen energy are integrable for every admitted smooth
    compact test and arbitrary admissible profile. No finite angular cutoff is assumed. -/
theorem Profile.integrableOn_physicalEnergyDensity (hn : 3 ≤ n) {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hfloor : 1 ≤ floor) {φ : (Field n)} (hφ : Test Y g e φ) :
    IntegrableOn (physicalEnergyDensity g e r φ) Y := by
  have hρ := (h.contDiffOn_density hK).continuousOn
  have hβ := (hp.contDiffOn_beta hY h hK hfloor).continuousOn
  have hiβ := (hp.contDiffOn_beta_inv hY h hK hfloor).continuousOn
  have h1 := integrable_finsetSum Finset.univ (fun i _ =>
    hφ.integrableOn_weighted_horizontal_fiber hn hY h hK e he hframe i _ hρ)
  have h2 := hφ.integrableOn_weighted_sobolev hn hY e he hframe 1 (by norm_num) _ (hρ.mul (hβ.pow 2))
  have h3 := integrable_finsetSum Finset.univ (fun i _ =>
    hφ.integrableOn_weighted_horizontal_sobolev hn hY h hK e he hframe i (1/2) (by norm_num) _ (hρ.mul hiβ))
  have h4 := hφ.integrableOn_weighted_sobolev hn hY e he hframe (3/2) (by norm_num) _ (hρ.mul hβ)
  apply (((h1.add h2).add h3).add h4).congr
  filter_upwards [] with y
  change ((∑ i,metricDensity g y*fiberSq e y (fun w => horizontal g φ y w (e y i)))+
    (metricDensity g y*(beta g r y)^2)*sobolevSq g e 1 y (fun w => φ (y,w)))+
    (∑ i,(metricDensity g y*(beta g r y)⁻¹)*sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
    (metricDensity g y*beta g r y)*sobolevSq g e (3/2) y (fun w => φ (y,w)) = _
  simp only [physicalEnergyDensity,Finset.mul_sum,mul_add,mul_assoc]

end CalderonN
