module

public import Proof.CalderonN.SmoothHarmonicWeights
public import Proof.CalderonN.TestRepresentative

import Proof.CalderonN.CrossTensor
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic SmoothSphereFields

variable {n : ℕ} [NeZero n]

theorem fiberSq_eq_component_norms (e : Frame n) (y : X n) (F : X n → ℂ) (U V : SphereL2 n)
    (hRe : U =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).im)) :
    fiberSq e y F = ‖U‖^2 + ‖V‖^2 := by
  rw [fiberSq_eq_integral_norm_sq]
  have heq : (fun v : UnitSphere n => ‖F (frameVector e y v.val)‖^2) =ᵐ[unitSphereProbability n]
      (fun v : UnitSphere n => (U v)^2 + (V v)^2) := by
    filter_upwards [hRe,hIm] with v hr hi
    rw [Complex.sq_norm,Complex.normSq_apply,← hr,← hi]
    ring
  have hInt (u : SphereL2 n) : Integrable (fun v : UnitSphere n => (u v)^2) (unitSphereProbability n) :=
    (Lp.memLp u).integrable_sq
  rw [integral_congr_ae heq, integral_add (hInt U) (hInt V),
    LocalMetricExtension.integral_sq_eq_norm_sq U, LocalMetricExtension.integral_sq_eq_norm_sq V]

/-- Sobolev square computed with the actual complex zonal projection. -/
theorem sobolevSq_eq_bessel_components (hn : 3 ≤ n) (g : MetricField n) (e : Frame n) (y : X n)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (U V B C : SphereL2 n)
    (hRe : U =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).im))
    (s : ℝ)
    (hB : ∀ k, harmonicProjection k B = besselWeight s k • harmonicProjection k U)
    (hC : ∀ k, harmonicProjection k C = besselWeight s k • harmonicProjection k V) :
    sobolevSq g e s y F = ‖B‖^2 + ‖C‖^2 := by
  rw [sobolevSq_harmonicProjection_components hn g e y hframe F U V hRe hIm]
  simpa only [← mul_add] using
    ((hasSum_weighted_harmonicProjection s U B hB).add
      (hasSum_weighted_harmonicProjection s V C hC)).tsum_eq

theorem sobolevSq_zero_eq_fiberSq_components (hn : 3 ≤ n) (g : MetricField n)
    (e : Frame n) (y : X n)
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (F : X n → ℂ) (U V : SphereL2 n)
    (hRe : U =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).re))
    (hIm : V =ᵐ[unitSphereProbability n] (fun v : UnitSphere n => (F (frameVector e y v.val)).im)) :
    sobolevSq g e 0 y F = fiberSq e y F := by
  have hGraph (u : SphereL2 n) (k : ℕ) :
      harmonicProjection k u = besselWeight 0 k • harmonicProjection k u := by
    simp [besselWeight]
  rw [sobolevSq_eq_bessel_components hn g e y hframe F U V U V hRe hIm 0 (hGraph U) (hGraph V),
    fiberSq_eq_component_norms e y F U V hRe hIm]

private theorem exists_angular_square_representative (hn : 3 ≤ n) {Y : Set (X n)}
    (hY : IsOpen Y) {g : MetricField n} (e : Frame n)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field n} (hφ : smoothNear φ (bundle Y g))
    (hcpt : ∃ K, IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K, ∀ w ∈ sphereAt g y, φ (y,w) = 0)
    (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : X n → ℝ, Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y, 0 ≤ Q y) ∧ ∀ y ∈ Y, Q y = sobolevSq g e s y (fun w => φ (y,w)) ∧
        (s = 0 → Q y = fiberSq e y (fun w => φ (y,w))) := by
  obtain ⟨K,hK,hKY,G,hG,hrep,hzero⟩ :=
    exists_smooth_standard_representative_of_support hY e he hframe hφ hcpt
  let R : X n × X n → ℝ := fun p => (G p).re
  let J : X n × X n → ℝ := fun p => (G p).im
  have hR : ContDiff ℝ ∞ R := Complex.reCLM.contDiff.comp hG
  have hJ : ContDiff ℝ ∞ J := Complex.imCLM.contDiff.comp hG
  let B := ambientBesselField hn s hs R hR
  let C := ambientBesselField hn s hs J hJ
  let Q (y : X n) := ‖B y‖^2 + ‖C y‖^2
  have hQ : Continuous Q := ((contDiff_ambientBesselField hn s hs R hR).continuous.norm.pow 2).add
    ((contDiff_ambientBesselField hn s hs J hJ).continuous.norm.pow 2)
  have hz (y : X n) (hy : y ∉ K) : Q y = 0 := by
    have hr := ambientBesselField_zero hn s hs R hR K
      (fun x hx v => by simp [R,hzero x hx v]) y hy
    have hi := ambientBesselField_zero hn s hs J hJ K
      (fun x hx v => by simp [J,hzero x hx v]) y hy
    simp [Q,B,C,hr,hi]
  have hsupp : tsupport Q ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_contra hnK
    exact hy (hz y hnK)
  refine ⟨Q,hQ,HasCompactSupport.intro hK hz,hsupp.trans hKY,fun y => by dsimp [Q]; positivity,?_⟩
  intro y hy
  let U := ambientSphereL2 R hR y
  let V := ambientSphereL2 J hJ y
  have hre : U =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (φ (y,frameVector e y v.val)).re :=
    (ambientSphereL2_ae R hR y).trans (Filter.Eventually.of_forall (fun v => congrArg Complex.re (hrep y hy v)))
  have him : V =ᵐ[unitSphereProbability n] fun v : UnitSphere n => (φ (y,frameVector e y v.val)).im :=
    (ambientSphereL2_ae J hJ y).trans (Filter.Eventually.of_forall (fun v => congrArg Complex.im (hrep y hy v)))
  have hS := sobolevSq_eq_bessel_components hn g e y (hframe y hy) (fun w => φ (y,w)) U V (B y) (C y)
    hre him s (ambientBesselField_projection hn s hs R hR y) (ambientBesselField_projection hn s hs J hJ y)
  refine ⟨hS.symm,fun h0 => ?_⟩
  change ‖B y‖^2 + ‖C y‖^2 = fiberSq e y (fun w => φ (y,w))
  rw [← hS,h0]
  exact sobolevSq_zero_eq_fiberSq_components hn g e y (hframe y hy) (fun w => φ (y,w)) U V hre him

theorem exists_sobolev_square_representative_of_support (hn : 3 ≤ n) {Y : Set (X n)}
    (hY : IsOpen Y) {g : MetricField n} (e : Frame n)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field n} (hφ : smoothNear φ (bundle Y g))
    (hcpt : ∃ K, IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K, ∀ w ∈ sphereAt g y, φ (y,w) = 0)
    (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : X n → ℝ, Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y, 0 ≤ Q y) ∧ ∀ y ∈ Y, Q y = sobolevSq g e s y (fun w => φ (y,w)) := by
  obtain ⟨Q,hQ,hc,hsupp,hpos,hEq⟩ := exists_angular_square_representative hn hY e he hframe hφ hcpt s hs
  exact ⟨Q,hQ,hc,hsupp,hpos,fun y hy => (hEq y hy).1⟩

theorem Test.exists_sobolev_square_representative (hn : 3 ≤ n) {Y : Set (X n)}
    (hY : IsOpen Y) {g : MetricField n} (e : Frame n)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field n} (hφ : Test Y g e φ) (s : ℝ) (hs : s ≤ 2) :
    ∃ Q : X n → ℝ, Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y, 0 ≤ Q y) ∧ ∀ y ∈ Y, Q y = sobolevSq g e s y (fun w => φ (y,w)) :=
  exists_sobolev_square_representative_of_support hn hY e he hframe hφ.1 hφ.2.1 s hs

theorem exists_fiber_square_representative_of_support (hn : 3 ≤ n) {Y : Set (X n)}
    (hY : IsOpen Y) {g : MetricField n} (e : Frame n)
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {φ : Field n} (hφ : smoothNear φ (bundle Y g))
    (hcpt : ∃ K, IsCompact K ∧ K ⊆ Y ∧ ∀ y ∈ Y \ K, ∀ w ∈ sphereAt g y, φ (y,w) = 0) :
    ∃ Q : X n → ℝ, Continuous Q ∧ HasCompactSupport Q ∧ tsupport Q ⊆ Y ∧
      (∀ y, 0 ≤ Q y) ∧ ∀ y ∈ Y, Q y = fiberSq e y (fun w => φ (y,w)) := by
  obtain ⟨Q,hQ,hc,hsupp,hpos,hEq⟩ := exists_angular_square_representative hn hY e he hframe hφ hcpt 0 (by norm_num)
  exact ⟨Q,hQ,hc,hsupp,hpos,fun y hy => (hEq y hy).2 rfl⟩

end CalderonN
