module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.LinearGreen
import Proof.CalderonN.LinearHessian
import Proof.CalderonN.LinearNormalization
import Mathlib.Tactic

public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {n : ℕ} [NeZero n]

/-- A smooth known side whose defining differential is the selected normal coordinate
projection. This is the geometric input to the fixed dilated lower strips. -/
@[expose] def ContainsAlignedSide (normal : (I n)) (Ω W : Set (X n)) : Prop :=
  ∃ (V : Set (X n)) (s : (X n) → ℝ), IsOpen V ∧ (0 : (X n)) ∈ V ∧ V ⊆ Ω ∧
    ContDiffOn ℝ ∞ s V ∧ s 0 = 0 ∧ (∀ v : (X n), fderiv ℝ s 0 v = v normal) ∧
    {x ∈ V | s x < 0} ⊆ W

theorem ContainsAlignedSide.containsSmoothSide {normal : (I n)} {Ω W : Set (X n)} (h : ContainsAlignedSide normal Ω W) :
    ContainsSmoothSide Ω W := by
  obtain ⟨V, s, hV, h₀, hsub, hs, hs₀, hnormal, hside⟩ := h
  refine ⟨V, s, hV, h₀, hsub, hs, hs₀, ?_, hside⟩
  intro hzero
  have h := hnormal (axis normal)
  simp [hzero, axis] at h

/-- The remaining local theorem in normalized coordinates. -/
@[expose] def NormalizedLocalMetricExtension (normal : (I n)) : Prop :=
  ∀ {Ω W : Set (X n)}, IsOpen Ω → IsOpen W → W ⊆ Ω → ContainsAlignedSide normal Ω W →
    ∀ {g₁ g₂ : (MetricField n)}, SmoothMetric Ω g₁ → SmoothMetric Ω g₂ → g₁ 0 = 1 → g₂ 0 = 1 →
      HarmonicCoordinates Ω g₁ → HarmonicCoordinates Ω g₂ →
    ∀ {G₁ G₂ : (X n) × (X n) → ℝ}, GreenGerm Ω g₁ G₁ → GreenGerm Ω g₂ G₂ →
      EqOn g₁ g₂ W → EqOn G₁ G₂ (OffDiagonal W) →
    ∀ {m : ℕ} {u₁ u₂ : Fin m → (X n) → ℝ},
      (∀ a, Harmonic Ω g₁ (u₁ a)) → (∀ a, Harmonic Ω g₂ (u₂ a)) →
      (∀ a, EqOn (u₁ a) (u₂ a) W) → HessianSpanning g₁ u₁ →
      ∃ r > 0, ball (0 : (X n)) r ⊆ Ω ∧ EqOn g₁ g₂ (ball 0 r)

set_option maxHeartbeats 1000000 in
/-- Reduction of the exact chart statement to its normalized form.
The original Green kernels and paired functions are transported together. -/
theorem localMetricExtension_of_normalized
    (normal : (I n)) (hnorm : NormalizedLocalMetricExtension normal)
    {Ω W : Set (X n)} (hΩ : IsOpen Ω) (hW : IsOpen W) (hWΩ : W ⊆ Ω)
    (hside : ContainsSmoothSide Ω W)
    {g₁ g₂ : (MetricField n)} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {G₁ G₂ : (X n) × (X n) → ℝ} (hG₁ : GreenGerm Ω g₁ G₁) (hG₂ : GreenGerm Ω g₂ G₂)
    (hmetric : EqOn g₁ g₂ W) (hgreen : EqOn G₁ G₂ (OffDiagonal W))
    {m : ℕ} {u₁ u₂ : Fin m → (X n) → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hpairs : ∀ a, EqOn (u₁ a) (u₂ a) W) (hspan : HessianSpanning g₁ u₁) :
    ∃ r > 0, ball (0 : (X n)) r ⊆ Ω ∧ EqOn g₁ g₂ (ball 0 r) := by
  obtain ⟨V, s, hV, hz, hVΩ, hs, hs₀, hDs, hnegative⟩ := hside
  have h₀ := hVΩ hz
  have hsame : g₁ 0 = g₂ 0 := by
    ext i j
    exact eq_at_origin_of_eqOn_side (show ContainsSmoothSide Ω W from
      ⟨V, s, hV, hz, hVΩ, hs, hs₀, hDs, hnegative⟩)
      ((hg₁.1 i j).continuousOn.continuousAt (hΩ.mem_nhds h₀))
      ((hg₂.1 i j).continuousOn.continuousAt (hΩ.mem_nhds h₀))
      (fun x hx => congrArg (fun K : (Mat n) => K i j) (hmetric hx))
  obtain ⟨A, c, hc, hnorm₁, hAc⟩ := exists_metric_separator_normalization normal (hg₁.2 0 h₀) _ hDs
  let Ω' := A ⁻¹' Ω
  let W' := A ⁻¹' W
  let s' := fun x => c⁻¹ * s (A x)
  have hs' : ContainsAlignedSide normal Ω' W' := by
    have hDs' : DifferentiableAt ℝ s (A 0) := by
      simpa only [map_zero] using (hs.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hz)
    have hF := (hDs'.hasFDerivAt.comp 0 A.toContinuousLinearMap.hasFDerivAt).const_mul c⁻¹
    refine ⟨A ⁻¹' V, s', hV.preimage A.continuous, by simpa only [mem_preimage, map_zero] using hz,
      fun _ hx => hVΩ hx, contDiffOn_const.mul
        (hs.comp A.toContinuousLinearMap.contDiff.contDiffOn (fun _ hx => hx)),
      by simp [s', hs₀], ?_, ?_⟩
    · intro v
      have hD : fderiv ℝ s' 0 = c⁻¹ • (fderiv ℝ s (A 0)).comp A.toContinuousLinearMap :=
        hF.fderiv
      rw [hD]
      change c⁻¹ * fderiv ℝ s (A 0) (A v) = v normal
      rw [map_zero, hAc, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    · intro x hx
      apply hnegative
      refine ⟨hx.1, lt_of_not_ge (fun h => ?_)⟩
      exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr hc.le) h)) hx.2
  have hI₁ : linearPullbackMetric g₁ A 0 = 1 := by
    simpa only [linearPullbackMetric, map_zero] using hnorm₁
  have hI₂ : linearPullbackMetric g₂ A 0 = 1 := by
    simpa only [linearPullbackMetric, map_zero, ← hsame] using hI₁
  have hmetric' : EqOn (linearPullbackMetric g₁ A) (linearPullbackMetric g₂ A) W' :=
    fun x hx => (linearPullbackMetric_eq_iff A x).mpr (hmetric hx)
  have hgreen' : EqOn (linearPullbackGreen G₁ A) (linearPullbackGreen G₂ A) (OffDiagonal W') :=
    fun q hq => hgreen (x := (A q.1, A q.2)) ⟨hq.1, hq.2.1, fun h => hq.2.2 (A.injective h)⟩
  obtain ⟨r, hr, hball, heq⟩ := hnorm (hΩ.preimage A.continuous) (hW.preimage A.continuous)
    (fun _ hx => hWΩ hx) hs' (smoothMetric_linearPullback hg₁ A) (smoothMetric_linearPullback hg₂ A)
    hI₁ hI₂ (harmonicCoordinates_linearPullback hΩ hg₁ hchart₁ A)
    (harmonicCoordinates_linearPullback hΩ hg₂ hchart₂ A)
    (hG₁.linearPullback hΩ hg₁ A) (hG₂.linearPullback hΩ hg₂ A) hmetric' hgreen'
    (fun a => harmonic_linearPullback hΩ hg₁ A (hu₁ a))
    (fun a => harmonic_linearPullback hΩ hg₂ A (hu₂ a))
    (fun a _ hx => hpairs a hx) (hessianSpanning_linearPullback hΩ h₀ (fun a => (hu₁ a).1) hspan A)
  have hnear : A.symm ⁻¹' ball (0 : (X n)) r ∈ nhds (0 : (X n)) :=
    (isOpen_ball.preimage A.symm.continuous).mem_nhds (by simpa only [mem_preimage, map_zero] using mem_ball_self hr)
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨R, hR, ?_, ?_⟩
  · intro z hz'
    have hzΩ : A (A.symm z) ∈ Ω := hball (hsub hz')
    simpa only [A.apply_symm_apply] using hzΩ
  · intro z hz'
    have hEq := (linearPullbackMetric_eq_iff A (A.symm z)).mp (heq (hsub hz'))
    simpa only [A.apply_symm_apply] using hEq

end CalderonN
