module

public import Proof.CalderonN.CrossSeries
public import Proof.CalderonN.CrossSpectral

import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.InfiniteSum

public section

noncomputable section
open Set MeasureTheory

namespace CalderonN

variable {d : ℕ} [NeZero d]
open LocalMetricExtension
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 900000 in
private theorem countable_of_summable_positive {ι : Type*} {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (hs : Summable a) : Countable ι := by
  have hnorm : Summable (fun i => ‖a i‖) := hs.norm
  have hc : (Function.support (fun i => ‖a i‖ₑ)).Countable :=
    Summable.countable_support_ennreal (tsum_enorm_ne_top_iff_summable_norm.mpr hnorm)
  have he : Function.support (fun i => ‖a i‖ₑ) = univ := by
    ext i
    simp [Function.mem_support, (ha i).ne']
  exact countable_univ_iff.mp (he ▸ hc)

open scoped ENNReal in
theorem norm_harmonicRestrict_le {D : Set (X d)}
    (hD : IsOpen D) {g : (MetricField d)} (hg : SmoothMetric D g) {S : Set (X d)} (hSD : S ⊆ D) :
    ‖harmonicRestrict hD hg hSD‖ ≤ 1 := by
  let h := Measure.restrict_mono_set (volume : Measure (X d)) hSD
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  have he : harmonicRestrict hD hg hSD u = restrictL2 h u.1 :=
    Lp.ext ((harmonicRestrict_ae hD hg hSD u).trans (restrictL2_ae h u.1).symm)
  rw [he, ← one_mul ‖u‖]
  exact ((restrictL2 h).le_opNorm u.1).trans
    (mul_le_mul_of_nonneg_right (norm_restrictL2_le h) (norm_nonneg _))

/-- The rank and operator error estimates for the approximations to one
harmonic restriction. The restriction here has its actual chart domain. -/
@[expose] def HasRestrictionApprox {D : Set (X d)} (hD : IsOpen D) {g : (MetricField d)}
    (hg : SmoothMetric D g) {S : Set (X d)} (hSD : S ⊆ D) (s N A₀ : ℕ) (B : ℝ) : Prop :=
  ∀ A : ℕ, A₀ ≤ A →
    ∃ T : harmonicL2Space hD hg →L[ℝ] ChartL2 (d := d) S,
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ N * A ^ d ∧
      ‖harmonicRestrict hD hg hSD - T‖ * (A : ℝ) ^ s ≤ B

set_option maxHeartbeats 800000 in
theorem HasRestrictionApprox.isCompactOperator {D : Set (X d)} {hD : IsOpen D} {g : (MetricField d)}
    {hg : SmoothMetric D g} {S : Set (X d)} {hSD : S ⊆ D} {s N A₀ : ℕ} {B : ℝ}
    (h : HasRestrictionApprox hD hg hSD s N A₀ B) (hs : s ≠ 0) :
    IsCompactOperator (harmonicRestrict hD hg hSD) := by
  apply isCompactOperator_of_finiteRank_approx
  intro ε hε
  obtain ⟨a, ha⟩ := exists_nat_gt (max 1 (B / ε))
  let A := max A₀ a
  have haA : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast le_max_right A₀ a
  have hA₁ : (1 : ℝ) ≤ A := (le_max_left _ _).trans (ha.le.trans haA)
  have hB : B / ε ≤ (A : ℝ) ^ s :=
    (le_max_right _ _).trans (ha.le.trans (haA.trans (le_self_pow₀ hA₁ hs)))
  obtain ⟨T, hT, _, herr⟩ := h A (le_max_left _ _)
  refine ⟨T, hT, (le_of_mul_le_mul_right ?_ (by positivity : 0 < (A : ℝ) ^ s))⟩
  exact herr.trans (by simpa only [mul_comm] using (div_le_iff₀ hε).mp hB)

set_option maxHeartbeats 3000000 in
/-- For an injective restriction with the specified approximants the
singular values have a power-sum bound uniform in the chart metrics. -/
theorem exists_uniform_restrictionSpectrum (s N A₀ : ℕ) (B β : ℝ)
    (hβ : 0 < β) (hsβ : (d : ℝ) < s * β) :
    ∃ P : ℝ, 0 ≤ P ∧
    ∀ {D S : Set (X d)} (hD : IsOpen D) {g : (MetricField d)} (hg : SmoothMetric D g) (hSD : S ⊆ D),
      HasRestrictionApprox hD hg hSD s N A₀ B →
      Function.Injective (harmonicRestrict hD hg hSD) →
      let R := harmonicRestrict hD hg hSD
      ∃ (ι : Type) (w : HilbertBasis ι ℝ (harmonicL2Space hD hg)) (μ : ι → ℝ),
        Countable ι ∧ (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ 1) ∧
        (∀ i, (R.adjoint ∘L R) (w i) = μ i ^ 2 • w i) ∧
        (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) ∧
        Summable (fun i => μ i ^ β) ∧ (∑' i, μ i ^ β) ≤ P := by
  classical
  obtain ⟨P, hP, hpower⟩ := uniform_powerSum_of_counted_approx 1 one_pos d s B N A₀ β hβ hsβ
  refine ⟨P, hP, ?_⟩
  intro D S hD g hg hSD happ hinj
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hsβ
    exact (not_lt_of_ge (Nat.cast_nonneg d)) hsβ
  let R := harmonicRestrict hD hg hSD
  obtain ⟨ι, w, μ, hμ, hμR, heigen, hgram⟩ :=
    exists_gram_spectral_data R (happ.isCompactOperator hs) hinj
  have hμ₁ : ∀ i, μ i ≤ 1 :=
    fun i => (hμR i).trans (norm_harmonicRestrict_le hD hg hSD)
  obtain ⟨hsum, hbound⟩ := hpower R w w.orthonormal μ hμ hμ₁ hgram happ
  exact ⟨ι, w, μ, countable_of_summable_positive (fun i => Real.rpow_pos_of_pos (hμ i) _) hsum,
    hμ, hμ₁, heigen, hgram, hsum, hbound⟩

end CalderonN
