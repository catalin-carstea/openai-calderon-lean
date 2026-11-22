module

public import Proof.CalderonN.CrossWeakContinuation
public import Proof.CalderonN.StrictMetricWeight

import Proof.CalderonN.CollarResidual
public import Proof.CalderonN.ExponentialBalancing
import Proof.CalderonN.WeightedCollars
import Proof.CalderonN.StrictCarlemanMargins
import Proof.CalderonN.CrossTensor
public import Proof.CalderonN.MetricDivergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Matrix
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

open Elliptic
open LocalMetricExtension (integral_sq_eq_norm_sq)
open Elliptic.CutoffCommutator (Lop_congr_of_eventuallyEq Lop_const_zero)

private abbrev chartMeasure (D : Set (X dim)) : Measure (X dim) := (volume : Measure (X dim)).restrict D

theorem harmonicRestrict_norm_le {D V : Set (X dim)} (hD : IsOpen D)
    {g : (MetricField dim)} (hg : SmoothMetric D g) (hVD : V ⊆ D) (u : harmonicL2Space hD hg) :
    ‖harmonicRestrict hD hg hVD u‖ ≤ ‖u‖ := by
  let hle : chartMeasure V ≤ (1 : ℝ≥0∞) • chartMeasure D := by
    simpa only [one_smul] using Measure.restrict_mono_set (volume : Measure (X dim)) hVD
  let R : ChartL2 D →L[ℝ] ChartL2 V := Lp.LpToLpOfMeasureLeSMul (by simp) hle
  have hR : ‖R‖ ≤ 1 := by
    simpa using (Lp.norm_LpToLpOfMeasureLeSMul_le
      (E := ℝ) (p := (2 : ℝ≥0∞)) (by simp : (1 : ℝ≥0∞) ≠ ⊤) hle)
  change ‖R u.1‖ ≤ ‖u.1‖
  calc
    ‖R u.1‖ ≤ ‖R‖ * ‖u.1‖ := R.le_opNorm u.1
    _ ≤ 1 * ‖u.1‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = _ := one_mul _

private theorem square_integral_of_representative {V : Set (X dim)}
    (q : ChartL2 V) {w : (X dim) → ℝ} (hw : (q : (X dim) → ℝ) =ᵐ[chartMeasure V] w) :
    IntegrableOn (fun x => w x ^ 2) V ∧ (∫ x in V, w x ^ 2) = ‖q‖ ^ 2 := by
  have hLp := (Lp.memLp q).ae_eq hw
  refine ⟨(memLp_two_iff_integrable_sq hLp.aestronglyMeasurable).mp hLp, ?_⟩
  calc
    (∫ x in V, w x ^ 2) = ∫ x in V, q x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      rw [hx]
    _ = _ := integral_sq_eq_norm_sq q

set_option maxHeartbeats 800000 in
/-- A containing union controls the norm on the target by the sum of the
two restriction norms. -/
theorem harmonicRestrict_norm_le_of_subset_union
    {D S O T : Set (X dim)} (hD : IsOpen D) {g : (MetricField dim)} (hg : SmoothMetric D g)
    (hSD : S ⊆ D) (hOD : O ⊆ D) (hTD : T ⊆ D) (hO : MeasurableSet O)
    (hT : T ⊆ S ∪ O) (u : harmonicL2Space hD hg) :
    ‖harmonicRestrict hD hg hTD u‖ ≤
      ‖harmonicRestrict hD hg hSD u‖ + ‖harmonicRestrict hD hg hOD u‖ := by
  obtain ⟨w,_,hw⟩ := harmonicL2Space_representative hD hg u
  have hInt (V : Set (X dim)) (hVD : V ⊆ D) :=
    square_integral_of_representative (harmonicRestrict hD hg hVD u)
      ((harmonicRestrict_ae hD hg hVD u).trans (ae_mono (Measure.restrict_mono_set _ hVD) hw))
  obtain ⟨hSint,hSsq⟩ := hInt S hSD
  obtain ⟨hOint,hOsq⟩ := hInt O hOD
  obtain ⟨_,hTsq⟩ := hInt T hTD
  have hpos (V : Set (X dim)) : ∀ᵐ x ∂(volume : Measure (X dim)).restrict V, 0 ≤ w x ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hUnion : S ∪ O ⊆ (S \ O) ∪ O := by
    intro x hx
    rcases hx with hx | hx
    · by_cases ho : x ∈ O
      · exact Or.inr ho
      · exact Or.inl ⟨hx,ho⟩
    · exact Or.inr hx
  have hSo : IntegrableOn (fun x => w x ^ 2) (S \ O) := hSint.mono_set sdiff_subset
  have hle : (∫ x in T, w x ^ 2) ≤ (∫ x in S, w x ^ 2) + ∫ x in O, w x ^ 2 := by
    calc
      _ ≤ ∫ x in (S \ O) ∪ O, w x ^ 2 :=
        setIntegral_mono_set (hSo.union hOint) (hpos _) (hT.trans hUnion).eventuallyLE
      _ = (∫ x in S \ O, w x ^ 2) + ∫ x in O, w x ^ 2 :=
        setIntegral_union disjoint_sdiff_left hO hSo hOint
      _ ≤ _ := add_le_add (setIntegral_mono_set hSint (hpos _) sdiff_subset.eventuallyLE) le_rfl
  rw [hSsq,hOsq,hTsq] at hle
  have hprod := mul_nonneg (norm_nonneg (harmonicRestrict hD hg hSD u))
    (norm_nonneg (harmonicRestrict hD hg hOD u))
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  exact hle.trans (by nlinarith only [hprod])

private theorem cutoff_residual_vanishes {D F : Set (X dim)} (b : (I dim) → (I dim) → (X dim) → ℝ)
    {χ w : (X dim) → ℝ} (hχD : tsupport χ ⊆ D) (hw : ∀ x ∈ D, Lop b w x = 0)
    (hχ : ∀ x ∉ F, (χ =ᶠ[𝓝 x] fun _ => (0 : ℝ)) ∨ χ =ᶠ[𝓝 x] fun _ => (1 : ℝ)) :
    ∀ x ∉ F, Lop b (fun y => χ y * w y) x = 0 := by
  intro x hx
  rcases hχ x hx with h | h
  · have hg : (fun y => χ y * w y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [h] with y hy
      rw [hy, zero_mul]
    rw [Lop_congr_of_eventuallyEq b hg, Lop_const_zero]
  · have h1 : χ x = 1 := h.eq_of_nhds
    have hxD := hχD (subset_tsupport χ (show χ x ≠ 0 by simp [h1]))
    have hg : (fun y => χ y * w y) =ᶠ[𝓝 x] w := by
      filter_upwards [h] with y hy
      rw [hy, one_mul]
    exact (Lop_congr_of_eventuallyEq b hg).trans (hw x hxD)

/-- An unchanged Carleman weight and two fixed collars give a common
interpolation constant and the weight-gap exponent throughout a metric family. -/
theorem exists_family_harmonicInterpolation_of_collarCutoff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J)
    (g : P → (MetricField dim)) (hg : ∀ p, SmoothMetric univ (g p))
    (hb : ∀ i j : (I dim), ContDiff ℝ ∞ (fun q : P × (X dim) => divergenceCoeff (g q.1) q.2 i j))
    {D S O B H K : Set (X dim)} (hD : IsOpen D) (hS : IsOpen S) (hO : MeasurableSet O)
    (hSD : S ⊆ D) (hOD : O ⊆ D)
    (hB : IsCompact B) (hH : IsCompact H) (hBD : B ⊆ D) (hHS : H ⊆ S)
    (hgD : ∀ p, SmoothMetric D (g p))
    {χ ψ : (X dim) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχD : tsupport χ ⊆ D) (hχK : tsupport χ ⊆ K)
    (hχO : ∀ x ∈ O, χ x = 1)
    (htrans : ∀ x ∉ B ∪ H, (χ =ᶠ[𝓝 x] fun _ => (0 : ℝ)) ∨ χ =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (hψ : Continuous ψ) {pB pO pH C τ₀ : ℝ} (hBO : pB < pO) (hOH : pO < pH)
    (hC : 0 ≤ C) (hτ₀ : 1 ≤ τ₀)
    (hψB : ∀ x ∈ B, ψ x ≤ pB) (hψH : ∀ x ∈ H, ψ x ≤ pH)
    (hψO : ∀ x ∈ O, pO ≤ ψ x)
    (hCar : ∀ p ∈ J, ∀ τ : ℝ, τ₀ ≤ τ → ∀ w : (X dim) → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, coordDeriv i (fun y => Real.exp (τ * ψ y) * w y) x ^ 2) +
        τ^3 * (∫ x, (Real.exp (τ * ψ x) * w x)^2) ≤
        C * ∫ x, Real.exp (2*(τ * ψ x)) * (chartVolume (g p) x * laplace (g p) w x)^2) :
    ∃ A : ℝ, 0 < A ∧ ∀ p ∈ J,
      HarmonicInterpolation hD (hgD p) hSD hOD A ((pO-pB)/(pH-pB)) := by
  let b (p : P) (i j : (I dim)) (x : (X dim)) := divergenceCoeff (g p) x i j
  have hbs (p : P) (i j : (I dim)) (x : (X dim)) : b p i j x = b p j i x :=
    divergenceCoeff_symm (hg p) (mem_univ x) i j
  have hpos (p : P) (x : (X dim)) : Matrix.PosDef (fun i j => b p i j x : (Mat dim)) :=
    divergenceMatrix_posDef (g p) x ((hg p).2 x (mem_univ x))
  obtain ⟨C₁,hC₁,hBrest⟩ := exists_family_collar_residual_l2_bound hJ b hb hbs hD hD
    (Subset.rfl) hB hBD (fun p _ x _ => hpos p x) hχ hχc hχD (continuous_const (y := (1 : ℝ)))
  obtain ⟨C₂,hC₂,hHrest⟩ := exists_family_collar_residual_l2_bound hJ b hb hbs hD hS
    hSD hH hHS (fun p _ x _ => hpos p x) hχ hχc hχD (continuous_const (y := (1 : ℝ)))
  let M := max C₁ C₂
  have hM : 0 ≤ M := hC₁.trans (le_max_left _ _)
  let A := 2 * Real.sqrt (C*M) + Real.exp ((pO-pB) * max τ₀ 1)
  let γ := (pO-pB)/(pH-pB)
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro p hp q
  let qS := harmonicRestrict hD (hgD p) hSD q
  let qO := harmonicRestrict hD (hgD p) hOD q
  obtain ⟨w, hw, hqw⟩ := harmonicL2Space_representative hD (hgD p) q
  obtain ⟨hwD, hnormD⟩ := square_integral_of_representative q.1 hqw
  obtain ⟨hwS, hnormS⟩ := square_integral_of_representative qS
    ((harmonicRestrict_ae hD (hgD p) hSD q).trans (ae_mono (Measure.restrict_mono_set _ hSD) hqw))
  obtain ⟨hwO, hnormO⟩ := square_integral_of_representative qO
    ((harmonicRestrict_ae hD (hgD p) hOD q).trans (ae_mono (Measure.restrict_mono_set _ hOD) hqw))
  have hLw (x : (X dim)) (hx : x ∈ D) : Lop (b p) w x = 0 := by
    change (∑ i, coordDeriv i (fun y => divergenceFlux (g p) w y i) x) = 0
    rw [← chartVolume_mul_laplace_eq_divergence hD (hgD p) hw.1 hx, hw.2 x hx, mul_zero]
  let u (x : (X dim)) := χ x * w x
  let L := Lop (b p) u
  have hu : ContDiff ℝ ∞ u := contDiff_mul_of_tsupport_subset hD hχ hχD hw.1
  have huc : HasCompactSupport u := hχc.mul_right
  have huK : tsupport u ⊆ K := tsupport_mul_subset_left.trans hχK
  have hL0 : ∀ x ∉ B ∪ H, L x = 0 := cutoff_residual_vanishes (b p) hχD hLw htrans
  have hbSlice (i j : (I dim)) : ContDiff ℝ ∞ (b p i j) :=
    Elliptic.Strict.jointSmooth_slice (F := fun p => b p i j) (hb i j) p
  have hLcont : Continuous L := by
    unfold L Lop
    exact continuous_finsetSum _ fun i _ => (contDiff_pd_apply
      (ContDiff.sum fun j _ => (hbSlice i j).mul (contDiff_pd_apply hu))).continuous
  have hLi : Integrable (fun x => L x ^ 2) :=
    (hLcont.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hB.union hH) (fun x hx => by change L x ^ 2 = 0; rw [hL0 x hx, zero_pow (by decide)]))
  have hLeq (x : (X dim)) : chartVolume (g p) x * laplace (g p) u x = L x :=
    chartVolume_mul_laplace_eq_divergence isOpen_univ (hg p) hu.contDiffOn (mem_univ x)
  have hrestB : (∫ x in B, L x ^ 2) ≤ M * ∫ x in D, w x ^ 2 := by
    have hrest := hBrest p hp w hw.1 hLw hwD
    simp only [one_mul] at hrest
    exact hrest.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun _ => sq_nonneg _))
  have hrestH : (∫ x in H, L x ^ 2) ≤ M * ∫ x in S, w x ^ 2 := by
    have hrest := hHrest p hp w hw.1 hLw hwS
    simp only [one_mul] at hrest
    exact hrest.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (integral_nonneg fun _ => sq_nonneg _))
  change ‖qO‖ ≤ A * ‖qS‖ ^ γ * ‖q‖ ^ (1-γ)
  rw [mul_assoc]
  apply interpolation_of_weighted_sq hBO hOH (mul_nonneg hC hM)
    (norm_nonneg _) (norm_nonneg _) (harmonicRestrict_norm_le hD (hgD p) hOD q)
  intro τ hτ
  have hτ' : 0 ≤ τ := zero_le_one.trans (hτ₀.trans hτ)
  have huw : Continuous (fun x => (Real.exp (τ * ψ x) * u x) ^ 2) :=
    (((Real.continuous_exp.comp (continuous_const.mul hψ)).mul hu.continuous).pow 2)
  have hu_int : Integrable (fun x => (Real.exp (τ * ψ x) * u x) ^ 2) :=
    huw.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (show IsCompact (tsupport u) from huc) (fun x hx => by
        change (Real.exp (τ * ψ x) * u x) ^ 2 = 0
        rw [(notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds]
        simp))
  have hc := hCar p hp τ hτ u hu huc huK
  simp only [hLeq] at hc
  have hsplit := weighted_sq_split hτ' hC (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    hc hu_int hLi hB.measurableSet hH.measurableSet hO hL0 hψB hψH hψO
    (fun x hx => by simp [u, hχO x hx]) hwO
  have hcomb := weighted_two_collar_combine hC (Real.exp_pos (2*(τ*pB))).le
    (Real.exp_pos (2*(τ*pH))).le hrestB hrestH
  have hout := hsplit.trans hcomb
  change _ ≤ C * M * (_ * ‖q.1‖ ^ 2 + _)
  simpa only [hnormO, hnormS, hnormD] using hout

/-- The chart Carleman estimate and two compact collars give the source
interpolation exponent for the actual restriction on the harmonic L² space. -/
theorem exists_harmonicInterpolation_of_collarCutoff
    {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {D S O B H K : Set (X dim)} (hD : IsOpen D) (hS : IsOpen S) (hO : MeasurableSet O)
    (hSD : S ⊆ D) (hOD : O ⊆ D)
    (hB : IsCompact B) (hH : IsCompact H) (hBD : B ⊆ D) (hHS : H ⊆ S)
    (hgD : SmoothMetric D g)
    {χ θ : (X dim) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχD : tsupport χ ⊆ D) (hχK : tsupport χ ⊆ K)
    (hχO : ∀ x ∈ O, χ x = 1)
    (htrans : ∀ x ∉ B ∪ H, (χ =ᶠ[𝓝 x] fun _ => (0 : ℝ)) ∨ χ =ᶠ[𝓝 x] fun _ => (1 : ℝ))
    (hθ : ContDiff ℝ ∞ θ) {κ l e C τ₀ : ℝ}
    (hκ : 0 < κ) (hl : 0 < l) (hκl : κ * l ≤ 1/4)
    (he : 0 ≤ e) (he4 : 4 * e < κ * l^2)
    (hC : 0 ≤ C) (hτ₀ : 1 ≤ τ₀)
    (hθB : ∀ x ∈ B, strictHeight κ (θ x) ≤ strictHeight κ (-l + 3*e))
    (hθH : ∀ x ∈ H, strictHeight κ (θ x) ≤ strictHeight κ (l + 3*e))
    (hθO : ∀ x ∈ O, strictHeight κ (-e) ≤ strictHeight κ (θ x))
    (hCar : ∀ τ : ℝ, τ₀ ≤ τ → ∀ w : (X dim) → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, coordDeriv i (fun y => Real.exp (τ * strictHeight κ (θ y)) * w y) x ^ 2) +
        τ^3 * (∫ x, (Real.exp (τ * strictHeight κ (θ x)) * w x)^2) ≤
        C * ∫ x, Real.exp (2*(τ * strictHeight κ (θ x))) * (chartVolume g x * laplace g w x)^2) :
    ∃ A γ : ℝ, 0 < A ∧ 1/2 < γ ∧ γ < 1 ∧
      HarmonicInterpolation hD hgD hSD hOD A γ := by
  let ψ (x : (X dim)) := strictHeight κ (θ x)
  have hψ : Continuous ψ := hθ.continuous.sub (continuous_const.mul (hθ.continuous.pow 2))
  obtain ⟨ha,hb,hγ₁,hγ₂⟩ := strictExponent_bounds hκ hl hκl he he4
  have hb' (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff g q.2 i j) :=
    (contDiffOn_univ.mp (contDiffOn_divergenceCoeff hg i j)).comp contDiff_snd
  obtain ⟨A,hA,h⟩ := exists_family_harmonicInterpolation_of_collarCutoff
    (isCompact_singleton : IsCompact ({(0 : ℝ)} : Set ℝ)) (fun _ => g) (fun _ => hg) hb'
    hD hS hO hSD hOD hB hH hBD hHS (fun _ => hgD) hχ hχc hχD hχK hχO htrans hψ
    (sub_pos.mp ha) (sub_pos.mp hb) hC hτ₀ hθB hθH hθO (fun _ _ => hCar)
  exact ⟨A,_,hA,hγ₁,hγ₂,h 0 (mem_singleton _)⟩

end CalderonN
