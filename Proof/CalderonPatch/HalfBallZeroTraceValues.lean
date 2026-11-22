module

public import Proof.CalderonPatch.HalfSpaceTangentialExtension
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Extension

import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory Set TopologicalSpace Filter Metric TauCeti
open scoped ENNReal ContDiff Topology

namespace CalderonPatch

open CalderonN (X I axis)

variable {n : ℕ} [NeZero n]
local notation "E" => X n
local notation "H" => positiveHalfSpaceOpens n
local notation "μ" => (volume : Measure E)

private theorem exists_thin_box {x₀ : E} (hx₀ : x₀ 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ t ∈ Ioo 0 δ,
      ∃ K : Set E, MeasurableSet K ∧ K ⊆ ball x₀ r ∩ {x : E | 0 < x 0 ∧ x 0 < t} ∧
        (μ).real K = t * c := by
  classical
  let δ := r / (2 * ((n : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let c := ∏ i ∈ (Finset.univ.erase (0 : I n)), 2 * δ
  have hc : 0 < c := Finset.prod_pos fun _ _ => by positivity
  refine ⟨δ,c,hδ,hc,fun t ht => ?_⟩
  let a (i : I n) := if i = 0 then 0 else x₀ i - δ
  let b (i : I n) := if i = 0 then t else x₀ i + δ
  let K := (WithLp.ofLp : E → (I n → ℝ)) ⁻¹' Set.pi univ (fun i => Ioo (a i) (b i))
  have hPi : MeasurableSet (Set.pi univ (fun i => Ioo (a i) (b i))) :=
    MeasurableSet.pi (Set.to_countable _) (fun i _ => measurableSet_Ioo)
  have hBox (x : E) (hx : x ∈ K) (i : I n) : a i < x i ∧ x i < b i := hx i (mem_univ i)
  refine ⟨K,hPi.preimage (PiLp.volume_preserving_ofLp (I n)).measurable,?_,?_⟩
  · intro x hx
    refine ⟨mem_ball.2 ?_,by simpa [a,b] using hBox x hx 0⟩
    rw [dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) hr.le,EuclideanSpace.real_norm_sq_eq]
    have hnorm (i : I n) : |(x-x₀) i| ≤ δ := by
      have hi := hBox x hx i
      by_cases hi₀ : i = 0
      · subst i
        simp only [a,b,ite_true] at hi
        change |x 0 - x₀ 0| ≤ δ
        rw [hx₀,sub_zero,abs_of_pos hi.1]
        exact hi.2.le.trans ht.2.le
      · simp only [a,b,ite_eq_right hi₀] at hi
        change |x i - x₀ i| ≤ δ
        exact abs_le.2 ⟨by linarith [hi.1],by linarith [hi.2]⟩
    have hSq : ∑ i : I n, ((x-x₀) i)^2 ≤ n * δ^2 := by
      calc
        _ ≤ ∑ _ : I n, δ^2 := Finset.sum_le_sum fun i _ =>
          (sq_le_sq).2 (by simpa only [abs_of_pos hδ] using hnorm i)
        _ = _ := by simp
    have hEq : r = 2 * ((n : ℝ) + 1) * δ := by
      dsimp [δ]
      field_simp
    have hNd : (n : ℝ) * δ^2 < (2 * ((n : ℝ) + 1) * δ)^2 := by
      have h₁ : (n : ℝ) < (2 * ((n : ℝ) + 1))^2 := by
        nlinarith [sq_nonneg (n : ℝ)]
      simpa only [mul_pow] using mul_lt_mul_of_pos_right h₁ (sq_pos_of_pos hδ)
    exact hSq.trans_lt (hEq.symm ▸ hNd)
  · change ((μ) K).toReal = _
    rw [(PiLp.volume_preserving_ofLp (I n)).measure_preimage hPi.nullMeasurableSet,
      Real.volume_pi_Ioo_toReal (fun i => ?_)]
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : I n))]
      simp only [a,b,ite_true,sub_zero,c]
      congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hne := (Finset.mem_erase.mp hi).1
      simp only [ite_eq_right hne]
      ring
    · by_cases hi : i = 0
      · simp [a,b,hi,ht.1.le]
      · simp only [a,b,ite_eq_right hi]
        linarith

/-- A continuous one-sided representative of a zero-trace half-space
function has zero face value. The (L^2) bound on normal difference
quotients of its zero extension rules out a boundary jump. -/
theorem eq_zero_on_face_of_locally_continuous_zero_trace
    (u : W1p0 μ H 2) {S : Set E} (hS : IsOpen S)
    {f : E → ℝ} (hf : ContinuousOn f (S ∩ inwardHalfSpace n))
    (hu : (W1p.value (u : W1p μ H 2) : E → ℝ) =ᵐ[(μ).restrict (S ∩ positiveHalfSpace n)] f)
    {x₀ : E} (hx₀ : x₀ ∈ S) (hx : x₀ 0 = 0) : f x₀ = 0 := by
  by_contra h0
  let B := |f x₀| / 2
  have hB : 0 < B := half_pos (abs_pos.mpr h0)
  have hY : x₀ ∈ S ∩ inwardHalfSpace n := ⟨hx₀,mem_inwardHalfSpace.mpr hx.ge⟩
  have hCont := (hf x₀ hY).abs
  have hNear : ∀ᶠ x in 𝓝[S ∩ inwardHalfSpace n] x₀, B < |f x| :=
    hCont.eventually (eventually_gt_nhds (half_lt_self (abs_pos.mpr h0)))
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp hS x₀ hx₀
  obtain ⟨r',hr',hR⟩ := Metric.mem_nhdsWithin_iff.mp hNear
  let R := min r r'
  have hRp : 0 < R := lt_min hr hr'
  have hStrong (x : E) (hxr : x ∈ ball x₀ R) (hxH : x ∈ (H : Set E)) : B ≤ |f x| := by
    exact (hR ⟨ball_subset_ball (min_le_right _ _) hxr,
      hrsub (ball_subset_ball (min_le_left _ _) hxr),positiveHalfSpace_subset_inwardHalfSpace hxH⟩).le
  obtain ⟨δ,c,hδ,hc,hBox⟩ := exists_thin_box hx hRp
  let w : W1p μ ⊤ 2 := W1p0.extendByZeroL (le_top : H ≤ ⊤) u
  let J := ‖W1p.gradient w‖ ^ 2
  have hJ : 0 ≤ J := sq_nonneg _
  let t := min (δ / 2) (c * B^2 / (J+1))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨K,hK,hKr,hKV⟩ := hBox t ⟨ht,htδ⟩
  let v : E := axis (0 : I n)
  have hv : ‖v‖ = 1 := by simp [v,axis]
  let q := W1p.differenceQuotient (mu := μ) (V := ⊤) (Omega := ⊤) le_rfl v (-t)
    (mapsTo_univ _ _) w
  have hUB : ‖W1p.value q‖ ^ 2 ≤ J := by
    have hQ := W1p.norm_value_differenceQuotient_le (by norm_num) v (-t) w
    rw [hv,one_mul] at hQ
    exact pow_le_pow_left₀ (norm_nonneg _) hQ 2
  have hValue : (W1p.value w : E → ℝ) =ᵐ[μ]
      (H : Set E).indicator (W1p.value (u : W1p μ H 2) : E → ℝ) := by
    rw [show W1p.value w = _ from W1p0.value_extendByZeroL le_top u]
    simpa only [Opens.coe_top,Measure.restrict_univ] using
      coeFn_extendByZeroLpₗᵢ ℝ (H).isOpen.measurableSet (subset_univ (H : Set E))
        (W1p.value (u : W1p μ H 2))
  have hShift := (measurePreserving_add_right μ ((-t) • v)).quasiMeasurePreserving.ae_eq_comp hValue
  have hq : (W1p.value q : E → ℝ) =ᵐ[μ] fun x =>
      (-t)⁻¹ * (W1p.value w (x + (-t) • v) - W1p.value w x) := by
    simpa only [q,Opens.coe_top,Measure.restrict_univ] using
      W1p.value_differenceQuotient_ae (mu := μ) (V := ⊤) (Omega := ⊤) le_rfl v (-t) (mapsTo_univ _ _) w
  have hAE : (fun _ : E => (B/t)^2) ≤ᵐ[(μ).restrict K] fun x => (W1p.value q x)^2 := by
    have hUK : K ⊆ S ∩ positiveHalfSpace n := fun x hxK =>
      ⟨hrsub (ball_subset_ball (min_le_left _ _) ((hKr hxK).1)),mem_positiveHalfSpace.mpr (hKr hxK).2.1⟩
    filter_upwards [ae_restrict_mem hK,ae_restrict_of_ae hq,ae_restrict_of_ae hValue,
      ae_restrict_of_ae hShift,ae_restrict_of_ae_restrict_of_subset hUK hu] with x hxK h₁ h₂ h₃ h₄
    have hxH : x ∈ (H : Set E) := (hUK hxK).2
    have hOut : x + (-t) • v ∉ (H : Set E) := by
      change ¬ 0 < (x + (-t) • v) 0
      have hx' := (hKr hxK).2.2
      simp [v,axis]
      linarith
    dsimp only [Function.comp_apply] at h₃
    rw [h₁,h₂,h₃,indicator_of_mem hxH,indicator_of_notMem hOut,h₄,zero_sub,inv_neg,neg_mul_neg]
    apply sq_le_sq.mpr
    rw [abs_div,abs_of_pos hB,abs_of_pos ht,abs_mul,abs_inv,abs_of_pos ht,div_eq_mul_inv,mul_comm B]
    exact mul_le_mul_of_nonneg_left (hStrong x (hKr hxK).1 hxH) (inv_nonneg.mpr ht.le)
  have hI : Integrable (fun x => (W1p.value q x)^2) μ := by
    have h := (Lp.memLp (W1p.value q)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa only [Opens.coe_top,Measure.restrict_univ,ENNReal.toReal_ofNat,Real.rpow_two,
      Real.norm_eq_abs,sq_abs] using h
  have hballVol : (μ) (ball x₀ R) < (⊤ : ℝ≥0∞) := isBounded_ball.measure_lt_top
  have hfin : (μ) K ≠ ⊤ := ((measure_mono (hKr.trans inter_subset_left)).trans_lt hballVol).ne
  let : IsFiniteMeasure ((μ).restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hLower : t * c * (B/t)^2 ≤ ‖W1p.value q‖ ^ 2 := by
    rw [← hKV,← smul_eq_mul,← setIntegral_const,← W1p.integral_value_sq_eq_norm_value_sq]
    simp only [Opens.coe_top,setIntegral_univ]
    exact (setIntegral_mono_ae_restrict (integrable_const _) hI.integrableOn hAE).trans
      (setIntegral_le_integral hI (.of_forall fun x => sq_nonneg _))
  have hCross : c * B^2 ≤ t * J := by
    have h' := mul_le_mul_of_nonneg_right (hLower.trans hUB) ht.le
    have hEq : t * c * (B / t)^2 * t = c * B^2 := by field_simp
    simpa only [hEq,mul_comm J t] using h' 
  have htJ : t * J < c * B^2 := by
    have hle : t * (J+1) ≤ c * B^2 :=
      (le_div_iff₀ (by positivity : 0 < J+1)).mp (min_le_right _ _)
    nlinarith
  exact (not_lt_of_ge hCross) htJ

end CalderonPatch
