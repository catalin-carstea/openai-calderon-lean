module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Affine
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Segment
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

public section

noncomputable section
open AffineMap Filter MeasureTheory Set
open scoped ContDiff ENNReal Interval Topology

namespace CalderonPatch

private theorem sq_integral_le_measure_mul_integral_sq
    {A : Type*} [MeasurableSpace A] {μ : Measure A} [IsFiniteMeasure μ]
    (hm : 0 < μ.real univ) {u : A → ℝ} (h : Integrable u μ)
    (h₂ : Integrable (fun x => (u x)^2) μ) :
    (∫ x, u x ∂μ)^2 ≤ μ.real univ * ∫ x, (u x)^2 ∂μ := by
  let c := (∫ x, u x ∂μ) / μ.real univ
  have hz : 0 ≤ ∫ x, (u x - c)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hp (x : A) : (u x - c)^2 = (u x)^2 - (2 * c) * u x + c^2 := by ring
  simp_rw [hp] at hz
  change 0 ≤ ∫ x, (((fun x : A => (u x)^2) - (fun x => (2 * c) * u x)) +
    (fun _ => (c^2 : ℝ)) : A → ℝ) x ∂μ at hz
  rw [integral_add' (h₂.sub (h.const_mul _)) (integrable_const _),
    integral_sub' h₂ (h.const_mul _), integral_const_mul, integral_const, smul_eq_mul] at hz
  apply le_of_sub_nonneg
  have hc : c * μ.real univ = ∫ x, u x ∂μ := div_mul_cancel₀ _ hm.ne'
  rw [← hc] at hz ⊢
  nlinarith [mul_nonneg hm.le hz]

/-- The fundamental theorem of calculus and Cauchy–Schwarz on
a closed interval. -/
theorem sq_sub_le_mul_integral_sq_of_hasDerivAt
    {a b : ℝ} (hab : a ≤ b) {u d : ℝ → ℝ}
    (hD : ∀ t, HasDerivAt u (d t) t) (hd : Continuous d) :
    (u b - u a)^2 ≤ (b - a) * ∫ t in Icc a b, (d t)^2 := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hd.intervalIntegrable a b)
  rw [intervalIntegral.integral_of_le hab'.le, ← integral_Icc_eq_integral_Ioc] at hFTC
  have hm : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab'.le)]
  have hSq := sq_integral_le_measure_mul_integral_sq
    (μ := volume.restrict (Icc a b)) (by rw [hm]; exact sub_pos.mpr hab')
    (hd.continuousOn.integrableOn_compact isCompact_Icc)
    ((hd.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  rwa [hm,hFTC] at hSq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fundamental theorem of calculus and Cauchy–Schwarz on a unit
parameter interval bound a squared difference by the integrated
squared differential along its segment. -/
theorem sq_sub_le_integral_lineMap_fderiv {u : E → ℝ} (h : ContDiff ℝ 1 u)
    (x y : E) :
    (u y - u x)^2 ≤ ‖y - x‖^2 *
      ∫ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (lineMap x y t)‖^2 := by
  let d (t : ℝ) := fderiv ℝ u (lineMap x y t) (y - x)
  let q (t : ℝ) := ‖fderiv ℝ u (lineMap x y t)‖^2
  have hLine : Continuous (lineMap x y : ℝ → E) :=
    continuous_iff_continuousAt.mpr fun _ => hasDerivAt_lineMap.continuousAt
  have hc := (h.continuous_fderiv one_ne_zero).comp hLine
  have hd : Continuous d := hc.clm_apply continuous_const
  have hq : Continuous q := hc.norm.pow 2
  have hDt (t : ℝ) : HasDerivAt (u ∘ lineMap x y) (d t) t := by
    exact ((h.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt t hasDerivAt_lineMap
  have hSq := sq_sub_le_mul_integral_sq_of_hasDerivAt zero_le_one hDt hd
  simp only [Function.comp_apply,lineMap_apply_one,lineMap_apply_zero,sub_zero,one_mul] at hSq
  refine hSq.trans ?_
  rw [← integral_const_mul]
  apply setIntegral_mono_on ((hd.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    ((hq.const_mul _).continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
  intro t _
  have hN := (fderiv ℝ u (lineMap x y t)).le_opNorm (y - x)
  have hN' : (d t)^2 ≤ (‖fderiv ℝ u (lineMap x y t)‖ * ‖y - x‖)^2 := by
    rw [← sq_abs (d t)]
    exact pow_le_pow_left₀ (abs_nonneg _) hN _
  rwa [mul_pow,mul_comm] at hN'


section Haar

open scoped Pointwise

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ] {K : Set E}

/-- For the first half of the segment parameter, moving the first
endpoint has Jacobian at least `2⁻ᵈ`. Convexity keeps its translated
and scaled image inside the set of integration. -/
private theorem setIntegral_lineMap_left_le
    (hK : IsCompact K) (hC : Convex ℝ K)
    {q : E → ℝ} (hq : Continuous q) (hq₀ : ∀ x ∈ K, 0 ≤ q x)
    {y : E} (hy : y ∈ K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    (∫ x in K, q (lineMap x y t) ∂μ) ≤
      (2 : ℝ)^Module.finrank ℝ E * ∫ x in K, q x ∂μ := by
  have ht₁ : 0 < 1 - t := by linarith [ht.2]
  let e := Homeomorph.addRight (t • y)
  let V := e '' ((1 - t) • K)
  have hVK : V ⊆ K := by
    rintro _ ⟨_,hw,rfl⟩
    obtain ⟨x,hx,rfl⟩ := show _ ∈ (fun x : E => (1 - t) • x) '' K from hw
    change (1 - t) • x + t • y ∈ K
    rw [← lineMap_apply_module]
    exact hC.lineMap_mem hx hy ⟨ht.1,by linarith [ht.2]⟩
  have hJ : ((1 - t)^Module.finrank ℝ E)⁻¹ ≤ (2 : ℝ)^Module.finrank ℝ E := by
    rw [← inv_pow]
    refine pow_le_pow_left₀ (inv_nonneg.mpr ht₁.le) ?_ _
    simpa only [inv_inv] using (inv_le_inv₀ ht₁ (by norm_num : 0 < (2 : ℝ)⁻¹)).2 (by linarith [ht.2])
  calc
    _ = ((1 - t)^Module.finrank ℝ E)⁻¹ *
        ∫ w in (1 - t) • K, q (e w) ∂μ := by
      simp_rw [lineMap_apply_module]
      exact Measure.setIntegral_comp_smul_of_pos μ (fun w => q (e w)) K ht₁
    _ = ((1 - t)^Module.finrank ℝ E)⁻¹ * ∫ z in V, q z ∂μ := by
      exact congrArg (((1 - t)^Module.finrank ℝ E)⁻¹ * ·)
        ((measurePreserving_add_right μ (t • y)).setIntegral_image_emb
          e.toMeasurableEquiv.measurableEmbedding q ((1 - t) • K)).symm
    _ ≤ ((1 - t)^Module.finrank ℝ E)⁻¹ * ∫ z in K, q z ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (pow_nonneg ht₁.le _))
      exact setIntegral_mono_set (hq.continuousOn.integrableOn_compact hK)
        (ae_restrict_of_forall_mem hK.isClosed.measurableSet hq₀)
        (Eventually.of_forall hVK)
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ
      (setIntegral_nonneg hK.isClosed.measurableSet hq₀)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
private theorem continuous_lineMap_uncurry : Continuous
    (fun p : (E × E) × ℝ => lineMap p.1.1 p.1.2 p.2) := by
  simp_rw [lineMap_apply_module]
  fun_prop

/-- Uniform averaging bound along the segments between all pairs of
points. At the second half of the parameter interval the endpoint
roles are exchanged. -/
private theorem doubleIntegral_lineMap_le
    (hK : IsCompact K) (hC : Convex ℝ K)
    {q : E → ℝ} (hq : Continuous q) (hq₀ : ∀ x ∈ K, 0 ≤ q x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ y in K, ∫ x in K, q (lineMap x y t) ∂μ ∂μ) ≤
      μ.real K * ((2 : ℝ)^Module.finrank ℝ E * ∫ x in K, q x ∂μ) := by
  let d := (2 : ℝ)^Module.finrank ℝ E * ∫ x in K, q x ∂μ
  let ν := μ.restrict K
  let : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hF (s : ℝ) : Integrable (fun p : E × E => q (lineMap p.2 p.1 s)) (ν.prod ν) := by
    have hCONT : Continuous (fun p : E × E => q (lineMap p.2 p.1 s)) :=
      hq.comp (continuous_lineMap_uncurry.comp
        ((continuous_snd.prodMk continuous_fst).prodMk continuous_const))
    simpa only [ν,IntegrableOn,Measure.prod_restrict] using
      hCONT.continuousOn.integrableOn_compact (μ := μ.prod μ) (hK.prod hK)
  have hSmall {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
      (∫ y in K, ∫ x in K, q (lineMap x y s) ∂μ ∂μ) ≤ μ.real K * d := by
    calc
      _ ≤ ∫ _ in K, d ∂μ := setIntegral_mono_on (hF s).integral_prod_left
        (integrable_const _) hK.isClosed.measurableSet
        (fun _ hy => setIntegral_lineMap_left_le μ hK hC hq hq₀ hy hs)
      _ = _ := by rw [setIntegral_const,smul_eq_mul]
  by_cases ht' : t ≤ 1 / 2
  · exact hSmall ⟨ht.1,ht'⟩
  · have hs : 1 - t ∈ Icc (0 : ℝ) (1 / 2) := ⟨sub_nonneg.mpr ht.2,by linarith⟩
    have hSwap := integral_integral_swap (f := fun y x => q (lineMap x y t)) (hF t)
    rw [hSwap]
    simpa only [lineMap_apply_one_sub] using hSmall hs


set_option maxHeartbeats 400000 in
/-- The squared distance from the mean of a smooth function on a
compact convex set is controlled by its squared differential.
The estimate uses the diameter bound `D` and the Jacobians of
segment contractions. -/
theorem integral_sq_sub_average_le_of_convex
    (hK : IsCompact K) (hC : Convex ℝ K) (hm : 0 < μ.real K)
    {D : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖y - x‖ ≤ D)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) :
    (∫ x in K, (u x - (∫ y in K, u y ∂μ) / μ.real K)^2 ∂μ) ≤
      D^2 * 2^Module.finrank ℝ E * ∫ x in K, ‖fderiv ℝ u x‖^2 ∂μ := by
  let ν := μ.restrict K
  let : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  let T := Icc (0 : ℝ) 1
  let τ := volume.restrict T
  let c := (∫ y, u y ∂ν) / μ.real K
  let q (x : E) := ‖fderiv ℝ u x‖^2
  let F (p : E × E) (t : ℝ) := q (lineMap p.2 p.1 t)
  let W (p : E × E) := (u p.1 - u p.2)^2
  have hq : Continuous q := (hu.continuous_fderiv one_ne_zero).norm.pow 2
  have hC₁ : Continuous (Function.uncurry F) :=
    hq.comp (continuous_lineMap_uncurry.comp
      ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd))
  have hF : Integrable (Function.uncurry F) ((ν.prod ν).prod τ) := by
    simpa only [ν,τ,IntegrableOn,Measure.prod_restrict] using
      hC₁.continuousOn.integrableOn_compact (μ := (μ.prod μ).prod volume)
        ((hK.prod hK).prod isCompact_Icc)
  have hFt (t : ℝ) : Integrable (fun p => F p t) (ν.prod ν) := by
    have ht : Continuous (fun p : E × E => q (lineMap p.2 p.1 t)) :=
      hq.comp (continuous_lineMap_uncurry.comp
        ((continuous_snd.prodMk continuous_fst).prodMk continuous_const))
    simpa only [ν,F,IntegrableOn,Measure.prod_restrict] using
      ht.continuousOn.integrableOn_compact (μ := μ.prod μ) (hK.prod hK)
  have hW : Integrable W (ν.prod ν) := by
    have hCW : Continuous W :=
      ((hu.continuous.comp continuous_fst).sub (hu.continuous.comp continuous_snd)).pow 2
    simpa only [ν,IntegrableOn,Measure.prod_restrict] using
      hCW.continuousOn.integrableOn_compact (μ := μ.prod μ) (hK.prod hK)
  have hMean (y : E) : μ.real K * (u y - c)^2 ≤ ∫ x, W (y,x) ∂ν := by
    let v (x : E) := u y - u x
    have hv : Continuous v := continuous_const.sub hu.continuous
    have hm' : ν.real univ = μ.real K := by
      change (μ.restrict K).real univ = μ.real K
      rw [Measure.real,Measure.restrict_apply_univ]
      rfl
    have hV := sq_integral_le_measure_mul_integral_sq (μ := ν) (hm' ▸ hm)
      (hv.continuousOn.integrableOn_compact hK)
      ((hv.pow 2).continuousOn.integrableOn_compact hK)
    have hI : (∫ x, v x ∂ν) = μ.real K * (u y - c) := by
      simp only [v]
      rw [integral_sub (integrable_const _) (hu.continuous.continuousOn.integrableOn_compact hK),
        integral_const,smul_eq_mul,hm']
      have hc : μ.real K * c = ∫ x, u x ∂ν := mul_div_cancel₀ _ hm.ne'
      rw [mul_sub,hc]
    rw [hI,hm',mul_pow] at hV
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [pow_two,mul_assoc,W,v] using hV
  have hPair : ∀ᵐ p ∂ν.prod ν, W p ≤ D^2 * ∫ t, F p t ∂τ := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hK.isClosed.measurableSet.prod hK.isClosed.measurableSet)]
      with p hp
    have hPoint := sq_sub_le_integral_lineMap_fderiv hu p.2 p.1
    exact hPoint.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hD p.2 hp.2 p.1 hp.1) _)
      (integral_nonneg fun t => sq_nonneg _))
  have hT : τ.real univ = 1 := by
    change (volume.restrict T).real univ = 1
    rw [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc]
    simp
  have hParam :
      (∫ p, ∫ t, F p t ∂τ ∂ν.prod ν) ≤
        μ.real K * ((2 : ℝ)^Module.finrank ℝ E * ∫ x, q x ∂ν) := by
    rw [integral_integral_swap (f := F) hF]
    refine (setIntegral_mono_on (s := T) hF.integral_prod_right
      (integrable_const (μ.real K * ((2 : ℝ)^Module.finrank ℝ E * ∫ x, q x ∂ν)))
      measurableSet_Icc ?_).trans_eq ?_
    · intro t ht
      change (∫ p, F p t ∂ν.prod ν) ≤ _
      rw [← integral_integral (f := fun y x => F (y,x) t) (hFt t)]
      exact doubleIntegral_lineMap_le μ hK hC hq (fun x _ => sq_nonneg _) ht
    · change (∫ _ : ℝ, _ ∂τ) = _
      rw [integral_const,smul_eq_mul,hT,one_mul]
  change (∫ x, (u x - c)^2 ∂ν) ≤ _
  apply (mul_le_mul_iff_right₀ hm).mp
  calc
    _ = ∫ y, μ.real K * (u y - c)^2 ∂ν := (integral_const_mul _ _).symm
    _ ≤ ∫ y, ∫ x, W (y,x) ∂ν ∂ν := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun y => mul_nonneg hm.le (sq_nonneg (u y - c)))
        hW.integral_prod_left (Eventually.of_forall hMean)
    _ = ∫ p, W p ∂ν.prod ν := integral_integral (f := fun y x => W (y,x)) hW
    _ ≤ ∫ p, D^2 * (∫ t, F p t ∂τ) ∂ν.prod ν :=
      integral_mono_ae hW (hF.integral_prod_left.const_mul _) hPair
    _ = D^2 * ∫ p, ∫ t, F p t ∂τ ∂ν.prod ν := integral_const_mul _ _
    _ ≤ D^2 * (μ.real K * ((2 : ℝ)^Module.finrank ℝ E * ∫ x, q x ∂ν)) :=
      mul_le_mul_of_nonneg_left hParam (sq_nonneg D)
    _ = _ := by change _ = μ.real K * (D^2 * 2^Module.finrank ℝ E * ∫ x, q x ∂ν); ring

end Haar

end CalderonPatch
