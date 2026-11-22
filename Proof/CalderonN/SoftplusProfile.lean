module

public import Proof.CalderonN.Radius
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Adapted from `RadiusProfile`, `RadiusProfileBounds` and `ProfileUniform` in the earlier anisotropic Calderón
formalization, revision d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

noncomputable section

namespace CalderonN.SoftplusProfile



noncomputable def logSlope (δ t : ℝ) : ℝ :=
  Real.exp (t/δ) / (δ * (1+Real.exp (t/δ)) * Real.log (1+Real.exp (t/δ)))

noncomputable def logSlopeDerivative (δ t : ℝ) : ℝ :=
  Real.exp (t/δ) * (Real.log (1+Real.exp (t/δ))-Real.exp (t/δ)) /
    (δ^2 * (1+Real.exp (t/δ))^2 * (Real.log (1+Real.exp (t/δ)))^2)

lemma log_exp_add_one_pos (s : ℝ) : 0 < Real.log (1+Real.exp s) := by
  apply Real.log_pos
  linarith [Real.exp_pos s]

lemma softplus_pos (δ t : ℝ) (hδ : 0 < δ) : 0 < softplus δ t :=
  CalderonN.softplus_pos hδ t

theorem hasDerivAt_softplus (δ t : ℝ) (hδ : δ ≠ 0) :
    HasDerivAt (softplus δ) (Real.exp (t/δ)/(1+Real.exp (t/δ))) t :=
  CalderonN.hasDerivAt_softplus hδ t

lemma softplus_derivative_pos (δ t : ℝ) : 0 < Real.exp (t/δ)/(1+Real.exp (t/δ)) := by
  positivity

lemma softplus_derivative_lt_one (δ t : ℝ) : Real.exp (t/δ)/(1+Real.exp (t/δ)) < 1 := by
  apply (div_lt_one (by positivity)).2
  linarith

lemma logSlope_pos (δ t : ℝ) (hδ : 0 < δ) : 0 < logSlope δ t := by
  unfold logSlope
  exact div_pos (Real.exp_pos _) (by positivity [log_exp_add_one_pos (t/δ)])

theorem hasDerivAt_log_softplus (δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (fun u => Real.log (softplus δ u)) (logSlope δ t) t := by
  have h := (hasDerivAt_softplus δ t (ne_of_gt hδ)).log (ne_of_gt (softplus_pos δ t hδ))
  convert h using 1
  unfold softplus logSlope
  field_simp

theorem hasDerivAt_logSlope (δ t : ℝ) (hδ : 0 < δ) :
    HasDerivAt (logSlope δ) (logSlopeDerivative δ t) t := by
  have hLp := log_exp_add_one_pos (t/δ)
  have he : HasDerivAt (fun u : ℝ => Real.exp (u/δ)) (Real.exp (t/δ)/δ) t := by
    simpa only [id_eq,div_eq_mul_inv,one_mul] using ((hasDerivAt_id' t).div_const δ).exp
  have hs : HasDerivAt (fun u : ℝ => 1+Real.exp (u/δ)) (Real.exp (t/δ)/δ) t := by
    convert! (hasDerivAt_const t (1:ℝ)).add he using 1 <;> simp only [Pi.add_apply,zero_add]
  have hL := hs.log (by positivity)
  have hden : HasDerivAt
      (fun u : ℝ => δ*(1+Real.exp (u/δ))*Real.log (1+Real.exp (u/δ)))
      (δ*(Real.exp (t/δ)/δ)*Real.log (1+Real.exp (t/δ))+
        δ*(1+Real.exp (t/δ))*((Real.exp (t/δ)/δ)/(1+Real.exp (t/δ)))) t := by
    convert! (hs.const_mul δ).mul hL using 1 <;> simp only [Pi.mul_apply]
  have h := he.div hden (by positivity)
  convert h using 1
  · rfl
  · unfold logSlopeDerivative
    field_simp [ne_of_gt hδ,ne_of_gt hLp]
    <;> ring

lemma logSlopeDerivative_neg (δ t : ℝ) (hδ : 0 < δ) : logSlopeDerivative δ t < 0 := by
  have he : 0 < Real.exp (t/δ) := Real.exp_pos _
  have hL : Real.log (1+Real.exp (t/δ)) < Real.exp (t/δ) := by
    have h := Real.log_lt_sub_one_of_pos (by positivity : 0 < 1+Real.exp (t/δ))
      (by linarith : 1+Real.exp (t/δ) ≠ 1)
    linarith
  unfold logSlopeDerivative
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg he (sub_neg.mpr hL))
    (by positivity [log_exp_add_one_pos (t/δ)])

lemma logSlope_mul_softplus (δ t : ℝ) (hδ : 0 < δ) :
    logSlope δ t * softplus δ t = Real.exp (t/δ)/(1+Real.exp (t/δ)) := by
  have hL : Real.log (1+Real.exp (t/δ)) ≠ 0 := ne_of_gt (log_exp_add_one_pos _)
  unfold logSlope softplus
  field_simp

lemma logSlope_le_inv_softplus (δ t : ℝ) (hδ : 0 < δ) :
    logSlope δ t ≤ 1 / softplus δ t := by
  apply (le_div_iff₀ (softplus_pos δ t hδ)).2
  rw [logSlope_mul_softplus δ t hδ]
  exact le_of_lt (softplus_derivative_lt_one δ t)

lemma le_softplus (δ t : ℝ) (hδ : 0 < δ) : t ≤ softplus δ t := by
  have h := Real.log_le_log (Real.exp_pos (t/δ))
    (by linarith : Real.exp (t/δ) ≤ 1+Real.exp (t/δ))
  rw [Real.log_exp] at h
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt hδ)
  unfold softplus
  have hi : δ * (t/δ) = t := by field_simp
  simpa only [hi] using hm

lemma softplus_le_delta_log_two (δ t : ℝ) (hδ : 0 < δ) (ht : t ≤ 0) :
    softplus δ t ≤ δ * Real.log 2 := by
  have he : Real.exp (t/δ) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonpos_of_nonpos_of_nonneg ht (le_of_lt hδ))
  have h := Real.log_le_log (by positivity : 0 < 1+Real.exp (t/δ))
    (by linarith : 1+Real.exp (t/δ) ≤ 2)
  exact mul_le_mul_of_nonneg_left h (le_of_lt hδ)

theorem strictMono_softplus (δ : ℝ) (hδ : 0 < δ) : StrictMono (softplus δ) :=
  strictMono_of_hasDerivAt_pos (fun t => hasDerivAt_softplus δ t (ne_of_gt hδ))
    (fun t => softplus_derivative_pos δ t)

theorem strictMonoOn_softplus_delta (t : ℝ) :
    StrictMonoOn (fun δ => softplus δ t) (Set.Ioi 0) :=
  CalderonN.strictMonoOn_softplus_scale t

lemma softplus_le_unit (δ t : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    softplus δ t ≤ softplus 1 t :=
  (strictMonoOn_softplus_delta t).monotoneOn hδ (by norm_num) hδ₁

lemma softplus_le_log_exp_upper (δ t T : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ht : t ≤ T) :
    softplus δ t ≤ Real.log (1+Real.exp T) := by
  have h := (softplus_le_unit δ t hδ hδ₁).trans
    ((strictMono_softplus 1 (by norm_num)).monotone ht)
  simpa only [softplus,div_one,one_mul] using h

lemma softplus_small_of_nonpos (δ t ε : ℝ) (hδ : 0 < δ) (ht : t ≤ 0)
    (hsmall : δ ≤ ε / Real.log 2) : softplus δ t ≤ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (softplus_le_delta_log_two δ t hδ ht).trans ((le_div_iff₀ hlog).mp hsmall)

theorem radius_gradient_scale_bound (δ t R C b : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hp : 2 ≤ p) (hbound : b ≤ (p:ℝ)*C*logSlope δ t) :
    (R*(softplus δ t)^p)*b^2 ≤ R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2) := by
  have hℓ := softplus_pos δ t hδ
  have ha := logSlope_pos δ t hδ
  have hsq : b^2 ≤ ((p:ℝ)*C*logSlope δ t)^2 := by
    nlinarith
  have hm : 0≤logSlope δ t*softplus δ t := by positivity
  have hm₁ : logSlope δ t*softplus δ t≤1 := by
    rw [logSlope_mul_softplus δ t hδ]
    exact le_of_lt (softplus_derivative_lt_one δ t)
  have hsq₁ : (logSlope δ t*softplus δ t)^2≤1 := by nlinarith
  have hpow : (softplus δ t)^p = (softplus δ t)^(p-2)*(softplus δ t)^2 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    (R*(softplus δ t)^p)*b^2 ≤ (R*(softplus δ t)^p)*((p:ℝ)*C*logSlope δ t)^2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2))*(logSlope δ t*softplus δ t)^2 := by
      rw [hpow]
      ring
    _ ≤ (R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2))*1 :=
      mul_le_mul_of_nonneg_left hsq₁ (by positivity)
    _ = R*(p:ℝ)^2*C^2*(softplus δ t)^(p-2) := mul_one _

theorem radius_gradient_uniform_scale_bound (δ t T R C b : ℝ) (p : ℕ)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (ht : t ≤ T)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hp : 2 ≤ p) (hbound : b ≤ (p:ℝ)*C*logSlope δ t) :
    (R*(softplus δ t)^p)*b^2 ≤ R*(p:ℝ)^2*C^2*(Real.log (1+Real.exp T))^(p-2) := by
  have hbase := radius_gradient_scale_bound δ t R C b p hδ hR hC hb hp hbound
  have hpow := pow_le_pow_left₀ (le_of_lt (softplus_pos δ t hδ))
    (softplus_le_log_exp_upper δ t T hδ hδ₁ ht) (p-2)
  exact hbase.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

lemma one_lt_logSlope_mul_delta_add_softplus (δ s : ℝ) (hδ : 0 < δ) :
    1 < logSlope δ s * (δ + softplus δ s) := by
  have he := Real.exp_pos (s/δ)
  have hL := log_exp_add_one_pos (s/δ)
  have hLe : Real.log (1 + Real.exp (s/δ)) < Real.exp (s/δ) := by
    have h := Real.log_lt_sub_one_of_pos
      (by positivity : 0 < 1 + Real.exp (s/δ))
      (by linarith : 1 + Real.exp (s/δ) ≠ 1)
    linarith
  unfold logSlope softplus
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ (by positivity :
    0 < δ * (1 + Real.exp (s/δ)) * Real.log (1 + Real.exp (s/δ)))).2
  nlinarith [mul_pos hδ (sub_pos.mpr hLe)]

lemma logSlope_uniform_lower_bound (δ s T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : s ≤ T) :
    1 / (1 + Real.log (1 + Real.exp T)) ≤ logSlope δ s := by
  have hU : 0 < 1 + Real.log (1 + Real.exp T) := by
    linarith [log_exp_add_one_pos T]
  have ha := logSlope_pos δ s hδ
  have hb : δ + softplus δ s ≤ 1 + Real.log (1 + Real.exp T) := by
    linarith [softplus_le_log_exp_upper δ s T hδ hδ1 hs]
  apply (div_le_iff₀ hU).2
  exact le_trans (le_of_lt (one_lt_logSlope_mul_delta_add_softplus δ s hδ))
    (mul_le_mul_of_nonneg_left hb (le_of_lt ha))


end CalderonN.SoftplusProfile
