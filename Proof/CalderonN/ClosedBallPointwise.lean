module

public import Proof.CalderonN.Coordinates
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! The closed-ball Taylor estimate from the checked Theorem 3.1 release.
Degree `dim + 1` makes the remainder weight bounded after the change
of variables in the integral. -/

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Pointwise Topology ENNReal

namespace CalderonN

variable {dim : ℕ}

private theorem integral_le_sqrt_volume_mul_sqrt_sq
    {K : Set (X dim)} (hK : IsCompact K) (hVolume : 0 < volume.real K)
    {h : (X dim) → ℝ} (hh : Continuous h) :
    (∫ x in K, h x) ≤ Real.sqrt (volume.real K) * Real.sqrt (∫ x in K, h x ^ 2) := by
  let C := volume.real K
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_ne_top
  have hC : 0 < C := hVolume
  let m : ℝ := ∫ x in K, h x
  let q : ℝ := ∫ x in K, h x ^ 2
  have hI : IntegrableOn h K := hh.continuousOn.integrableOn_compact hK
  have hI₂ : IntegrableOn (fun x => h x ^ 2) K := (hh.pow 2).continuousOn.integrableOn_compact hK
  let a : ℝ := m / C
  have hA : 0 ≤ ∫ x in K, (h x - a)^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hPoly (x : (X dim)) : (h x - a)^2 = (h x)^2 - (2*a)*h x+a^2 := by ring
  simp_rw [hPoly] at hA
  have hc : Integrable (fun _ : (X dim) => a^2) (volume.restrict K) :=
    integrable_const _
  have hC₁ : IntegrableOn (fun x => (2*a)*h x) K := hI.const_mul _
  have hSub : IntegrableOn (fun x => (h x)^2-(2*a)*h x) K := hI₂.sub hC₁
  rw [integral_add hSub hc,integral_sub hI₂ hC₁,integral_const_mul,
    integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hA
  change 0 ≤ q - 2*a*m+C*a^2 at hA
  have he : q - 2*a*m+C*a^2 = (C*q-m^2)/C := by
    dsimp only [a]
    field_simp [hC.ne']
    ring
  rw [he] at hA
  have hSq : m^2 ≤ C*q := by
    have h := (le_div_iff₀ hC).mp hA
    linarith
  have hQ : 0 ≤ q := integral_nonneg (fun _ => sq_nonneg _)
  have hS : (Real.sqrt C * Real.sqrt q)^2 = C*q := by
    rw [mul_pow,Real.sq_sqrt hC.le,Real.sq_sqrt hQ]
  by_cases hm : 0 ≤ m
  · exact (sq_le_sq₀ hm (by positivity)).mp (hSq.trans_eq hS.symm)
  · exact (le_of_not_ge hm).trans (by positivity)

private theorem integral_sq_affine_le
    {K B : Set (X dim)} (hB : IsCompact B)
    {s : ℝ} (hs : 0 < s) (a : (X dim))
    (hMap : MapsTo (fun x : (X dim) => a+s • x) K B)
    {h : (X dim) → ℝ} (hh : Continuous h) :
    (∫ x in K, h (a+s • x)^2) ≤ ((s^dim)⁻¹) * (∫ x in B, h x^2) := by
  let f (x : (X dim)) := h x ^ 2
  let T := MeasurableEquiv.addLeft a
  let D : Set (X dim) := T '' (s • K)
  have hDK : T ⁻¹' D = s • K := preimage_image_eq _ T.injective
  have hDB : D ⊆ B := by
    rintro _ ⟨q,hq,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hq
    exact hMap hx
  have hTrans : (∫ x in s • K, f (a+x)) = ∫ x in D, f x := by
    have ht := (measurePreserving_add_left (volume : Measure (X dim)) a).setIntegral_preimage_emb
      T.measurableEmbedding f D
    change (∫ x in T ⁻¹' D, f (a+x)) = _ at ht
    rw [hDK] at ht
    exact ht
  have hdim : Module.finrank ℝ (X dim) = dim := by simp
  change (∫ x in K, (fun z => f (a+z)) (s • x)) ≤ _
  rw [Measure.setIntegral_comp_smul_of_pos volume (fun z => f (a+z)) K hs, hdim, hTrans, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_mono_set ((hh.pow 2).continuousOn.integrableOn_compact hB)
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hDB))
    (inv_nonneg.2 (pow_nonneg hs.le _))

set_option maxHeartbeats 1800000 in
/-- The boundary-inclusive estimate uses derivatives through order
`dim + 1`, so every Taylor remainder is integrable uniformly to the boundary. -/
theorem norm_le_unitBall_L2_jets
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : X dim → F} (hf : ContDiff ℝ ((dim + 1 : ℕ) : ℕ∞ω) f)
    {x : X dim} (hx : x ∈ closedBall (0 : X dim) 1) :
    ‖f x‖ ≤ (2 : ℝ)^(dim + 1) / Real.sqrt (volume.real (closedBall (0 : X dim) 1)) *
      (∑ k ∈ Finset.range (dim + 2),
        Real.sqrt (∫ y in closedBall (0 : X dim) 1, ‖iteratedFDeriv ℝ k f y‖^2)) := by
  let B := closedBall (0 : X dim) 1
  let J := Ioo (0 : ℝ) 1
  let Q (k : ℕ) (y : X dim) := ‖iteratedFDeriv ℝ k f y‖
  let L (k : ℕ) := Real.sqrt (∫ y in B, Q k y ^ 2)
  let C : ℝ := volume.real B
  let P : ℝ := 2^(dim+1)
  let A (y : X dim) (t : ℝ) := y+t • (x-y)
  let R (y : X dim) (t : ℝ) := (1-t)^dim * Q (dim+1) (A y t)
  have hB : IsCompact B := isCompact_closedBall _ _
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hB.measure_ne_top
  have hBm : MeasurableSet B := isClosed_closedBall.measurableSet
  have hC : 0 < C := ENNReal.toReal_pos
    (ne_of_gt (measure_closedBall_pos volume (0 : X dim) one_pos)) hB.measure_ne_top
  have hQ (k : ℕ) (hk : k ≤ dim+1) : Continuous (Q k) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hk)).norm
  have hA : Continuous (Function.uncurry A) := by
    dsimp only [Function.uncurry,A]
    fun_prop
  have hR : Continuous (Function.uncurry R) :=
    (continuous_const.sub continuous_snd).pow dim |>.mul ((hQ (dim+1) le_rfl).comp hA)
  have hRi : Integrable (Function.uncurry R) ((volume.restrict B).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact (hR.continuousOn.integrableOn_compact (hB.prod isCompact_Icc)).mono_set
      (prod_mono Subset.rfl Ioo_subset_Icc_self)
  have hWeight (k : ℕ) : ‖((k.factorial : ℝ)⁻¹)‖ ≤ 1 := by
    have hk : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [Real.norm_of_nonneg (inv_nonneg.2 (by positivity))]
    exact inv_le_one_of_one_le₀ hk
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hBound (y : X dim) (hy : y ∈ B) :
      ‖f x‖ ≤ P * ((∑ k ∈ Finset.range (dim+1), Q k y) + ∫ t in J, R y t) := by
    have hn : ‖x-y‖ ≤ 2 := by
      have hx' := mem_closedBall_zero_iff.mp hx
      have hy' := mem_closedBall_zero_iff.mp hy
      exact (norm_sub_le _ _).trans (by linarith)
    let T (k : ℕ) := ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f y (fun _ => x-y)
    let W (t : ℝ) := (1-t)^dim • iteratedFDeriv ℝ (dim+1) f (A y t) (fun _ => x-y)
    have hEq : f x = (∑ k ∈ Finset.range (dim+1), T k) +
        ((dim.factorial : ℝ)⁻¹) • ∫ t in J, W t := by
      have h := map_add_eq_sum_add_integral_iteratedFDeriv
        (n := dim) (x := y) (y := x-y) (fun _ _ => hf.contDiffAt)
      rw [intervalIntegral.integral_of_le zero_le_one,← restrict_Ioo_eq_restrict_Ioc] at h
      simpa only [J,A,T,W,add_sub_cancel,add_comm y x,add_sub_cancel_left] using h
    have hT (k : ℕ) (hk : k ∈ Finset.range (dim+1)) : ‖T k‖ ≤ P * Q k y := by
      have hnorm := (iteratedFDeriv ℝ k f y).le_opNorm (fun _ => x-y)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hnorm
      have hk' : k ≤ dim+1 := (Finset.mem_range.mp hk).le
      have hp : ‖x-y‖^k ≤ P := (pow_le_pow_left₀ (norm_nonneg _) hn _).trans
        (pow_le_pow_right₀ (by norm_num) hk')
      rw [norm_smul]
      calc
        _ ≤ 1 * (Q k y * ‖x-y‖ ^ k) :=
          mul_le_mul (hWeight k) hnorm (norm_nonneg _) zero_le_one
        _ ≤ _ := by
          rw [one_mul,mul_comm P]
          exact mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    have hD (t : ℝ) (ht : t ∈ J) : ‖W t‖ ≤ P * R y t := by
      have hnorm := (iteratedFDeriv ℝ (dim+1) f (A y t)).le_opNorm (fun _ => x-y)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hnorm
      have hts : 0 ≤ (1-t)^dim := pow_nonneg (sub_nonneg.mpr ht.2.le) _
      rw [norm_smul,Real.norm_of_nonneg hts]
      exact (mul_le_mul_of_nonneg_left
        (hnorm.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hn _) (norm_nonneg _))) hts).trans_eq (by
            simp only [P,R,Q]
            ring)
    have hWc : Continuous W := by
      have hDer : Continuous (fun t => iteratedFDeriv ℝ (dim+1) f (A y t)) :=
        (hf.continuous_iteratedFDeriv le_rfl).comp
          (hA.comp (continuous_const.prodMk continuous_id))
      exact ((continuous_const.sub continuous_id).pow dim).smul (hDer.eval continuous_const)
    have hWi : IntegrableOn W J :=
      (hWc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hIntR : IntegrableOn (R y) J :=
      (((hR.comp (continuous_const.prodMk continuous_id)).continuousOn).integrableOn_compact
        isCompact_Icc).mono_set Ioo_subset_Icc_self
    have hWb : ‖∫ t in J, W t‖ ≤ P * (∫ t in J, R y t) := by
      apply (norm_integral_le_integral_norm _).trans
      rw [← integral_const_mul]
      exact setIntegral_mono_on hWi.norm (hIntR.const_mul _) measurableSet_Ioo hD
    rw [hEq,mul_add]
    apply (norm_add_le _ _).trans
    refine add_le_add ?_ ?_
    · exact (norm_sum_le _ _).trans (by rw [Finset.mul_sum]; exact Finset.sum_le_sum hT)
    · rw [norm_smul]
      exact (mul_le_mul (hWeight dim) hWb (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hQI (k : ℕ) (hk : k ≤ dim+1) : IntegrableOn (Q k) B :=
    (hQ k hk).continuousOn.integrableOn_compact hB
  have hLow : IntegrableOn (fun y => ∑ k ∈ Finset.range (dim+1), Q k y) B :=
    integrable_finsetSum _ (fun k hk => hQI k (Finset.mem_range.mp hk).le)
  have hHigh : IntegrableOn (fun y => ∫ t in J, R y t) B := hRi.integral_prod_left
  have hAverage : C * ‖f x‖ ≤ P * ((∑ k ∈ Finset.range (dim+1), ∫ y in B, Q k y) +
      ∫ t in J, ∫ y in B, R y t) := by
    calc
      _ = ∫ y in B, ‖f x‖ := by rw [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]
      _ ≤ ∫ y in B, P * ((∑ k ∈ Finset.range (dim+1), Q k y) + ∫ t in J, R y t) :=
        setIntegral_mono_on (integrable_const _) ((hLow.add hHigh).const_mul _) hBm hBound
      _ = _ := by
        rw [integral_const_mul,integral_add hLow hHigh,integral_finsetSum _
          (fun k hk => hQI k (Finset.mem_range.mp hk).le),integral_integral_swap hRi]
  have hSlice (t : ℝ) (ht : t ∈ J) :
      (∫ y in B, R y t) ≤ Real.sqrt C * L (dim+1) := by
    let s := 1-t
    let d := s^dim
    have hs : 0 < s := sub_pos.mpr ht.2
    have hd : 0 < d := pow_pos hs _
    have hd₁ : d ≤ 1 := pow_le_one₀ hs.le (sub_le_self _ ht.1.le)
    have hForm (y : X dim) : A y t = t • x+s • y := by
      simp only [A,s,sub_smul,smul_sub,one_smul]
      abel
    have hmap : MapsTo (fun y => t • x+s • y) B B := by
      intro y hy
      change t • x+s • y ∈ B
      rw [← hForm]
      exact (convex_closedBall _ _).add_smul_sub_mem hy hx ⟨ht.1.le,ht.2.le⟩
    have hS := integral_sq_affine_le hB hs (t • x) hmap (hQ (dim+1) le_rfl)
    have hAff : Continuous (fun y : X dim => t • x+s • y) :=
      continuous_const.add (continuous_id.const_smul s)
    have hAv := integral_le_sqrt_volume_mul_sqrt_sq hB hC ((hQ (dim+1) le_rfl).comp hAff)
    simp only [R,integral_const_mul,hForm]
    change d * (∫ y in B, Q (dim+1) (t • x+s • y)) ≤ _
    have hMul : d * (∫ y in B, Q (dim+1) (t • x+s • y)) ≤
        d * (Real.sqrt C * Real.sqrt (d⁻¹ * (∫ y in B, Q (dim+1) y ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (hAv.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) (Real.sqrt_nonneg C))) hd.le
    refine hMul.trans ?_
    rw [Real.sqrt_mul (inv_nonneg.2 hd.le)]
    have hscale : d * √d⁻¹ ≤ 1 := by
      apply (sq_le_sq₀ (by positivity) zero_le_one).mp
      rw [mul_pow,Real.sq_sqrt (inv_nonneg.2 hd.le),pow_two,mul_assoc,mul_inv_cancel₀ hd.ne',mul_one]
      simpa using hd₁
    change d * (√C * (√d⁻¹ * L (dim+1))) ≤ _
    calc
      _ = (d * √d⁻¹) * (√C * L (dim+1)) := by ring
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hscale (by dsimp only [L]; positivity :
        0 ≤ Real.sqrt C * L (dim+1))
  have hRem : (∫ t in J, ∫ y in B, R y t) ≤ Real.sqrt C * L (dim+1) := by
    refine (setIntegral_mono_on hRi.swap.integral_prod_left (integrable_const _) measurableSet_Ioo hSlice).trans_eq ?_
    simp [J,integral_const,Real.volume_real_Ioo]
  have hSum : (∑ k ∈ Finset.range (dim+1), ∫ y in B, Q k y) ≤
      √C * (∑ k ∈ Finset.range (dim+1), L k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk =>
      integral_le_sqrt_volume_mul_sqrt_sq hB hC (hQ k (Finset.mem_range.mp hk).le)
  have hU : C * ‖f x‖ ≤ √C * (P * ∑ k ∈ Finset.range (dim+2), L k) := by
    refine hAverage.trans ((mul_le_mul_of_nonneg_left (add_le_add hSum hRem) hP).trans_eq ?_)
    have hsplit : (∑ k ∈ Finset.range (dim+2), L k) =
        (∑ k ∈ Finset.range (dim+1), L k) + L (dim+1) := Finset.sum_range_succ L (dim+1)
    rw [hsplit]
    ring
  have hCS : 0 < √C := Real.sqrt_pos.2 hC
  have hT : ‖f x‖ * √C ≤ P * ∑ k ∈ Finset.range (dim+2), L k := by
    apply (mul_le_mul_iff_right₀ hCS).mp
    calc
      √C * (‖f x‖ * √C) = C * ‖f x‖ := by
        rw [mul_left_comm,← pow_two,Real.sq_sqrt hC.le,mul_comm]
      _ ≤ _ := hU
  change ‖f x‖ ≤ P / √C * _
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hCS).mpr hT

end CalderonN
