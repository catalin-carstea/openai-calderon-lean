module

public import Proof.CalderonN.NormalCoordinates
public import Proof.CalderonN.SphereFrame

import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Adapted from `EndpointTaylor` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Interval

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Uniform Lipschitz control of the normal endpoint on compact families,
with the physical velocity as the small variable. -/
theorem exists_uniform_normal_endpoint_displacement_of_speed
    {Y : Set (X dim)} (hY : IsCompact Y) {A : Set ℝ} (hA : IsCompact A)
    {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {K R : ℝ} (hK : 0 ≤ K) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a ∈ A, ∀ y ∈ Y, ∀ r ∈ Icc (0 : ℝ) R, ∀ w : (X dim),
      ‖w‖ ≤ Real.sqrt K → E a (y,0) = y →
      ‖endpoint (E a) (fun _ => r) (y,w) - y‖ ≤ L * r := by
  let J (q : ℝ × ((X dim) × (X dim))) := fderiv ℝ (fun w => E q.1 (q.2.1,w)) q.2.2
  let setJ := A ×ˢ (Y ×ˢ closedBall (0 : (X dim)) (R * Real.sqrt K))
  have hd : ContDiff ℝ ∞ (fun q : (ℝ × (X dim)) × (X dim) => E q.1.1 (q.1.2,q.2)) :=
    hE.comp ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).prodMk contDiff_snd))
  have hJeq (q : ℝ × ((X dim) × (X dim))) :
      J q = (fderiv ℝ (fun z : (ℝ × (X dim)) × (X dim) => E z.1.1 (z.1.2,z.2)) ((q.1,q.2.1),q.2.2)).comp
        (ContinuousLinearMap.inr ℝ (ℝ × (X dim)) (X dim)) := by
    have h := ((hd.differentiable (by simp) ((q.1,q.2.1),q.2.2)).hasFDerivAt.comp q.2.2
      ((hasFDerivAt_const (q.1,q.2.1) q.2.2).prodMk (hasFDerivAt_id q.2.2))).fderiv
    exact h
  have hJ : Continuous J := by
    have heq : J = _ := funext hJeq
    rw [heq]
    let T := (ContinuousLinearMap.compL ℝ (X dim) ((ℝ × (X dim)) × (X dim)) (X dim)).flip
      (ContinuousLinearMap.inr ℝ (ℝ × (X dim)) (X dim))
    exact T.continuous.comp ((hd.fderiv_right (m := ∞) (by simp)).continuous.comp (by fun_prop))
  obtain ⟨M,hM⟩ := (hA.prod (hY.prod (isCompact_closedBall _ _))).exists_bound_of_continuousOn
    (hJ.continuousOn : ContinuousOn J setJ)
  let M' := max M 0
  refine ⟨M' * Real.sqrt K, by positivity, fun a ha y hy r hr w hn hzero => ?_⟩
  have hs : ‖r • w‖ ≤ r * Real.sqrt K := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact mul_le_mul_of_nonneg_left hn hr.1
  let B := closedBall (0 : (X dim)) (R * Real.sqrt K)
  have h0 : (0 : (X dim)) ∈ B := mem_closedBall_self (by positivity)
  have hvec : r • w ∈ B := mem_closedBall_zero_iff.mpr
    (hs.trans (mul_le_mul_of_nonneg_right hr.2 (Real.sqrt_nonneg _)))
  let f : (X dim) → (X dim) := fun v => E a (y,v)
  have hf : ContDiff ℝ ∞ f := hE.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hbound (v : (X dim)) (hv : v ∈ B) : ‖fderiv ℝ f v‖ ≤ M' :=
    (hM (a,y,v) ⟨ha,hy,hv⟩).trans (le_max_left _ _)
  have hL := (convex_closedBall (0 : (X dim)) (R * Real.sqrt K)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hf.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt) hbound h0 hvec
  change ‖f (r • w) - f 0‖ ≤ M' * ‖r • w - 0‖ at hL
  have hfy : f 0 = y := hzero
  rw [hfy,sub_zero] at hL
  exact hL.trans ((mul_le_mul_of_nonneg_left hs (le_max_right _ _)).trans_eq (by ring))

/-- Uniform Lipschitz control of the normal endpoint on compact families,
with the physical velocity as the small variable. -/
theorem exists_uniform_normal_endpoint_displacement
    {Y : Set (X dim)} (hY : IsCompact Y) {A : Set ℝ} (hA : IsCompact A)
    {E : ℝ → (X dim) × (X dim) → (X dim)}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (hzero : ∀ a ∈ A, ∀ y ∈ Y, E a (y,0) = y)
    {γ : ℝ → (MetricField dim)} {K R : ℝ} (hK : 0 < K) (hR : 0 ≤ R)
    (hell : ∀ a ∈ A, ∀ y ∈ Y, ∀ w : (X dim), K⁻¹ * ‖w‖^2 ≤ metricPair (γ a) y w w) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a ∈ A, ∀ y ∈ Y, ∀ r ∈ Icc (0 : ℝ) R, ∀ w ∈ sphereAt (γ a) y,
      ‖endpoint (E a) (fun _ => r) (y,w) - y‖ ≤ L * r := by
  obtain ⟨L,hL,hbound⟩ := exists_uniform_normal_endpoint_displacement_of_speed hY hA hE hK.le hR
  refine ⟨L,hL,fun a ha y hy r hr w hw => hbound a ha y hy r hr w ?_ (hzero a ha y hy)⟩
  have hww : metricPair (γ a) y w w = 1 := hw
  have hww' := hell a ha y hy w
  rw [hww,inv_mul_eq_div,div_le_iff₀ hK,one_mul] at hww'
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hww'

/-- The ordinary first-order Taylor remainder for an endpoint at distance
at most (Lr) has the required two powers of the same radius. -/
theorem abs_endpoint_affine_remainder_le
    (u : (X dim) → ℝ) (y z : (X dim)) (M L r : ℝ) (hM : 0 ≤ M)
    (_hLr : 0 ≤ L*r) (hDist : ‖z-y‖ ≤ L*r)
    (hSmooth : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 u (y+t • (z-y)))
    (hJet : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ 2 u (y+t • (z-y))‖ ≤ M) :
    |u z - (u y + fderiv ℝ u y (z-y))| ≤ (M*L^2)*r^2 := by
  let v := z-y
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := 1) (f := u) (x := y) (y := v) hSmooth
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, inv_one, one_smul, zero_add, iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply,
    pow_one] at hT
  have he : y+v = z := by dsimp only [v]; abel
  rw [he] at hT
  rw [hT, add_sub_cancel_left, ← Real.norm_eq_abs]
  have hpoint : ∀ t ∈ Ι (0 : ℝ) 1,
      ‖(1-t) • iteratedFDeriv ℝ 2 u (y+t • v) (fun _ => v)‖ ≤ M * ‖v‖^2 := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le,ht.2⟩
    have h1 : ‖(1-t : ℝ)‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
    have h2 := ((iteratedFDeriv ℝ 2 u (y+t • v)).le_opNorm (fun _ => v))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h2' := h2.trans (mul_le_mul_of_nonneg_right (hJet t ht') (sq_nonneg ‖v‖))
    rw [norm_smul]
    simpa only [one_mul] using mul_le_mul h1 h2' (norm_nonneg _) zero_le_one
  have hi : ‖∫ t in (0 : ℝ)..1, (1-t) • iteratedFDeriv ℝ 2 u (y+t • v) (fun _ => v)‖ ≤
      M * ‖v‖^2 := by simpa using intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  refine hi.trans ?_
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hDist 2) hM
  exact h.trans_eq (by ring)

end CalderonN
