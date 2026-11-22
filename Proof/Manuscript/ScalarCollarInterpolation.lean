module

public import Proof.Manuscript.ScalarProductGluing
public import Proof.Manuscript.ScalarLowerOrderCarleman

import Proof.CalderonN.WeightedCollars
import Proof.CalderonN.ExponentialBalancing
import Proof.CalderonN.CollarResidual
import Proof.CalderonN.CrossTensor
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory CalderonN LocalMetricExtension
open CalderonN.Elliptic (interpolation_of_weighted_sq weighted_sq_split weighted_two_collar_combine)
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

theorem contDiff_apply_univ {L : ScalarElliptic n} (hL : L.SmoothOn univ)
    {u : X n → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (L.apply u) := by
  have hA (i j : I n) : ContDiff ℝ ∞ (fun x => L.principalMatrix x i j) :=
    contDiffOn_univ.mp (contDiffOn_metric_inv_entry hL.1 i j)
  have hB (i : I n) : ContDiff ℝ ∞ (fun x => L.first x i) := contDiffOn_univ.mp (hL.2.1 i)
  have hZ : ContDiff ℝ ∞ L.zeroth := contDiffOn_univ.mp hL.2.2
  exact ((ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (hA i j).mul (Elliptic.contDiff_pd (i := i) (Elliptic.contDiff_pd (i := j) hu))).add
      (ContDiff.sum fun i _ => (hB i).mul (Elliptic.contDiff_pd (i := i) hu))).add (hZ.mul hu)

theorem apply_zero (L : ScalarElliptic n) (x : X n) : L.apply (fun _ => 0) x = 0 := by
  change (∑ i, ∑ j, L.principalMatrix x i j * Elliptic.pd i (Elliptic.pd j (fun _ => 0)) x) +
    (∑ i, L.first x i * Elliptic.pd i (fun _ => 0) x) + L.zeroth x * 0 = 0
  have he (i : I n) : Elliptic.pd i (fun _ => 0) = fun _ => 0 :=
    funext (Elliptic.pd_const 0)
  simp [he]

private theorem scalar_cutoff_residual_vanishes {L : ScalarElliptic n} {D B H : Set (X n)}
    {χ w : X n → ℝ} (hχD : tsupport χ ⊆ D) (hw : L.SolvesOn D w)
    (hχ : ∀ x ∉ B ∪ H, (χ =ᶠ[𝓝 x] fun _ => 0) ∨ χ =ᶠ[𝓝 x] fun _ => 1) :
    ∀ x ∉ B ∪ H, L.apply (fun y => χ y * w y) x = 0 := by
  intro x hx
  rcases hχ x hx with h | h
  · have hg : (fun y => χ y * w y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      h.mono (fun y hy => by change χ y * w y = 0; rw [hy,zero_mul])
    rw [apply_congr_of_eventuallyEq hg,apply_zero]
  · have hxD := hχD (subset_tsupport χ (show χ x ≠ 0 by rw [h.eq_of_nhds]; norm_num))
    have hg : (fun y => χ y * w y) =ᶠ[𝓝 x] w :=
      h.mono (fun y hy => by change χ y * w y = w y; rw [hy,one_mul])
    exact (apply_congr_of_eventuallyEq hg).trans (hw.2 x hxD)

theorem memLp_integral_sq_eq_lpNorm_sq {V : Set (X n)} {w : X n → ℝ}
    (hw : MemLp w 2 ((volume : Measure (X n)).restrict V)) :
    (∫ x in V, w x^2) = (lpNorm w 2 ((volume : Measure (X n)).restrict V))^2 := by
  let q := hw.toLp w
  have hnorm : ‖q‖ = lpNorm w 2 ((volume : Measure (X n)).restrict V) := Lp.norm_toLp _ _
  rw [← hnorm, ← integral_sq_eq_norm_sq q]
  exact integral_congr_ae ((MemLp.coeFn_toLp hw).symm.mono fun _ h => congrArg (fun y : ℝ => y^2) h)

set_option maxHeartbeats 2400000 in
/-- Two scalar collar residual bounds and full scalar Carleman combine
with the source's exact weight-gap exponent. -/
theorem interpolates_of_scalar_collars {L : ScalarElliptic n} (hLg : L.SmoothOn univ)
    {D S O B H K : Set (X n)} (hD : IsOpen D) (hO : MeasurableSet O)
    (hSD : S ⊆ D) (hOD : O ⊆ D) (hB : IsCompact B) (hH : IsCompact H)
    {χ ψ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχD : tsupport χ ⊆ D) (hχK : tsupport χ ⊆ K)
    (hχO : ∀ x ∈ O, χ x = 1)
    (htrans : ∀ x ∉ B ∪ H, (χ =ᶠ[𝓝 x] fun _ => 0) ∨ χ =ᶠ[𝓝 x] fun _ => 1)
    (hψ : Continuous ψ) {pB pO pH C M τ₀ : ℝ} (hBO : pB < pO) (hOH : pO < pH)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hτ₀ : 1 ≤ τ₀)
    (hψB : ∀ x ∈ B, ψ x ≤ pB) (hψH : ∀ x ∈ H, ψ x ≤ pH) (hψO : ∀ x ∈ O, pO ≤ ψ x)
    (hCar : ∀ τ : ℝ, τ₀ ≤ τ → ∀ w : X n → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ K →
        τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ ψ w) x ^ 2) +
          τ^3 * (∫ x, (weightedFunction τ ψ w x)^2) ≤
          C * ∫ x, (weightedFunction τ ψ (fun y => chartVolume L.metric y * L.apply w y) x)^2)
    (hRestB : ∀ w, L.SolvesOn D w → MemLp w 2 ((volume : Measure (X n)).restrict D) →
      (∫ x in B, (chartVolume L.metric x * L.apply (fun y => χ y*w y) x)^2) ≤ M * ∫ x in D, w x^2)
    (hRestH : ∀ w, L.SolvesOn D w → MemLp w 2 ((volume : Measure (X n)).restrict S) →
      (∫ x in H, (chartVolume L.metric x * L.apply (fun y => χ y*w y) x)^2) ≤ M * ∫ x in S, w x^2) :
    L.Interpolates D S O
      (2*Real.sqrt (C*M) + Real.exp ((pO-pB)*max τ₀ 1)) ((pO-pB)/(pH-pB)) := by
  intro w hw hMem
  have hMemS := hMem.mono_measure (Measure.restrict_mono_set volume hSD)
  have hMemO := hMem.mono_measure (Measure.restrict_mono_set volume hOD)
  have hwO := hMemO.integrable_sq
  have hO_le : lpNorm w 2 ((volume : Measure (X n)).restrict O) ≤ lpNorm w 2 ((volume : Measure (X n)).restrict D) := by
    apply (sq_le_sq₀ (lpNorm_nonneg ..) (lpNorm_nonneg ..)).mp
    rw [← memLp_integral_sq_eq_lpNorm_sq hMemO, ← memLp_integral_sq_eq_lpNorm_sq hMem]
    exact setIntegral_mono_set hMem.integrable_sq (ae_of_all _ fun _ => sq_nonneg _) hOD.eventuallyLE
  let u (x : X n) := χ x * w x
  let R (x : X n) := chartVolume L.metric x * L.apply u x
  have hu : ContDiff ℝ ∞ u := Elliptic.contDiff_mul_of_tsupport_subset hD hχ hχD hw.1
  have huc : HasCompactSupport u := hχc.mul_right
  have huK : tsupport u ⊆ K := tsupport_mul_subset_left.trans hχK
  have hR0 : ∀ x ∉ B ∪ H, R x = 0 := by
    intro x hx
    simp [R,u,scalar_cutoff_residual_vanishes hχD hw htrans x hx]
  have hRcont : Continuous R :=
    (contDiffOn_univ.mp (contDiffOn_metric_volume hLg.1)).continuous.mul (contDiff_apply_univ hLg hu).continuous
  have hRi : Integrable (fun x => R x ^ 2) :=
    (hRcont.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (hB.union hH) (fun x hx => by change R x ^ 2 = 0; rw [hR0 x hx,zero_pow (by decide)]))
  rw [mul_assoc]
  apply interpolation_of_weighted_sq hBO hOH (mul_nonneg hC hM)
    (lpNorm_nonneg ..) (lpNorm_nonneg ..) hO_le
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
  have hc := hCar τ hτ u hu huc huK
  have hExp (x : X n) : (weightedFunction τ ψ R x)^2 = Real.exp (2 * (τ*ψ x)) * R x^2 := by
    unfold weightedFunction
    rw [mul_pow,pow_two (Real.exp _),← Real.exp_add,two_mul]
  change τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ ψ u) x ^ 2) +
    τ^3 * (∫ x, (weightedFunction τ ψ u x)^2) ≤ C * ∫ x, (weightedFunction τ ψ R x)^2 at hc
  rw [show (fun x => (weightedFunction τ ψ R x)^2) = _ from funext hExp] at hc
  simp only [weightedFunction] at hc
  have hGrad : 0 ≤ ∫ x : X n, ∑ i, coordDeriv i (fun y => Real.exp (τ * ψ y) * u y) x ^ 2 :=
    integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsplit := weighted_sq_split hτ' hC hGrad
    hc hu_int hRi hB.measurableSet hH.measurableSet hO (fun x hx => hR0 x hx) hψB hψH hψO
    (fun x hx => by simp [u,hχO x hx]) hwO
  have hcomb := weighted_two_collar_combine hC (Real.exp_pos (2*(τ*pB))).le
    (Real.exp_pos (2*(τ*pH))).le (hRestB w hw hMem) (hRestH w hw hMemS)
  simpa only [memLp_integral_sq_eq_lpNorm_sq hMem,memLp_integral_sq_eq_lpNorm_sq hMemS,
    memLp_integral_sq_eq_lpNorm_sq hMemO] using hsplit.trans hcomb

end CalderonPaper.ScalarElliptic
