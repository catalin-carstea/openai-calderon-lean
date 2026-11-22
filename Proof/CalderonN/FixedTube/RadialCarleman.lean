module

public import Proof.CalderonN.FixedTube.RadialWeight
public import Proof.CalderonN.FixedTube.DilatedGeometry

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.StrictParametricPoint
import Proof.CalderonN.JointCoefficientSmoothness

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim]

/-- The radial phase extends smoothly after cutting it off away from its
center. It retains the whole germ at every point of the separated compact set. -/
theorem exists_global_radialWeight_of_compact {K : Set (X dim)} (hK : IsCompact K) (c : (X dim))
    (hc : c ∉ K) :
    ∃ φ : (X dim) → ℝ, ContDiff ℝ ∞ φ ∧ ∀ x ∈ K, φ =ᶠ[𝓝 x] radialWeight c := by
  let U : Set (X dim) := {c}ᶜ
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hKU : K ⊆ U := fun x hx => by
    intro h
    exact hc ((mem_singleton_iff.mp h) ▸ hx)
  have hrad : ContDiffOn ℝ ∞ (radialWeight c) U := by
    intro x hx
    exact (contDiffAt_radialWeight (fun h => hx (mem_singleton_iff.mpr h))).contDiffWithinAt
  obtain ⟨χ,hχ,_,hχU,hχK⟩ := Elliptic.exists_plateau_cutoff hU hK hKU
  refine ⟨fun x => χ x * radialWeight c x,
    Elliptic.contDiff_mul_of_tsupport_subset hU hχ hχU hrad,?_⟩
  intro x hx
  filter_upwards [hχK x hx] with y hy
  rw [hy,one_mul]

private theorem strictMetricWeightAt_congr {g : (MetricField dim)} {f h : (X dim) → ℝ} {x : (X dim)}
    (he : f =ᶠ[𝓝 x] h) (hf : StrictMetricWeightAt g f x) :
    StrictMetricWeightAt g h x := by
  have hFirst (i : (I dim)) : coordDeriv i f =ᶠ[𝓝 x] coordDeriv i h :=
    (he.fderiv (𝕜 := ℝ)).mono fun z hz => congrArg (fun L : (X dim) →L[ℝ] ℝ => L (axis i)) hz
  have hd (i : (I dim)) : coordDeriv i f x = coordDeriv i h x := (hFirst i).eq_of_nhds
  have hh (i j : (I dim)) : coordDeriv i (coordDeriv j f) x = coordDeriv i (coordDeriv j h) x :=
    congrArg (fun L : (X dim) →L[ℝ] ℝ => L (axis i)) ((hFirst j).fderiv_eq (𝕜 := ℝ))
  have hg : chartMetricGradient g f x = chartMetricGradient g h x := by
    simp only [chartMetricGradient,hd]
  have hn : covectorSq g f x = covectorSq g h x := by simp only [covectorSq,hd]
  have hH (v w : (X dim)) : metricHessianEval g f x v w = metricHessianEval g h x v w := by
    simp only [metricHessianEval,metricHessian,hessian,hd,hh]
  simpa only [StrictMetricWeightAt,hg,hn,hH,hd] using hf

/-- Local Carleman at a point of a separated radial collar, using the
manuscript's inverse-distance phase and the actual dilated chart operator. -/
theorem exists_local_radialCarleman
    {g : (MetricField dim)} (hg : SmoothMetric univ g) (hg₀ : g 0 = 1)
    {c x : (X dim)} (hx : x ≠ c) :
    ∃ r C τ₀ : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ₀ ∧
      ∀ lam ∈ closedBall (0 : ℝ) r, ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ w : (X dim) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall x r →
        τ * (∫ y, ∑ i, coordDeriv i (fun z => Real.exp (τ * radialWeight c z) * w z) y ^ 2) +
        τ^3 * (∫ y, (Real.exp (τ * radialWeight c y) * w y)^2) ≤
          C * ∫ y, Real.exp (2*(τ * radialWeight c y)) *
            (chartVolume (dilatedMetric g lam) y * laplace (dilatedMetric g lam) w y)^2 := by
  let d := dist x c / 2
  have hd : 0 < d := half_pos (dist_pos.mpr hx)
  have hxc : c ∉ closedBall x d := by
    rw [mem_closedBall,dist_comm c x]
    exact not_le_of_gt (half_lt_self (dist_pos.mpr hx))
  obtain ⟨φ,hφ,hφrad⟩ := exists_global_radialWeight_of_compact (isCompact_closedBall x d) c hxc
  have hφjoint : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => φ q.2) := hφ.comp contDiff_snd
  have he : dilatedMetric g 0 = fun _ => (1 : (Mat dim)) := by funext y; simp [dilatedMetric,hg₀]
  have hs : StrictMetricWeightAt (dilatedMetric g 0) φ x := by
    rw [he]
    exact strictMetricWeightAt_congr (hφrad x (mem_closedBall_self hd.le)).symm (radialWeight_strict_identity hx)
  obtain ⟨r,C,τ₀,hr,hC,hτ₀,hest⟩ := exists_local_metricCarleman
    (g := dilatedMetric g) (φ := fun _ : ℝ => φ)
    (contDiff_dilatedMetric_entry hg) (fun lam y => hg.2 (lam • y) (mem_univ _)) hφjoint 0 x hs
  let R := min r d
  refine ⟨R,C,τ₀,lt_min hr hd,hC,hτ₀,?_⟩
  intro lam hlam τ hτ w hw hwc hsupport
  have hsupport' : tsupport w ⊆ closedBall x d :=
    hsupport.trans (closedBall_subset_closedBall (min_le_right _ _))
  have happ := hest lam (closedBall_subset_closedBall (min_le_left _ _) hlam) τ hτ w hw hwc
    (hsupport.trans (closedBall_subset_closedBall (min_le_left _ _)))
  have hprod : (fun y => Real.exp (τ * φ y) * w y) =
      fun y => Real.exp (τ * radialWeight c y) * w y := by
    funext y
    by_cases hy : y ∈ tsupport w
    · rw [(hφrad y (hsupport' hy)).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hy,mul_zero,mul_zero]
  have hprod' (y : (X dim)) : Real.exp (τ * φ y) * w y =
      Real.exp (τ * radialWeight c y) * w y := congrFun hprod y
  rw [hprod] at happ
  simp only [hprod'] at happ
  convert happ using 1
  apply congrArg (fun z : ℝ => C*z)
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ tsupport w
  · rw [(hφrad y (hsupport' hy)).eq_of_nhds]
  · have hw₀ : w =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy
    have hFirst (i : (I dim)) : coordDeriv i w =ᶠ[𝓝 y] 0 := by
      filter_upwards [hw₀.fderiv (𝕜 := ℝ)] with p hp
      simp [coordDeriv,hp]
    have h₁ (i : (I dim)) : coordDeriv i w y = 0 := (hFirst i).eq_of_nhds
    have h₂ (i j : (I dim)) : coordDeriv i (coordDeriv j w) y = 0 := by
      simp [coordDeriv,(hFirst j).fderiv_eq (𝕜 := ℝ)]
    simp only [laplace,h₁,h₂,mul_zero,Finset.sum_const_zero,sub_zero,zero_pow two_ne_zero]


open Carleman Carleman.Strict in
set_option maxHeartbeats 600000 in
/-- A thin radial collar admits one unchanged inverse-distance weight
and constants uniform near the Euclidean metric parameter. -/
theorem exists_compact_radialCarleman
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (g : P → (MetricField dim)) (p₀ : P) (hg : ∀ p, SmoothMetric univ (g p))
    (hbg : ∀ i j : (I dim), ContDiff ℝ ∞ (fun z : P × (X dim) => divergenceCoeff (g z.1) z.2 i j))
    (hg₀ : g p₀ = fun _ => (1 : (Mat dim))) (c : (X dim)) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁₂ : r₁ ≤ r₂) (hthin : r₂^3 < 2*r₁^3)
    {K : Set (X dim)} (hK : IsCompact K)
    (hin : ∀ x ∈ K, r₁ ≤ ‖x-c‖) (hout : ∀ x ∈ K, ‖x-c‖ ≤ r₂) :
    ∃ R C τ₀ : ℝ, 0 < R ∧ 0 < C ∧ 1 ≤ τ₀ ∧
      ∃ φ : (X dim) → ℝ, ContDiff ℝ ∞ φ ∧ (∀ x ∈ K, φ =ᶠ[𝓝 x] radialWeight c) ∧
      ∀ p ∈ closedBall p₀ R, ∀ τ : ℝ, τ₀ ≤ τ →
      ∀ w : (X dim) → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ K →
        τ * (∫ x, ∑ i, coordDeriv i (fun y => Real.exp (τ * φ y) * w y) x ^ 2) +
        τ^3 * (∫ x, (Real.exp (τ * φ x) * w x)^2) ≤
          C * ∫ x, Real.exp (2*(τ * φ x)) *
            (chartVolume (g p) x * laplace (g p) w x)^2 := by
  have hc : c ∉ K := by
    intro h
    exact h₁.not_ge (by simpa using hin c h)
  obtain ⟨φ,hφ,hφrad⟩ := exists_global_radialWeight_of_compact hK c hc
  have h₂ := h₁.trans_le h₁₂
  have hgap : (r₁^3)⁻¹ < 2*(r₂^3)⁻¹ := by
    rw [← one_div, ← one_div, ← div_eq_mul_one_div, div_lt_div_iff₀ (pow_pos h₁ _) (pow_pos h₂ _)]
    simpa only [one_mul] using hthin
  obtain ⟨m,hm₁,hm₂⟩ := exists_between hgap
  let a (p : P) (i j : (I dim)) (x : (X dim)) := divergenceCoeff (g p) x i j
  have ha (i j : (I dim)) : Elliptic.Strict.JointSmooth (fun p => a p i j) := hbg i j
  have hsym (p : P) (i j : (I dim)) : a p i j = a p j i :=
    funext fun x => divergenceCoeff_symm (hg p) (mem_univ x) i j
  have ha₀ : a p₀ = fun i j _ => (1 : (Mat dim)) i j := by
    funext i j x
    simp [a,divergenceCoeff,chartVolume,hg₀]
  have hstrict (x : (X dim)) (hx : x ∈ K) :=
    radialWeight_signed_criterion (c := c) (x := x) (m := m) (fun h => hc (h ▸ hx))
      hφ (hφrad x hx)
      ((inv_anti₀ (pow_pos h₁ 3) (pow_le_pow_left₀ h₁.le (hin x hx) 3)).trans_lt hm₁)
      (hm₂.trans_le (mul_le_mul_of_nonneg_left
        (inv_anti₀ (pow_pos (h₁.trans_le (hin x hx)) 3)
          (pow_le_pow_left₀ (norm_nonneg _) (hout x hx) 3)) (by norm_num)))
  obtain ⟨R,C,τ₀,hR,hC,hτ,hEst⟩ := exists_parameter_strict_weight_carleman_on_compact
    a (fun _ => φ) ha (hφ.comp contDiff_snd) hsym p₀ hK m
    (by rw [ha₀]; exact fun x hx => (hstrict x hx).1)
    (by rw [ha₀]; exact fun x hx => (hstrict x hx).2)
  refine ⟨R,C,τ₀,hR,hC,hτ,φ,hφ,hφrad,fun p hp τ ht w hw hwc hsupp => ?_⟩
  have he (x : (X dim)) : Lop (a p) w x =
      chartVolume (g p) x * laplace (g p) w x :=
    (chartVolume_mul_laplace_eq_divergence isOpen_univ
      (hg p) hw.contDiffOn (mem_univ x)).symm
  simpa only [he,pd,coordDeriv,axis] using hEst p hp τ ht w hw hwc hsupp

end CalderonN.FixedTube
