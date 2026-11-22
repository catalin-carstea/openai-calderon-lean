module

public import Proof.CalderonN.SmoothBoundarySobolev
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Multiplication

import Mathlib.Tactic

/-! Half-order multiplication comes from the actual bulk product and sharp
trace. Negative half-order multiplication is its dual on the same sphere. -/

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Gradient InnerProductSpace Classical DirectSum Topology
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti OAI.AnisotropicCalderon SphereHarmonic

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothDataMul (m u : SmoothData dim) : SmoothData dim := ⟨m.1*u.1,m.2.mul u.2⟩

omit [Nontrivial (Fin dim)] in
private theorem smoothSobolev_mul_eq_contDiffSMulL (m u : SmoothData dim) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |m.1 x| ≤ C)
    (hG : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient m.1 x‖ ≤ C) :
    smoothSobolev (smoothDataMul m u) =
      (W1p.contDiffSMulL (mu := (volume : Measure (X dim))) (Omega := fixedBallOpens dim)
        (p := 2) m.1 m.2 hC hM hG) (smoothSobolev u) := by
  rw [W1p.contDiffSMulL_apply]
  apply W1p.ext_value
  apply Lp.ext
  filter_upwards [W1p.value_contDiffSMul_ae m.2 hC hM hG (smoothSobolev u),
    value_smoothSobolev_ae u,value_smoothSobolev_ae (smoothDataMul m u)] with x hmul hu hx
  rw [hmul,hu,hx]
  rfl

private theorem norm_smoothBoundarySobolev_mul_half_finite_le (hn : 3 ≤ dim)
    (m : SmoothData dim) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |m.1 x| ≤ C)
    (hG : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient m.1 x‖ ≤ C)
    (g : HarmonicFiniteCoefficients dim) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothDataMul m (harmonicFiniteSmooth g))‖ ≤
      (2*Real.sqrt ((dim : ℝ)+3))*C*‖harmonicBoundaryFiniteL (1/2 : ℝ) g‖ := by
  let L := harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)
  let u := harmonicFiniteSmooth g
  let S := W1p.contDiffSMulL (mu := (volume : Measure (X dim))) (Omega := fixedBallOpens dim)
    (p := 2) m.1 m.2 hC hM hG
  have hNormS : ‖S‖ ≤ 2*C := W1p.norm_contDiffSMulL_le m.2 hC hM hG
  have hNorm : ‖smoothSobolev (smoothDataMul m u)‖ ≤ (2*C)*Real.sqrt (unitSphereArea dim)*‖L g‖ := by
    rw [smoothSobolev_mul_eq_contDiffSMulL m u hC hM hG,← harmonicFirstOrderLift_finite_smooth g]
    exact (S.le_opNorm _).trans ((mul_le_mul hNormS (norm_harmonicFirstOrderLift_le (L g))
      (norm_nonneg _) (by positivity)).trans_eq (by ring))
  have h := sq_smoothBoundarySobolev_half_le hn (smoothDataMul m u)
  have hAr := unitSphereArea_pos (dim := dim)
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hNorm 2
  have hB : (unitSphereArea dim)*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothDataMul m u)‖^2 ≤
      (unitSphereArea dim)*((2*Real.sqrt ((dim : ℝ)+3))*C*‖L g‖)^2 := by
    refine h.trans ((mul_le_mul_of_nonneg_left hSq (by positivity)).trans_eq ?_)
    simp only [mul_pow,Real.sq_sqrt hAr.le,Real.sq_sqrt (by positivity : 0 ≤ (dim : ℝ)+3)]
    ring
  have hS := (mul_le_mul_iff_of_pos_left hAr).mp hB
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hS

omit [Nontrivial (Fin dim)] in
private theorem harmonicBoundaryFiniteL_lof (s : ℝ) (k : ℕ) (a : harmonicSphereSubspace dim k) :
    harmonicBoundaryFiniteL s
      (DirectSum.lof ℝ ℕ (fun j => ↥(harmonicSphereSubspace dim j)) k a) = sphereSobolevSingleL s k a := by
  unfold harmonicBoundaryFiniteL
  exact DirectSum.toModule_lof (R := ℝ) (φ := fun j => (sphereSobolevSingleL s j).toLinearMap) k a

private def finiteBoundaryTruncation (u : SphereL2 dim) (n : ℕ) : HarmonicFiniteCoefficients dim :=
  ∑ k ∈ Finset.range n, DirectSum.lof ℝ ℕ (fun j => ↥(harmonicSphereSubspace dim j)) k (harmonicProjection k u)

private theorem harmonicBoundaryFiniteL_truncation (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (u : SmoothData dim) (n : ℕ) :
    harmonicBoundaryFiniteL s (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n) =
      sphereSobolevPartialSum s n (smoothBoundarySobolev hn s hs u) := by
  unfold finiteBoundaryTruncation sphereSobolevPartialSum
  simp only [map_sum,harmonicBoundaryFiniteL_lof]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  have h := sphereSobolevCoefficientL_reconstruct s k (smoothBoundarySobolev hn s hs u)
  rw [smoothBoundarySobolev_apply] at h
  exact (smul_right_injective (harmonicSphereSubspace dim k) (besselWeight_pos s k).ne' h).symm

omit [Nontrivial (Fin dim)] in
private theorem norm_sphereSobolevPartialSum_le (s : ℝ) (n : ℕ) (u : SphereSobolev dim s) :
    ‖sphereSobolevPartialSum s n u‖ ≤ ‖u‖ := by
  rw [sphereSobolevPartialSum_eq]
  have h := lp.norm_sum_single (E := fun k : ℕ => harmonicSphereSubspace dim k)
    (p := 2) (show 0 < (2 : ℝ≥0∞).toReal by norm_num) (fun k => u k) (Finset.range n)
  have h' := lp.sum_rpow_le_norm_rpow (show 0 < (2 : ℝ≥0∞).toReal by norm_num) u (Finset.range n)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at h h'
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h.trans_le h')

omit [Nontrivial (Fin dim)] in
private theorem smoothBoundarySobolev_zero (hn : 3 ≤ dim) (u : SmoothData dim) :
    smoothBoundarySobolev hn 0 (by norm_num) u = sphereHarmonicDecomposition (smoothSphereLift u.1 u.2) := by
  apply lp.ext
  funext k
  rw [smoothBoundarySobolev_apply,sphereHarmonicDecomposition_apply]
  simp only [besselWeight,Real.rpow_zero,one_smul]

private theorem tendsto_smoothSphereLift_finiteBoundaryTruncation (hn : 3 ≤ dim) (u : SmoothData dim) :
    Tendsto (fun n : ℕ => smoothSphereLift
      (harmonicFiniteSmooth (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n)).1
      (harmonicFiniteSmooth (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n)).2)
      atTop (𝓝 (smoothSphereLift u.1 u.2)) := by
  have h := tendsto_sphereSobolevPartialSum 0 (smoothBoundarySobolev hn 0 (by norm_num) u)
  have he : (fun n : ℕ => sphereSobolevPartialSum 0 n (smoothBoundarySobolev hn 0 (by norm_num) u)) =
      fun n : ℕ => smoothBoundarySobolev hn 0 (by norm_num)
        (harmonicFiniteSmooth (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n)) := by
    funext n
    rw [smoothBoundarySobolev_harmonicFiniteSmooth hn 0 (by norm_num),harmonicBoundaryFiniteL_truncation hn]
  rw [he] at h
  simp only [smoothBoundarySobolev_zero hn] at h
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using
    (sphereHarmonicDecomposition.symm.continuous.tendsto _).comp h

omit [Nontrivial (Fin dim)] in
private theorem smoothBoundarySobolev_congr_order (hn : 3 ≤ dim) {s t : ℝ}
    (h : s = t) (hs : s ≤ 2) (ht : t ≤ 2) (u : SmoothData dim) :
    smoothBoundarySobolev hn s hs u = (smoothBoundarySobolev hn t ht u : SphereSobolev dim s) := by
  subst t
  rfl

/-- Multiplication by a smooth coefficient with uniformly controlled first
bulk jet acts boundedly on the actual half-order trace. -/
theorem norm_smoothBoundarySobolev_mul_half_le (hn : 3 ≤ dim)
    (m u : SmoothData dim) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |m.1 x| ≤ C)
    (hG : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient m.1 x‖ ≤ C) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (smoothDataMul m u)‖ ≤
      (2*Real.sqrt ((dim : ℝ)+3))*C*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖ := by
  let h : ℝ := 2*Real.sqrt ((dim : ℝ)+3)*C
  let U := smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u
  have h₀ : 0 ≤ h := by dsimp only [h]; positivity
  have hNorm := norm_smoothBoundarySobolev_le_of_finite_tests hn (-(1/2 : ℝ))
    (by norm_num) (by norm_num) (smoothDataMul m u) (h*‖U‖) (by positivity)
  rw [smoothBoundarySobolev_congr_order hn (neg_neg _) _ (by norm_num)] at hNorm
  apply hNorm
  intro g
  let v := harmonicFiniteSmooth g
  let uN (n : ℕ) := harmonicFiniteSmooth (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n)
  have hPair (w : SmoothData dim) :
      (∫ x : ↥(standardSphere dim), (smoothDataMul m w).1 x*v.1 x ∂(sphereProbability dim)) =
        ⟪smoothSphereLift (smoothDataMul m v).1 (smoothDataMul m v).2,
          smoothSphereLift w.1 w.2⟫_ℝ := by
    rw [smoothSphereLift_inner]
    apply integral_congr_ae
    filter_upwards with x
    change m.1 x*w.1 x*v.1 x = m.1 x*v.1 x*w.1 x
    ring
  have hLim := tendsto_smoothSphereLift_finiteBoundaryTruncation hn u
  have hCont := (innerSL ℝ (smoothSphereLift (smoothDataMul m v).1 (smoothDataMul m v).2)).continuous.abs
  have hLim' := (hCont.tendsto _).comp hLim
  simp only [Function.comp_def,innerSL_apply_apply] at hLim'
  rw [hPair u]
  apply le_of_tendsto_of_tendsto' hLim' tendsto_const_nhds
  intro n
  rw [← hPair (uN n)]
  have hh := abs_integral_mul_le_smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) (by norm_num)
    (smoothDataMul m (uN n)) v
  rw [smoothBoundarySobolev_congr_order hn (neg_neg _) _ (by norm_num)] at hh
  have hM' := norm_smoothBoundarySobolev_mul_half_finite_le hn m hC hM hG
    (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n)
  have hN : ‖harmonicBoundaryFiniteL (1/2 : ℝ) (finiteBoundaryTruncation (smoothSphereLift u.1 u.2) n)‖ ≤ ‖U‖ := by
    rw [harmonicBoundaryFiniteL_truncation hn (1/2 : ℝ) (by norm_num)]
    exact norm_sphereSobolevPartialSum_le _ _ _
  have hv := smoothBoundarySobolev_harmonicFiniteSmooth hn (-(1/2 : ℝ)) (by norm_num) g
  rw [hv] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hM'.trans (mul_le_mul_of_nonneg_left hN h₀)) (norm_nonneg _))

/-- The same scalar multiplication bound at the negative endpoint follows
from the exact half-order dual pairing. -/
theorem norm_smoothBoundarySobolev_mul_negHalf_le (hn : 3 ≤ dim)
    (m u : SmoothData dim) {C : ℝ} (hC : 0 ≤ C)
    (hM : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), |m.1 x| ≤ C)
    (hG : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ‖gradient m.1 x‖ ≤ C) :
    ‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) (smoothDataMul m u)‖ ≤
      (2*Real.sqrt ((dim : ℝ)+3))*C*‖smoothBoundarySobolev hn (-(1/2 : ℝ)) (by norm_num) u‖ := by
  apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2 : ℝ) (by norm_num) (by norm_num)
    _ _ (by positivity)
  intro g
  let v := harmonicFiniteSmooth g
  have hI : (∫ x : ↥(standardSphere dim), (smoothDataMul m u).1 x*v.1 x ∂(sphereProbability dim)) =
      ∫ x : ↥(standardSphere dim), u.1 x*(smoothDataMul m v).1 x ∂(sphereProbability dim) := by
    apply integral_congr_ae
    filter_upwards with x
    change m.1 x*u.1 x*v.1 x = u.1 x*(m.1 x*v.1 x)
    ring
  rw [hI]
  have h := abs_integral_mul_le_smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (by norm_num)
    u (smoothDataMul m v)
  refine h.trans ((mul_le_mul_of_nonneg_left
    (norm_smoothBoundarySobolev_mul_half_finite_le hn m hC hM hG g) (norm_nonneg _)).trans_eq ?_)
  ring

end CalderonN
