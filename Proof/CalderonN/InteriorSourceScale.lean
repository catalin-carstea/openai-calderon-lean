module

public import Proof.CalderonN.GreenSourceCutoff
public import Proof.CalderonN.FixedBallSourceEnergy
public import Proof.CalderonN.InteriorPointwise
public import Proof.CalderonN.EuclideanVolume
public import Proof.CalderonN.AffineChart

import Mathlib.Tactic

public section

/-! A source-free ball around the evaluation point admits the same
interior estimate after every positive rescaling. The coefficient family
includes the limiting constant coefficients at scale zero. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonN
open Elliptic TauCeti.PDE
variable {n : ℕ}

private theorem coordDeriv_comp_affine {f : X n → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : X n) (s : ℝ) (x : X n) (i : I n) :
    coordDeriv i (f ∘ affineChartMap c s) x = s * coordDeriv i f (affineChartMap c s x) := by
  let L := s • ContinuousLinearMap.id ℝ (X n)
  have hL : HasFDerivAt (affineChartMap c s) L x := by
    exact L.hasFDerivAt.const_add c
  have h := (HasFDerivAt.comp (G := ℝ) x
    ((hf.differentiable (by simp) _).hasFDerivAt) hL).fderiv
  simp only [coordDeriv, h, ContinuousLinearMap.comp_apply, L, _root_.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem Lop_affine_of_smooth {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    {b : X n → ℝ} (hb : ContDiff ℝ ∞ b) (c : X n) (s : ℝ) (x : X n) :
    Lop (fun i j z => a (affineChartMap c s z) i j) (b ∘ affineChartMap c s) x =
      s^2 * Lop (fun i j z => a z i j) b (affineChartMap c s x) := by
  let f (i : I n) (z : X n) := ∑ j, a z i j * coordDeriv j b z
  have hF (i : I n) : ContDiff ℝ ∞ (f i) := by
    refine ContDiff.sum fun j _ => ?_
    exact ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp ha).mul
      (contDiff_pd hb)
  have hFlux (i : I n) : (fun z => ∑ j : I n, a (affineChartMap c s z) i j *
      coordDeriv j (b ∘ affineChartMap c s) z) = fun z => s * (f i ∘ affineChartMap c s) z := by
    funext z
    simp only [coordDeriv_comp_affine hb c s, Function.comp_apply, f, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold Lop
  simp only [pd, hFlux, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    _ = s * coordDeriv i (f i ∘ affineChartMap c s) x :=
      pd_const_mul (i := i) s ((hF i).comp (contDiff_affineChartMap c s)) x
    _ = s^2 * coordDeriv i (f i) (affineChartMap c s x) := by
      rw [coordDeriv_comp_affine (hF i)]
      ring

private theorem posDef_of_uniform_of_symmetric
    {a : X n → Mat n} {lo hi : ℝ} {U : Set (X n)} (he : UniformlyEllipticOn U a lo hi)
    (hs : ∀ i j x, a x i j = a x j i) {x : X n} (hx : x ∈ U) : (a x).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun ξ hξ => ?_⟩
  · ext i j
    simpa using hs j i x
  · let v : X n := WithLp.toLp 2 ξ
    have hv : v ≠ 0 := fun hz => hξ (by
      have h' := congrArg (@WithLp.ofLp 2 (I n → ℝ)) hz
      simpa [v] using h')
    have hq := (he.2.2 hx).1 v
    simp only [Matrix.toQuadraticForm'_apply, v, WithLp.ofLp_toLp, star_trivial] at hq ⊢
    exact (mul_pos he.1 (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le hq

set_option maxHeartbeats 3500000 in
theorem exists_rescaled_source_point_bound [NeZero n]
    {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) (hs : ∀ i j x, a x i j = a x j i)
    {lo hi : ℝ} (he : UniformlyEllipticOn (fixedBallOpens n : Set (X n)) a lo hi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ closedBall (0 : X n) (1/4), ∀ r ∈ Ioc (0 : ℝ) (1/4),
      ∀ b : X n → ℝ, ContDiff ℝ ∞ b → (∀ x ∈ ball y r, negativeBallDivergence a b x = 0) →
        |b y| ≤ C * r ^ (-(n : ℝ)/2) * Real.sqrt (∫ x in ball y r, b x^2) := by
  let J := closedBall (0 : X n) (1/4) ×ˢ Icc (0 : ℝ) (1/4)
  let U := ball (0 : X n) 1
  let A (p : X n × ℝ) (i j : I n) (x : X n) := a (affineChartMap p.1 p.2 x) i j
  have hA (i j : I n) : Strict.JointSmooth (fun p => A p i j) := by
    exact ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp ha).comp
      (contDiff_fst.fst.add (contDiff_fst.snd.smul contDiff_snd))
  have hpos (p : X n × ℝ) (hp : p ∈ J) (x : X n) (hx : x ∈ U) :
      Matrix.PosDef (fun i j => A p i j x : Mat n) := by
    have hy : ‖p.1‖ ≤ 1/4 := by simpa only [mem_closedBall, dist_zero_right] using hp.1
    have hs' := hp.2
    have hx' : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right, U] using hx
    have hNorm : ‖p.1 + p.2 • x‖ < 1 := by
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_smul, Real.norm_of_nonneg hs'.1]
      calc _ ≤ ‖p.1‖ + p.2 * 1 := add_le_add le_rfl (mul_le_mul_of_nonneg_left hx'.le hs'.1)
        _ < 1 := by linarith [hs'.2]
    exact posDef_of_uniform_of_symmetric he hs (by simpa [fixedBallOpens, affineChartMap] using hNorm)
  obtain ⟨C,hC,hP⟩ := exists_interior_word_point_bound_family
    ((isCompact_closedBall _ _).prod isCompact_Icc : IsCompact J) (isOpen_ball : IsOpen U)
    (isCompact_singleton (x := (0 : X n))) (singleton_subset_iff.mpr (mem_ball_self (by norm_num)))
    A hA hpos ([] : List (I n))
  refine ⟨C,hC,fun y hy r hr b hb hB => ?_⟩
  let u := b ∘ affineChartMap y r
  have hu : ContDiff ℝ ∞ u := hb.comp (contDiff_affineChartMap y r)
  have hAeq (x : X n) (hx : x ∈ U) : Lop (A (y,r)) u x = 0 := by
    have hMem : affineChartMap y r x ∈ ball y r := by
      rw [mem_ball, affineChartMap, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
      exact (mul_lt_iff_lt_one_right hr.1).mpr (by simpa [U, mem_ball, dist_zero_right] using hx)
    have hZero := hB _ hMem
    rw [negativeBallDivergence, neg_eq_zero] at hZero
    change Lop (fun i j z => a (affineChartMap y r z) i j) (b ∘ affineChartMap y r) x = 0
    rw [Lop_affine_of_smooth ha hb, hZero, mul_zero]
  have huI : IntegrableOn (fun x => u x^2) U :=
    ((hu.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : X n) 1)).mono_set
      ball_subset_closedBall
  have h := hP (y,r) ⟨hy,hr.1.le,hr.2⟩ u hu hAeq huI 0 (Set.mem_singleton _)
  change |b (y + r • (0 : X n))| ≤ C * Real.sqrt (∫ x in U, b (y + r • x)^2) at h
  rw [smul_zero, add_zero, setIntegral_comp_affineChart_ball (fun z => b z^2) y hr.1, mul_one] at h
  have hrpow : Real.sqrt ((r ^ n)⁻¹) = r ^ (-(n : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg hr.1.le, ← Real.rpow_mul hr.1.le]
    congr 1
    ring
  rwa [Real.sqrt_mul (inv_nonneg.mpr (pow_nonneg hr.1.le n)), hrpow, ← mul_assoc] at h

end CalderonN
