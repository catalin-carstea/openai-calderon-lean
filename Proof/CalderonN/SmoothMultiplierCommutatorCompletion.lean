module

public import Proof.CalderonN.SmoothPairingCompletion
public import Proof.CalderonN.SmoothBoundaryMultiplier

import Proof.CalderonN.ActualFiniteRadialMidpoint

import Mathlib.Tactic

/-! The actual skew adjoint of a real multiplier commutator extends
a finite harmonic norm estimate to smooth boundary inputs. -/

public section

noncomputable section
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2300000
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothSubtractData (u v : SmoothData dim) : SmoothData dim :=
  ⟨u.1-v.1,u.2.sub v.2⟩

theorem smoothSphereLift_subtract (hn : 3 ≤ dim) (u v : SmoothData dim) :
    smoothSphereLift (smoothSubtractData u v).1 (smoothSubtractData u v).2 =
      smoothSphereLift u.1 u.2-smoothSphereLift v.1 v.2 := by
  let U : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let V : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  change smoothSphereLift (U-V).1 (smoothBallData_contDiff (U-V)) = _
  simpa only [smoothBoundaryLiftL_apply] using (smoothBoundaryLiftL hn).map_sub U V

theorem smooth_multiplier_commutator_adjoint (hn : 3 ≤ dim)
    (m : SmoothData dim) (T : SmoothData dim → SmoothData dim)
    (hT : ∀ u v, ⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift v.1 v.2⟫_ℝ =
      ⟪smoothSphereLift u.1 u.2,smoothSphereLift (T v).1 (T v).2⟫_ℝ)
    (x y : SmoothData dim) :
    let Z (v : SmoothData dim) := smoothSphereLift v.1 v.2
    let M := smoothDataMul m
    let S (v : SmoothData dim) := smoothSubtractData (T (M v)) (M (T v))
    let Sadj (v : SmoothData dim) := smoothSubtractData (M (T v)) (T (M v))
    ⟪Z (S x),Z y⟫_ℝ = ⟪Z x,Z (Sadj y)⟫_ℝ := by
  let Z (v : SmoothData dim) := smoothSphereLift v.1 v.2
  let M := smoothDataMul m
  let S (v : SmoothData dim) := smoothSubtractData (T (M v)) (M (T v))
  let Sadj (v : SmoothData dim) := smoothSubtractData (M (T v)) (T (M v))
  have hM (x y : SmoothData dim) : ⟪Z (M x),Z y⟫_ℝ = ⟪Z x,Z (M y)⟫_ℝ := by
    simp only [Z,smoothSphereLift_inner]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    change (m.1 z*x.1 z)*y.1 z = x.1 z*(m.1 z*y.1 z)
    ring
  have hT' (u v : SmoothData dim) : ⟪Z (T u),Z v⟫_ℝ = ⟪Z u,Z (T v)⟫_ℝ := hT u v
  change ⟪Z (smoothSubtractData (T (M x)) (M (T x))),Z y⟫_ℝ =
    ⟪Z x,Z (smoothSubtractData (M (T y)) (T (M y)))⟫_ℝ
  simp only [Z,smoothSphereLift_subtract hn,inner_sub_left,inner_sub_right]
  change ⟪Z (T (M x)),Z y⟫_ℝ-⟪Z (M (T x)),Z y⟫_ℝ =
    ⟪Z x,Z (M (T y))⟫_ℝ-⟪Z x,Z (T (M y))⟫_ℝ
  rw [hT' (M x) y,hM x (T y),hM (T x) y,hT' x (M y)]

theorem norm_smooth_multiplier_commutator_half_of_finite (hn : 3 ≤ dim)
    (m : SmoothData dim) (T : SmoothData dim → SmoothData dim)
    (hT : ∀ u v, ⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift v.1 v.2⟫_ℝ =
      ⟪smoothSphereLift u.1 u.2,smoothSphereLift (T v).1 (T v).2⟫_ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hFin : ∀ f : HarmonicFiniteCoefficients dim,
      let u := harmonicFiniteSmooth f
      ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num)
        (smoothSubtractData (T (smoothDataMul m u)) (smoothDataMul m (T u)))‖ ≤
        C*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖)
    (u : SmoothData dim) :
    ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num)
      (smoothSubtractData (T (smoothDataMul m u)) (smoothDataMul m (T u)))‖ ≤
      C*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖ := by
  let Z (x : SmoothData dim) := smoothSphereLift x.1 x.2
  let M := smoothDataMul m
  let S (x : SmoothData dim) := smoothSubtractData (T (M x)) (M (T x))
  let Sadj (x : SmoothData dim) := smoothSubtractData (M (T x)) (T (M x))
  have hAdj (x y : SmoothData dim) : ⟪Z (S x),Z y⟫_ℝ = ⟪Z x,Z (Sadj y)⟫_ℝ :=
    smooth_multiplier_commutator_adjoint hn m T hT x y
  have hPair (f g : HarmonicFiniteCoefficients dim) :
      |⟪Z (S (harmonicFiniteSmooth f)),finiteHarmonicSphereL hn g⟫_ℝ| ≤
        C*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖*‖harmonicBoundaryFiniteL (-(1/2) : ℝ) g‖ := by
    rw [finiteHarmonicSphereL_apply]
    have hh := abs_integral_mul_le_smoothBoundarySobolev hn (-(1/2:ℝ)) (by norm_num) (by norm_num)
      (S (harmonicFiniteSmooth f)) (harmonicFiniteSmooth g)
    rw [smoothBoundarySobolev_order_eq hn (neg_neg (1/2:ℝ)) _ (by norm_num),
      smoothBoundarySobolev_harmonicFiniteSmooth] at hh
    simp only [Z,smoothSphereLift_inner]
    exact hh.trans (mul_le_mul_of_nonneg_right (hFin f) (norm_nonneg _))
  have hSmooth := abs_smooth_pair_le_of_finite_harmonic hn S Sadj hAdj (1/2:ℝ) (-(1/2):ℝ) C
    (by norm_num) (by norm_num) hPair
  have hBound := norm_smoothBoundarySobolev_le_of_finite_tests hn (-(1/2:ℝ)) (by norm_num) (by norm_num)
    (S u) (C*‖smoothBoundarySobolev hn (1/2:ℝ) (by norm_num) u‖) (by positivity)
    (fun g => by
      have hh := hSmooth u (harmonicFiniteSmooth g)
      rw [smoothSphereLift_inner,smoothBoundarySobolev_harmonicFiniteSmooth] at hh
      exact hh)
  rw [smoothBoundarySobolev_order_eq hn (neg_neg (1/2:ℝ)) _ (by norm_num)] at hBound
  exact hBound

theorem norm_smooth_multiplier_commutator_negHalf_of_half (hn : 3 ≤ dim)
    (m : SmoothData dim) (T : SmoothData dim → SmoothData dim)
    (hT : ∀ u v, ⟪smoothSphereLift (T u).1 (T u).2,smoothSphereLift v.1 v.2⟫_ℝ =
      ⟪smoothSphereLift u.1 u.2,smoothSphereLift (T v).1 (T v).2⟫_ℝ)
    (C : ℝ) (hC : 0 ≤ C) :
    let S (v : SmoothData dim) :=
      smoothSubtractData (T (smoothDataMul m v)) (smoothDataMul m (T v))
    (∀ v : SmoothData dim, ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (S v)‖ ≤
      C*‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) v‖) →
    ∀ u : SmoothData dim, ‖smoothBoundarySobolev hn (-(1/2) : ℝ) (by norm_num) (S u)‖ ≤
      C*‖smoothBoundarySobolev hn (-(1/2) : ℝ) (by norm_num) u‖ := by
  dsimp only
  intro hHalf u
  let Z (v : SmoothData dim) := smoothSphereLift v.1 v.2
  let M := smoothDataMul m
  let S (v : SmoothData dim) := smoothSubtractData (T (M v)) (M (T v))
  let Sadj (v : SmoothData dim) := smoothSubtractData (M (T v)) (T (M v))
  have hAdj (v : SmoothData dim) : Z (Sadj v) = -Z (S v) := by
    simp only [Z,Sadj,S,smoothSphereLift_subtract hn,neg_sub]
  apply norm_smoothBoundarySobolev_le_of_finite_tests hn (1/2 : ℝ) (by norm_num) (by norm_num)
    (S u) (C*‖smoothBoundarySobolev hn (-(1/2) : ℝ) (by norm_num) u‖) (by positivity)
  intro f
  let v := harmonicFiniteSmooth f
  have hComm : ⟪Z (S u),Z v⟫_ℝ = ⟪Z u,Z (Sadj v)⟫_ℝ :=
    smooth_multiplier_commutator_adjoint hn m T hT u v
  rw [hAdj,inner_neg_right] at hComm
  have hPair := abs_integral_mul_le_smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) (by norm_num)
    u (S v)
  have hI (x y : SmoothData dim) :
      ⟪Z x,Z y⟫_ℝ = ∫ z : ↥(standardSphere dim), x.1 z*y.1 z ∂(sphereProbability dim) :=
    smoothSphereLift_inner _ _ x.2 y.2
  change |∫ z : ↥(standardSphere dim), (S u).1 z*v.1 z ∂(sphereProbability dim)| ≤ _
  rw [← hI (S u) v,hComm,abs_neg,hI u (S v)]
  refine hPair.trans ?_
  rw [← smoothBoundarySobolev_harmonicFiniteSmooth hn (1/2 : ℝ) (by norm_num) f]
  exact (mul_le_mul_of_nonneg_left (hHalf v) (norm_nonneg _)).trans_eq (by ring)

end CalderonN
