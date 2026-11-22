module

public import Proof.CalderonN.SignedNormalAdjoint
public import Proof.CalderonN.FlatBallPolynomials

import Proof.CalderonN.NormalizedVelocityAtZero
import Proof.CalderonN.FlatVelocityAdjoint
import Proof.CalderonN.BallVelocityDatumCongruence
import Proof.CalderonN.TraceFreeFlatQuadratic
import Mathlib.Tactic

/-! Adapted from `SignedAdjointAtZero` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2000000

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The signed-radius remainder at zero is exactly the trace-free
quadratic from the two translation terms. -/
theorem signedNormalAdjointRemainder_zero
    {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    {lam : ℝ} {y : (X dim)} {Y Ω : Set (X dim)} {ρ : ℝ}
    (hY : IsOpen Y) (hE : ContDiff ℝ ∞ (E lam))
    (hN : NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ)) (hy : y ∈ Y)
    (he : ∀ i j, metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    {c : ℝ} (hc : 0 < c) (hγ : γ lam y = c • g lam y)
    (b : (I dim) → ℝ) (i j : (I dim))
    (hα : ContDiffOn ℝ ∞
      (fun w : (X dim) => signedNormalFirstAdjoint γ g E e j ((lam,(y,(0,b))),w)) ({0}ᶜ : Set (X dim)))
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    let a (k : (I dim)) := frameCoordinates (γ lam) y (e lam y) (axis k)
    signedNormalAdjointRemainder γ g E e i j ((lam,(y,(0,b))),w) =
      ((dim:ℝ)*((dim:ℝ)+2))*(flatLinear (a i) w * flatLinear (a j) w - flatLinear (a i) (a j)/(dim:ℝ)) := by
  let p : (SignedNormalParameter dim) := (lam,(y,(0,b)))
  let t := Real.sqrt c⁻¹
  have ht : 0 < t := Real.sqrt_pos.mpr (inv_pos.mpr hc)
  have ht_sq : t^2 = c⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hc.le)
  let a (k : (I dim)) := frameCoordinates (γ lam) y (e lam y) (axis k)
  let m := signedNormalMetric g E e
  let V := signedNormalVelocity γ E e
  let S : Set (X dim) := ({0}ᶜ : Set (X dim))
  let m₀ (_ : (X dim) × (X dim)) := t^2 • (1 : (Mat dim))
  let V₀ (k : (I dim)) (q : (X dim) × (X dim)) := a k + b k • q.2
  have hS : IsOpen S := isClosed_singleton.isOpen_compl
  have hSS : (standardSphere dim) ⊆ S := by
    intro z hz
    change z ≠ 0
    intro heq
    have hn := mem_sphere_zero_iff_norm.mp hz
    simp [heq] at hn
  have hm : (fun z => m (p,z)) = fun z => m₀ (0,z) := by
    funext z
    change normalizedBallMetric (g lam) (E lam) (e lam) y 0 z = t^2 • (1 : (Mat dim))
    rw [normalizedBallMetric_zero_of_conformal hE hN hy he hc hγ,ht_sq]
  have hV (k : (I dim)) : (fun z => V k (p,z)) = fun z => V₀ k (0,z) := by
    funext z
    exact scaledNormalTraceVelocity_zero hY hE hN hy he (b k) z (axis k)
  have hm' : SmoothMetric univ (fun z => m (p,z)) := by
    rw [hm]
    exact smoothMetric_flatBallMetric ht
  have hVs (k : (I dim)) : ContDiffOn ℝ ∞ (fun z => V k (p,z)) S := by
    rw [hV k]
    change ContDiffOn ℝ ∞ (fun z : (X dim) => a k + b k • z) S
    exact ((contDiff_const (c := a k)).add ((contDiff_const (c := b k)).smul
      (contDiff_id : ContDiff ℝ ∞ (id : (X dim) → (X dim))))).contDiffOn
  have ha {z : (X dim)} (hz : z ∈ (standardSphere dim)) :
      signedNormalFirstAdjoint γ g E e j (p,z) = (dim:ℝ)*flatLinear (a j) z := by
    unfold signedNormalFirstAdjoint
    rw [parametricBallVelocityAdjoint_congr_slice (φ := fun _ => 1) (ψ := fun _ => 1)
      hm (hV j) isOpen_univ hS (subset_univ _) hSS (subset_univ _) (by simp [S])
      hm' (hVs j) contDiffOn_const contDiffOn_const (fun _ _ => rfl) hz]
    exact flatVelocityAdjoint_one ht (a j) (b j) hz
  let l : (X dim) := (dim : ℝ) • a j
  have hlin (z : (X dim)) : flatLinear l z = (dim:ℝ)*flatLinear (a j) z := by
    simp [l,flatLinear,real_inner_smul_left]
  have hd : EqOn (fun z => signedNormalFirstAdjoint γ g E e j (p,z))
      (fun z => flatLinear l z) (standardSphere dim) := by
    intro z hz
    exact (ha hz).trans (hlin z).symm
  have hb := parametricBallVelocityAdjoint_congr_slice
    (φ := signedNormalFirstAdjoint γ g E e j) (ψ := fun q => flatLinear l q.2)
    hm (hV i) isOpen_univ hS (subset_univ _) hSS (subset_univ _) (by simp [S])
    hm' (hVs i) hα (contDiff_flatLinear l).contDiffOn hd hw
  change signedNormalAdjointRemainder γ g E e i j (p,w) = _
  unfold signedNormalAdjointRemainder
  change parametricBallVelocityAdjoint m (V i) (signedNormalFirstAdjoint γ g E e j) (p,w) -
    b i * signedNormalFirstAdjoint γ g E e j (p,w) = _
  rw [hb,flatVelocityAdjoint_linear ht (a i) l (b i) hw,ha hw,hlin]
  have hright : flatLinear (a i) l = (dim:ℝ)*flatLinear (a i) (a j) := by
    simp [l,flatLinear,real_inner_smul_right]
  rw [hright]
  ring

/-- Contracting the limiting remainder with the inverse reference metric
cancels the entire constant-mode singular term. -/
theorem sum_inverse_mul_signedNormalAdjointRemainder_zero
    {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    {lam : ℝ} {y : (X dim)} {Y Ω : Set (X dim)} {ρ : ℝ}
    (hY : IsOpen Y) (hE : ContDiff ℝ ∞ (E lam))
    (hN : NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ)) (hy : y ∈ Y)
    (hPos : (γ lam y).PosDef)
    (he : ∀ i j, metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    {c : ℝ} (hc : 0 < c) (hγ : γ lam y = c • g lam y) (b : (I dim) → ℝ)
    (hα : ∀ j : (I dim), ContDiffOn ℝ ∞
      (fun w : (X dim) => signedNormalFirstAdjoint γ g E e j ((lam,(y,(0,b))),w)) ({0}ᶜ : Set (X dim)))
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    ∑ i, ∑ j, (γ lam y)⁻¹ i j *
      signedNormalAdjointRemainder γ g E e i j ((lam,(y,(0,b))),w) = 0 := by
  let a (k : (I dim)) := frameCoordinates (γ lam) y (e lam y) (axis k)
  have hzero := sum_inverse_mul_flatTraceFreeQuadratic_eq_zero (γ lam) y hPos (e lam) he hw
  change ∑ i, ∑ j, (γ lam y)⁻¹ i j * (flatLinear (a i) w * flatLinear (a j) w -
    flatLinear (a i) (a j)/(dim:ℝ)) = 0 at hzero
  calc
    _ = ((dim:ℝ)*((dim:ℝ)+2)) * (∑ i, ∑ j, (γ lam y)⁻¹ i j * (flatLinear (a i) w * flatLinear (a j) w -
      flatLinear (a i) (a j)/(dim:ℝ))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [signedNormalAdjointRemainder_zero hY hE hN hy he hc hγ b i j (hα j) hw]
      dsimp only
      ring
    _ = 0 := by rw [hzero,mul_zero]

end CalderonN
