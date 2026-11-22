module

public import Proof.CalderonN.NormalJacobiBoundary
public import Proof.CalderonN.SphereFrame

import Proof.CalderonN.JacobiInterval
import Proof.CalderonN.MetricConnection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped Interval ContDiff InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem connection_sum_frame (g : (MetricField dim)) (y v : (X dim)) (b : (I dim) → (X dim)) (z : (X dim)) :
    connection g y v (∑ i, z i • b i) = ∑ i, z i • connection g y v (b i) := by
  simp only [← connectionBilinear_apply, map_sum, map_smul]

/-- The time derivative of a vector reconstructed from a parallel frame. -/
theorem hasDerivAt_parallelFrame_sum
    (g : (MetricField dim)) (y v : (X dim)) (F : ℝ → (I dim) → (X dim)) (Z : ℝ → (X dim)) {t : ℝ} {z' : (X dim)}
    (hZ : HasDerivAt Z z' t)
    (hF : ∀ i, HasDerivAt (fun s => F s i) (-connection g y v (F t i)) t) :
    HasDerivAt (fun s => ∑ i, Z s i • F s i)
      ((∑ i, z' i • F t i) - connection g y v (∑ i, Z t i • F t i)) t := by
  have hZ' (i : (I dim)) : HasDerivAt (fun s => Z s i) (z' i) t :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hZ
  convert HasDerivAt.fun_sum (u := (Finset.univ : Finset (I dim))) (fun i _ =>
    (hZ' i).smul (hF i)) using 1
  rw [connection_sum_frame]
  simp only [smul_neg,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  abel

/-- In a parallel frame the covariant time derivative differentiates only
the coordinate vector, for the actual variation along the radial curve. -/
theorem variationCovariantTime_parallelFrame
    (g : (MetricField dim)) {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (F : ℝ → (I dim) → (X dim)) (Z : ℝ → (X dim)) {t : ℝ} {z' : (X dim)}
    (hZ : HasDerivAt Z z' t)
    (hF : ∀ i, HasDerivAt (fun s => F s i)
      (-connection g (q (0,t)) (timeVelocity q (0,t)) (F t i)) t)
    (hEq : (fun s => pathVariation q (0,s)) =ᶠ[nhds t] fun s => ∑ i, Z s i • F s i) :
    variationCovariantTime g q 0 t = ∑ i, z' i • F t i := by
  have hsum := hasDerivAt_parallelFrame_sum g (q (0,t)) (timeVelocity q (0,t)) F Z hZ hF
  have hJ := hasDerivAt_geodesicTime ((contDiff_pathVariation hq).differentiable (by simp) (0,t))
  have he := hJ.unique (hsum.congr_of_eventuallyEq hEq)
  have hrep : pathVariation q (0,t) = ∑ i, Z t i • F t i := hEq.eq_of_nhds
  rw [variationCovariantTime,he,hrep,sub_add_cancel]

/-- Parallel transport preserves the inner product of two vector fields
along the same curve. -/
theorem metricPair_parallel_eq_initial {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {g : (MetricField dim)} (hg : SmoothMetric Ω g) {q : ℝ → (X dim)} (V A B : ℝ → (X dim))
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ Ω ∧ HasDerivAt q (V t) t)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt A (-connection g (q t) (V t) (A t)) t)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt B (-connection g (q t) (V t) (B t)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    metricPair g (q t) (A t) (B t) = metricPair g (q 0) (A 0) (B 0) := by
  let f (s : ℝ) := metricPair g (q s) (A s) (B s)
  have h (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt f 0 s := by
    have h' := hasDerivAt_metricPair hΩ hg (hpath s hs).1 (hpath s hs).2 (hA s hs) (hB s hs)
    simpa [f,metricPair] using h'
  have hEq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := t) (f := f) (f' := fun _ => (0 : ℝ))
    (fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact h s ⟨hs.1,hs.2.trans ht.2⟩) intervalIntegrable_const
  exact sub_eq_zero.mp (by simpa using hEq.symm)

/-- Parallel transport of the frame columns preserves their Gram
matrix along the whole geodesic interval. -/
theorem parallelFrame_metricPair_eq_initial {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {g : (MetricField dim)} (hg : SmoothMetric Ω g) {q : ℝ → (X dim)} (V : ℝ → (X dim))
    (F : ℝ → (I dim) → (X dim))
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ Ω ∧ HasDerivAt q (V t) t)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
      HasDerivAt (fun s => F s i) (-connection g (q t) (V t) (F t i)) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i j : (I dim)) :
    metricPair g (q t) (F t i) (F t j) = metricPair g (q 0) (F 0 i) (F 0 j) :=
  metricPair_parallel_eq_initial hΩ hg V _ _ hpath (fun s hs => hF s hs i)
    (fun s hs => hF s hs j) ht

/-- The framed acceleration estimate controls the actual geodesic
boundary form. It is enough to carry an orthonormal frame at the initial
point because the transport equation preserves all its inner products. -/
theorem jacobi_variation_boundary_lower
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)} (hg : SmoothMetric Ω g)
    {q : ℝ × ℝ → (X dim)} (hq : ContDiff ℝ ∞ q)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1, q (0,t) ∈ Ω)
    (F : ℝ → (I dim) → (X dim)) (Z Z' Z'' : ℝ → (X dim))
    (hF₀ : ∀ i j, metricPair g (q (0,0)) (F 0 i) (F 0 j) = if i = j then 1 else 0)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, HasDerivAt (fun s => F s i)
      (-connection g (q (0,t)) (timeVelocity q (0,t)) (F t i)) t)
    (hEq : ∀ t ∈ Icc (0 : ℝ) 1,
      (fun s => pathVariation q (0,s)) =ᶠ[nhds t] fun s => ∑ i, Z s i • F s i)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Z (Z' t) t)
    (hZ' : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt Z' (Z'' t) t)
    {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/2)
    (hacc : ∀ t ∈ Icc (0 : ℝ) 1, ‖Z'' t‖ ≤ ε * ‖Z t‖) :
    ‖Z 1-Z 0‖^2-2*ε*(‖Z 0‖+‖Z 1‖)^2 ≤
      metricPair g (q (0,1)) (variationCovariantTime g q 0 1) (pathVariation q (0,1)) -
      metricPair g (q (0,0)) (variationCovariantTime g q 0 0) (pathVariation q (0,0)) := by
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      metricPair g (q (0,s)) (variationCovariantTime g q 0 s) (pathVariation q (0,s)) =
        ⟪Z' s,Z s⟫_ℝ := by
    have hframe (i j : (I dim)) : metricPair g (q (0,s)) (F s i) (F s j) = if i = j then 1 else 0 :=
      (parallelFrame_metricPair_eq_initial hΩ hg (fun v => timeVelocity q (0,v)) F
        (fun v hv => ⟨hpath v hv,hasDerivAt_geodesicTime (hq.differentiable (by simp) (0,v))⟩)
        hF hs i j).trans (hF₀ i j)
    rw [variationCovariantTime_parallelFrame g hq F Z (hZ s hs) (hF s hs) (hEq s hs),
      (hEq s hs).eq_of_nhds]
    let e : (Frame dim) := fun _ => F s
    change metricPair g (q (0,s)) (frameVector e (q (0,s)) (Z' s)) (frameVector e (q (0,s)) (Z s)) =
      ⟪Z' s,Z s⟫_ℝ
    rw [metricPair_frameVector _ _ _ _ _ hframe,EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial,dotProduct]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hp 1 ⟨zero_le_one,le_rfl⟩,hp 0 ⟨le_rfl,zero_le_one⟩]
  exact jacobi_boundaryForm_lower Z Z' Z'' ε hε hε' hZ hZ' hacc

end CalderonN
