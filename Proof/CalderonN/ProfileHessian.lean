module

public import Proof.CalderonN.MetricConnection
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.HessianContraction
import Mathlib.Tactic

@[expose] public section

/- Port of ProfileHessian.lean from the checked Proposition 5.3 release f308cb9d. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial
open scoped ContDiff Topology
namespace CalderonN
variable {n : ℕ}

open Set MvPolynomial

open OAI.AnisotropicCalderon.AngularPolynomial

/-- The coordinate Hessian from the same covariant jets used in the profile contract. -/
def hessianMatrix (γ : (MetricField n)) (f : (X n) → ℝ) : (MetricField n) :=
  fun y i j => covJet γ f 2 y ![i,j]

def frameHessian (γ : (MetricField n)) (e : (Frame n)) (f : (X n) → ℝ) (y : (X n)) (i j : (I n)) : ℝ :=
  metricPair (hessianMatrix γ f) y (e y i) (e y j)

lemma Profile.frame_quadratic {Y : Set (X n)} {γ : (MetricField n)} {e : (Frame n)} {r : (X n) → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (h : Profile Y γ e r floor c₀ Cj)
    {y : (X n)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) (v : (I n) → ℝ) :
    (∑ i, ∑ j, frameHessian γ e (fun x => Real.log (r x)) y i j * v i * v j) ≤
      -(c₀ * beta γ r y) * ∑ i, (v i)^2 := by
  have hH := (h.2 y hy).2.2.1 (frameVector e y (WithLp.toLp 2 v))
  change metricPair (hessianMatrix γ (fun x => Real.log (r x))) y
      (frameVector e y (WithLp.toLp 2 v)) (frameVector e y (WithLp.toLp 2 v)) ≤ _ at hH
  rw [metricPair_frame_expansion, metricPair_frameVector γ e y _ _ he] at hH
  simpa only [frameHessian, WithLp.ofLp_toLp, pow_two] using hH

/-- The profile Hessian bound controls the full Fischer tensor contraction for arbitrary
    polynomial components, including the derivatives of a harmonic homogeneous component. -/
lemma Profile.fischer_contraction {Y : Set (X n)} {γ : (MetricField n)} {e : (Frame n)} {r : (X n) → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (h : Profile Y γ e r floor c₀ Cj)
    {y : (X n)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (q : (I n) → MvPolynomial (I n) ℝ) :
    (∑ i, ∑ j, frameHessian γ e (fun x => Real.log (r x)) y i j * fischerInner (q i) (q j)) ≤
      -(c₀ * beta γ r y) * ∑ i, fischerInner (q i) (q i) :=
  OAI.AnisotropicCalderon.HessianContraction.fischer_matrix_contraction_le_of_quadratic _ _
    (h.frame_quadratic hy he) q

lemma Profile.fischer_gradient_contraction {Y : Set (X n)} {γ : (MetricField n)} {e : (Frame n)} {r : (X n) → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (h : Profile Y γ e r floor c₀ Cj)
    {y : (X n)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (v : MvPolynomial (I n) ℝ) (hv : v.IsHomogeneous k) :
    (∑ i, ∑ j, frameHessian γ e (fun x => Real.log (r x)) y i j *
      fischerInner (pderiv i v) (pderiv j v)) ≤
      -(c₀ * beta γ r y) * k * fischerInner v v := by
  have hq := h.fischer_contraction hy he (fun i => pderiv i v)
  rw [sum_fischerInner_pderiv_self hv] at hq
  simpa only [mul_assoc] using hq

lemma Profile.frame_trace {Y : Set (X n)} {γ : (MetricField n)} {e : (Frame n)} {r : (X n) → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (h : Profile Y γ e r floor c₀ Cj)
    {y : (X n)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0) :
    (∑ i, frameHessian γ e (fun x => Real.log (r x)) y i i) ≤ -(n : ℝ) * c₀ * beta γ r y := by
  have hi (i : (I n)) : frameHessian γ e (fun x => Real.log (r x)) y i i ≤ -(c₀ * beta γ r y) := by
    have hh := (h.2 y hy).2.2.1 (e y i)
    change frameHessian γ e (fun x => Real.log (r x)) y i i ≤
      -(c₀ * beta γ r y) * metricPair γ y (e y i) (e y i) at hh
    simpa only [he i i, ite_true, mul_one] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  convert hs using 1 <;> ring

/-- The C[av] term in the manuscript degree calculation, with C=2k Hess(log r). -/
lemma Profile.scaled_fischer_gradient_contraction {Y : Set (X n)} {γ : (MetricField n)} {e : (Frame n)} {r : (X n) → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (h : Profile Y γ e r floor c₀ Cj)
    {y : (X n)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (v : MvPolynomial (I n) ℝ) (hv : v.IsHomogeneous k) :
    (∑ i, ∑ j, (2*k*frameHessian γ e (fun x => Real.log (r x)) y i j) *
      fischerInner (pderiv i v) (pderiv j v)) ≤
      -2*c₀*k^2*beta γ r y*fischerInner v v := by
  have hh := mul_le_mul_of_nonneg_left (h.fischer_gradient_contraction hy he v hv)
    (show 0 ≤ 2*(k:ℝ) by positivity)
  convert hh using 1
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · ring

end CalderonN
