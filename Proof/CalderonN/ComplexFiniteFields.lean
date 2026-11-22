module

public import Proof.CalderonN.ComplexZonalPolynomial

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {n : ℕ} [NeZero n]
open OAI.AnisotropicCalderon.AngularPolynomial

variable {ι : Type*} [Fintype ι]

def pairedPolynomialField (g : (MetricField n)) (e : (Frame n)) (b : ι → MvPolynomial (I n) ℝ)
    (c d : (X n) → ι → ℝ) : (Field n) := fun z =>
  movingFrameComplexPolynomial g e (finitePolynomialField b c z.1) (finitePolynomialField b d z.1) z

lemma pairedPolynomialField_horizontal {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (b : ι → MvPolynomial (I n) ℝ) (c d : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y)
    {y : (X n)} (hy : y ∈ Y) (w a : (X n)) :
    horizontal g (pairedPolynomialField g e b c d) y w a =
      movingFrameComplexPolynomial g e (covariantPolynomialDerivative g e b c y a)
        (covariantPolynomialDerivative g e b d y a) (y,w) := by
  change horizontal g (fun z => Complex.mk (evaluatedPolynomialField g e b c z) (evaluatedPolynomialField g e b d z)) y w a = _
  rw [horizontal_complexMk g _ _ y w a
    ((contDiffAt_evaluatedPolynomialField hY h e he b c hy (hc.contDiffAt (hY.mem_nhds hy)) w).differentiableAt (by simp))
    ((contDiffAt_evaluatedPolynomialField hY h e he b d hy (hd.contDiffAt (hY.mem_nhds hy)) w).differentiableAt (by simp)),
    evaluatedPolynomialField_horizontal hY h hK e he hframe b c hy
      ((hc.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)),
    evaluatedPolynomialField_horizontal hY h hK e he hframe b d hy
      ((hd.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))]
  rfl

lemma fiberSq_pairedPolynomialField (g : (MetricField n)) (e : (Frame n)) (y : (X n))
    (hframe : ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : (X n) → ι → ℝ) :
    fiberSq e y (fun w => pairedPolynomialField g e b c d (y,w)) =
      normalizedFischerSquare k (finitePolynomialField b c y) + normalizedFischerSquare k (finitePolynomialField b d y) := by
  change fiberSq e y (fun w => movingFrameComplexPolynomial g e (finitePolynomialField b c y)
    (finitePolynomialField b d y) (y,w)) = _
  exact fiberSq_movingFrameComplexPolynomial g e y hframe _ _
    (finitePolynomialField_homogeneous b hb c y) (finitePolynomialField_homogeneous b hb d y)
    (finitePolynomialField_harmonic b hΔ c y) (finitePolynomialField_harmonic b hΔ d y)

lemma fiberSq_pairedPolynomialField_horizontal {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y, ∀ i j, metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {k : ℕ} (hk : 1 ≤ k) (b : ι → MvPolynomial (I n) ℝ) (hb : ∀ a, (b a).IsHomogeneous k)
    (hΔ : ∀ a, laplacian (b a) = 0) (c d : (X n) → ι → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y)
    {y : (X n)} (hy : y ∈ Y) (i : (I n)) :
    fiberSq e y (fun w => horizontal g (pairedPolynomialField g e b c d) y w (e y i)) =
      normalizedFischerSquare k (covariantPolynomialDerivative g e b c y (e y i)) +
        normalizedFischerSquare k (covariantPolynomialDerivative g e b d y (e y i)) := by
  have hfun : (fun w => horizontal g (pairedPolynomialField g e b c d) y w (e y i)) =
      fun w => movingFrameComplexPolynomial g e (covariantPolynomialDerivative g e b c y (e y i))
        (covariantPolynomialDerivative g e b d y (e y i)) (y,w) := by
    funext w
    exact pairedPolynomialField_horizontal hY h hK e he hframe b c d hc hd hy w (e y i)
  rw [hfun]
  exact fiberSq_movingFrameComplexPolynomial g e y (hframe y hy) _ _
    (covariantPolynomialDerivative_homogeneous hk g e b hb c y (e y i))
    (covariantPolynomialDerivative_homogeneous hk g e b hb d y (e y i))
    (covariantPolynomialDerivative_harmonic g e b hΔ c y (e y i) (frameConnection_skew hY h hK e he hframe hy (e y i)))
    (covariantPolynomialDerivative_harmonic g e b hΔ d y (e y i) (frameConnection_skew hY h hK e he hframe hy (e y i)))

lemma Profile.integrable_modeFischerDensity {Y : Set (X n)} (hY : IsOpen Y) {K : ℝ} {g : (MetricField n)}
    (h : Elliptic Y K g) (hK : 0 < K) (e : (Frame n))
    (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (k : ℕ) (b : ι → MvPolynomial (I n) ℝ) (c : (X n) → ι → ℝ) (hc : ContDiff ℝ ∞ c)
    (hcompact : HasCompactSupport c) (hsupp : tsupport c ⊆ Y) :
    Integrable (modeFischerDensity g e r k b c) := by
  have hF := contDiffOn_fischerPair (Ω:=Y) b b c c hc.contDiffOn hc.contDiffOn
  have hH : ContDiffOn ℝ ∞ (covariantFrameEnergy g e b c) Y := by
    apply ContDiffOn.sum
    intro i _
    have hd := derivativeCoefficientFamily_smoothOn hY h hK e he c (fun x => e x i) hc.contDiffOn (he i)
    have hh := contDiffOn_fischerPair (derivativePolynomialFamily b) (derivativePolynomialFamily b) _ _ hd hd
    simpa only [← covariantPolynomialDerivative_eq_augmented] using hh
  have hβ := hp.contDiffOn_beta hY h hK hfloor
  have hiβ := hp.contDiffOn_beta_inv hY h hK hfloor
  have hs : ContDiffOn ℝ ∞ (modeFischerDensity g e r k b c) Y :=
    (h.contDiffOn_density hK).mul
      (((hH.add ((contDiffOn_const.mul (hβ.pow 2)).mul hF)).add
        ((contDiffOn_const.mul hiβ).mul hH)).add ((contDiffOn_const.mul hβ).mul hF))
  exact integrable_local_supported hY c hcompact hsupp _ hs
    (fun y hy => modeFischerDensity_zero_outside g e r k b c hy)

end CalderonN
