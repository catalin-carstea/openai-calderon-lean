import Proof.FiniteAngularProjection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.AngularPolynomial

variable {α : Type*} {ι : α → Type*} [∀ i,Fintype (ι i)]

lemma movingFrameComplexPolynomial_sum (g : MetricField) (e : Frame) (s : Finset α)
    (p q : α → MvPolynomial I ℝ) (z : X × X) :
    movingFrameComplexPolynomial g e (∑ i ∈ s,p i) (∑ i ∈ s,q i) z =
      ∑ i ∈ s,movingFrameComplexPolynomial g e (p i) (q i) z := by
  apply Complex.ext <;> simp [movingFrameComplexPolynomial,movingFramePolynomial,map_sum]

def finiteAngularField (g : MetricField) (e : Frame) (s : Finset α) (b : (i : α) → ι i → MvPolynomial I ℝ)
    (c d : (i : α) → X → ι i → ℝ) : Field := fun z =>
  movingFrameComplexPolynomial g e (∑ i ∈ s,finitePolynomialField (b i) (c i) z.1)
    (∑ i ∈ s,finitePolynomialField (b i) (d i) z.1) z

lemma finiteAngularField_eq_sum (g : MetricField) (e : Frame) (s : Finset α) (b : (i : α) → ι i → MvPolynomial I ℝ)
    (c d : (i : α) → X → ι i → ℝ) :
    finiteAngularField g e s b c d = ∑ i ∈ s,pairedPolynomialField g e (b i) (c i) (d i) := by
  funext z
  simp only [Finset.sum_apply]
  change movingFrameComplexPolynomial g e (∑ i ∈ s,finitePolynomialField (b i) (c i) z.1)
    (∑ i ∈ s,finitePolynomialField (b i) (d i) z.1) z =
      ∑ i ∈ s,movingFrameComplexPolynomial g e (finitePolynomialField (b i) (c i) z.1)
        (finitePolynomialField (b i) (d i) z.1) z
  exact movingFrameComplexPolynomial_sum g e s (fun i => finitePolynomialField (b i) (c i) z.1)
    (fun i => finitePolynomialField (b i) (d i) z.1) z

lemma contDiffAt_pairedPolynomialField {κ : Type*} [Fintype κ] {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (b : κ → MvPolynomial I ℝ) (c d : X → κ → ℝ) (hc : ContDiffOn ℝ ∞ c Y) (hd : ContDiffOn ℝ ∞ d Y)
    {y : X} (hy : y ∈ Y) (w : X) : ContDiffAt ℝ ∞ (pairedPolynomialField g e b c d) (y,w) := by
  have hC := contDiffAt_evaluatedPolynomialField hY h e he b c hy (hc.contDiffAt (hY.mem_nhds hy)) w
  have hD := contDiffAt_evaluatedPolynomialField hY h e he b d hy (hd.contDiffAt (hY.mem_nhds hy)) w
  exact Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp (y,w) (hC.prodMk hD)

/-- The actual horizontal derivative of a finite angular field is the sum of the actual
    covariant derivatives of its polynomial components. -/
theorem finiteAngularField_horizontal {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (s : Finset α) (b : (i : α) → ι i → MvPolynomial I ℝ) (c d : (i : α) → X → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiffOn ℝ ∞ (c i) Y) (hd : ∀ i ∈ s,ContDiffOn ℝ ∞ (d i) Y)
    {y : X} (hy : y ∈ Y) (w a : X) :
    horizontal g (finiteAngularField g e s b c d) y w a =
      movingFrameComplexPolynomial g e (∑ i ∈ s,covariantPolynomialDerivative g e (b i) (c i) y a)
        (∑ i ∈ s,covariantPolynomialDerivative g e (b i) (d i) y a) (y,w) := by
  have hD (i : α) (hi : i ∈ s) := ((contDiffAt_pairedPolynomialField hY h e he (b i) (c i) (d i)
    (hc i hi) (hd i hi) hy w).differentiableAt (by simp)).hasFDerivAt
  have hsum := HasFDerivAt.sum (u:=s) (fun i hi => hD i hi)
  rw [finiteAngularField_eq_sum,horizontal,hsum.fderiv,movingFrameComplexPolynomial_sum]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact pairedPolynomialField_horizontal hY h hK e he hframe (b i) (c i) (d i) (hc i hi) (hd i hi) hy w a

end ShrinkingSpheres
