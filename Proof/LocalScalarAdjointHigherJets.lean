import Proof.CoordinateFiniteSumCalculus
import Proof.CoordinateProductThreeJetAlgebra
import Proof.Archive.ScalarAdjointCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

lemma coordinate_const_mul {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (c : ℝ) (i : I) :
    coordDeriv i (fun x => c*f x) y = c*coordDeriv i f y := by
  simpa only [coordDeriv,fderiv_const_apply,zero_apply,zero_mul,zero_add] using
    coordinate_mul hY contDiffOn_const hf hy i

lemma coordinate_second_const_mul {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (c : ℝ) (i j : I) :
    coordDeriv i (coordDeriv j (fun x => c*f x)) y = c*coordDeriv i (coordDeriv j f) y := by
  have he : coordDeriv j (fun x => c*f x) =ᶠ[𝓝 y] (fun x => c*coordDeriv j f x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_const_mul hY hf hx c j
  change fderiv ℝ (coordDeriv j (fun x => c*f x)) y (axis i) = _
  rw [he.fderiv_eq]
  exact coordinate_const_mul hY (contDiffOn_coordDeriv hY hf j) hy c i

/-- Local-coordinate version of the supplied second derivative formula for the
first coefficient of the scalar formal-adjoint defect. -/
lemma coordinate_second_adjointFirstCoefficient {Y : Set X} (hY : IsOpen Y)
    (μ : X → ℝ) (a : MetricField) (hμ : ContDiffOn ℝ ∞ μ Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y) (hpos : ∀ x ∈ Y,μ x ≠ 0)
    {y : X} (hy : y ∈ Y) (i k l : I) :
    coordDeriv k (coordDeriv l (fun x => adjointFirstCoefficient (fun j => axis j) μ a x i)) y =
      2*coordDeriv k (coordDeriv l (fun x => (μ x)⁻¹)) y*(∑ j,coordDeriv j (fun x => μ x*a x i j) y)+
      2*coordDeriv l (fun x => (μ x)⁻¹) y*(∑ j,coordDeriv k (coordDeriv j (fun x => μ x*a x i j)) y)+
      2*coordDeriv k (fun x => (μ x)⁻¹) y*(∑ j,coordDeriv l (coordDeriv j (fun x => μ x*a x i j)) y)+
      2*(μ y)⁻¹*(∑ j,coordDeriv k (coordDeriv l (coordDeriv j (fun x => μ x*a x i j))) y) := by
  let F (j : I) (x : X) := μ x*a x i j
  let b (x : X) := ∑ j,coordDeriv j (F j) x
  have hF (j : I) : ContDiffOn ℝ ∞ (F j) Y := hμ.mul (ha i j)
  have hb : ContDiffOn ℝ ∞ b Y := ContDiffOn.sum (fun j _ => contDiffOn_coordDeriv hY (hF j) j)
  have hn : ContDiffOn ℝ ∞ (fun x => (μ x)⁻¹) Y := hμ.inv hpos
  have he : (fun x => adjointFirstCoefficient (fun j => axis j) μ a x i) =
      (fun x => 2*((μ x)⁻¹*b x)) := by
    funext x
    change 2*(μ x)⁻¹*(∑ j,coordDeriv j (F j) x) = _
    dsimp only [b]
    ring
  rw [he,coordinate_second_const_mul hY (hn.mul hb) hy 2 k l,coordinate_second_mul hY hn hb hy k l]
  have hs (u : I) : coordDeriv u b y = ∑ j,coordDeriv u (coordDeriv j (F j)) y :=
    coordinate_sum hY _ (fun j => contDiffOn_coordDeriv hY (hF j) j) hy u
  have hs2 : coordDeriv k (coordDeriv l b) y = ∑ j,coordDeriv k (coordDeriv l (coordDeriv j (F j))) y :=
    coordinate_second_sum hY _ (fun j => contDiffOn_coordDeriv hY (hF j) j) hy k l
  rw [hs k,hs l,hs2]
  dsimp only [b,F]
  ring

lemma coordinate_second_adjointFirstCoefficient_bound {Y : Set X} (hY : IsOpen Y)
    (μ : X → ℝ) (a : MetricField) (hμ : ContDiffOn ℝ ∞ μ Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y) (hpos : ∀ x ∈ Y,μ x ≠ 0)
    {y : X} (hy : y ∈ Y) (i k l : I) (M B1 B2 B3 : ℝ) (hM : 0 ≤ M)
    (hn : |(μ y)⁻¹| ≤ M)
    (hn1 : ∀ j,|coordDeriv j (fun x => (μ x)⁻¹) y| ≤ M)
    (hn2 : ∀ j m,|coordDeriv j (coordDeriv m (fun x => (μ x)⁻¹)) y| ≤ M)
    (h1 : ∀ j,|coordDeriv j (fun x => μ x*a x i j) y| ≤ B1)
    (h2 : ∀ j m,|coordDeriv m (coordDeriv j (fun x => μ x*a x i j)) y| ≤ B2)
    (h3 : ∀ j m n,|coordDeriv n (coordDeriv m (coordDeriv j (fun x => μ x*a x i j))) y| ≤ B3) :
    |coordDeriv k (coordDeriv l (fun x => adjointFirstCoefficient (fun j => axis j) μ a x i)) y| ≤
      6*M*(B1+2*B2+B3) := by
  have hab (u t B : ℝ) (hu : |u| ≤ M) (ht : |t| ≤ 3*B) : |2*u*t| ≤ 2*M*(3*B) := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) ht (abs_nonneg _) (by positivity)
  rw [coordinate_second_adjointFirstCoefficient hY μ a hμ ha hpos hy i k l]
  have hA := hab _ _ B1 (hn2 k l) (abs_sum_three_le _ B1 h1)
  have hB := hab _ _ B2 (hn1 l) (abs_sum_three_le _ B2 (fun j => h2 j k))
  have hC := hab _ _ B2 (hn1 k) (abs_sum_three_le _ B2 (fun j => h2 j l))
  have hD := hab _ _ B3 hn (abs_sum_three_le _ B3 (fun j => h3 j l k))
  have hAbs (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
    linarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d]
  exact (hAbs _ _ _ _).trans (by linarith only [hA,hB,hC,hD])

/-- Local form of the supplied first derivative estimate for the zero coefficient. -/
lemma coordinate_adjointZeroCoefficient_bound {Y : Set X} (hY : IsOpen Y)
    (μ : X → ℝ) (a : MetricField) (hμ : ContDiffOn ℝ ∞ μ Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y) (hpos : ∀ x ∈ Y,μ x ≠ 0)
    {y : X} (hy : y ∈ Y) (k : I) (M B2 B3 : ℝ) (hM : 0 ≤ M)
    (hn : |(μ y)⁻¹| ≤ M) (hn1 : |coordDeriv k (fun x => (μ x)⁻¹) y| ≤ M)
    (h2 : ∀ i j,|coordDeriv j (coordDeriv i (fun x => μ x*a x i j)) y| ≤ B2)
    (h3 : ∀ i j,|coordDeriv k (coordDeriv j (coordDeriv i (fun x => μ x*a x i j))) y| ≤ B3) :
    |coordDeriv k (adjointZeroCoefficient (fun j => axis j) μ a) y| ≤ 9*M*(B2+B3) := by
  let b (x : X) := ∑ i,∑ j,coordDeriv j (coordDeriv i (fun x => μ x*a x i j)) x
  have hF (i j : I) := hμ.mul (ha i j)
  have hb : ContDiffOn ℝ ∞ b Y := ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY (hF i j) i) j))
  have hnSmooth : ContDiffOn ℝ ∞ (fun x => (μ x)⁻¹) Y := hμ.inv hpos
  have he : adjointZeroCoefficient (fun j => axis j) μ a = (fun x => (μ x)⁻¹*b x) := rfl
  have hDb : coordDeriv k b y = ∑ i,∑ j,coordDeriv k (coordDeriv j (coordDeriv i (fun x => μ x*a x i j))) y := by
    rw [show b = (fun x => ∑ i,∑ j,coordDeriv j (coordDeriv i (fun x => μ x*a x i j)) x) from rfl]
    rw [coordinate_sum hY _ (fun i => ContDiffOn.sum (fun j _ =>
      contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY (hF i j) i) j)) hy k]
    apply Finset.sum_congr rfl
    intro i _
    exact coordinate_sum hY _ (fun j => contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY (hF i j) i) j) hy k
  rw [he,coordinate_mul hY hnSmooth hb hy k,hDb]
  have hs2 := abs_sum_three_le _ (3*B2) (fun i => abs_sum_three_le _ B2 (h2 i))
  have hs3 := abs_sum_three_le _ (3*B3) (fun i => abs_sum_three_le _ B3 (h3 i))
  have hA : |coordDeriv k (fun x => (μ x)⁻¹) y*b y| ≤ M*(9*B2) := by
    rw [abs_mul]
    exact mul_le_mul hn1 (by change |∑ i,∑ j,coordDeriv j (coordDeriv i (fun x => μ x*a x i j)) y| ≤ _;linarith only [hs2]) (abs_nonneg _) hM
  have hB : |(μ y)⁻¹*(∑ i,∑ j,coordDeriv k (coordDeriv j (coordDeriv i (fun x => μ x*a x i j))) y)| ≤ M*(9*B3) := by
    rw [abs_mul]
    exact mul_le_mul hn (by linarith only [hs3]) (abs_nonneg _) hM
  exact (abs_add_le _ _).trans (by linarith only [hA,hB])

end ShrinkingSpheres
