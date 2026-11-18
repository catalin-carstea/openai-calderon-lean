import Proof.LocalScalarAdjointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

/-- Local-coordinate form of the supplied first-adjoint derivative algebra. -/
lemma coordinate_adjointFirstCoefficient {Y : Set X} (hY : IsOpen Y)
    (μ : X → ℝ) (a : MetricField) (hμ : ContDiffOn ℝ ∞ μ Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y) (hpos : ∀ x ∈ Y,μ x ≠ 0)
    {y : X} (hy : y ∈ Y) (i k : I) :
    coordDeriv k (fun x => adjointFirstCoefficient (fun j => axis j) μ a x i) y =
      2*coordDeriv k (fun x => (μ x)⁻¹) y*(∑ j,coordDeriv j (fun x => μ x*a x i j) y)+
      2*(μ y)⁻¹*(∑ j,coordDeriv k (coordDeriv j (fun x => μ x*a x i j)) y) := by
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
  rw [he,coordinate_const_mul hY (hn.mul hb) hy 2 k,coordinate_mul hY hn hb hy k]
  have hs : coordDeriv k b y = ∑ j,coordDeriv k (coordDeriv j (F j)) y :=
    coordinate_sum hY _ (fun j => contDiffOn_coordDeriv hY (hF j) j) hy k
  rw [hs]
  dsimp only [b,F]
  ring

lemma coordinate_adjointFirstCoefficient_bound {Y : Set X} (hY : IsOpen Y)
    (μ : X → ℝ) (a : MetricField) (hμ : ContDiffOn ℝ ∞ μ Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y) (hpos : ∀ x ∈ Y,μ x ≠ 0)
    {y : X} (hy : y ∈ Y) (i k : I) (M B1 B2 : ℝ) (hM : 0 ≤ M)
    (hn : |(μ y)⁻¹| ≤ M) (hn1 : |coordDeriv k (fun x => (μ x)⁻¹) y| ≤ M)
    (h1 : ∀ j,|coordDeriv j (fun x => μ x*a x i j) y| ≤ B1)
    (h2 : ∀ j,|coordDeriv k (coordDeriv j (fun x => μ x*a x i j)) y| ≤ B2) :
    |coordDeriv k (fun x => adjointFirstCoefficient (fun j => axis j) μ a x i) y| ≤ 6*M*(B1+B2) := by
  have hab (u t B : ℝ) (hu : |u| ≤ M) (ht : |t| ≤ 3*B) : |2*u*t| ≤ 2*M*(3*B) := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) ht (abs_nonneg _) (by positivity)
  rw [coordinate_adjointFirstCoefficient hY μ a hμ ha hpos hy i k]
  have hA := hab _ _ B1 hn1 (abs_sum_three_le _ B1 h1)
  have hB := hab _ _ B2 hn (abs_sum_three_le _ B2 h2)
  exact (abs_add_le _ _).trans (by linarith only [hA,hB])

end ShrinkingSpheres
