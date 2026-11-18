import Proof.CoordinateThirdProductBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma coordinate_mul {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y) (i : I) :
    coordDeriv i (fun x => f x*g x) y = coordDeriv i f y*g y+f y*coordDeriv i g y := by
  change fderiv ℝ (fun x => f x*g x) y (axis i) = _
  rw [(((hf.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.fun_mul
    ((hg.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt).fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,coordDeriv]
  ring

/-- All orders up to three in the supplied scalar product estimate, now local
on the actual open coordinate domain. -/
lemma CoordinateScalarThreeJetBound.mul {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : CoordinateScalarThreeJetBound f y A) (hG : CoordinateScalarThreeJetBound g y B) :
    CoordinateScalarThreeJetBound (fun x => f x*g x) y (8*A*B) := by
  have hAB : 0 ≤ A*B := mul_nonneg hA hB
  have hab (u v : ℝ) (hu : |u| ≤ A) (hv : |v| ≤ B) : |u*v| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hA
  constructor
  · exact (hab _ _ hF.value hG.value).trans (by nlinarith only [hAB])
  · intro i
    rw [coordinate_mul hY hf hg hy i]
    exact (abs_add_le _ _).trans (by linarith only [hab _ _ (hF.first i) hG.value,hab _ _ hF.value (hG.first i),hAB])
  · intro i j
    rw [coordinate_second_mul hY hf hg hy i j]
    have h1 := hab _ _ (hF.second i j) hG.value
    have h2 := hab _ _ (hF.first j) (hG.first i)
    have h3 := hab _ _ (hF.first i) (hG.first j)
    have h4 := hab _ _ hF.value (hG.second i j)
    have hAbs (a b c d : ℝ) : |a+b+c+d| ≤ |a|+|b|+|c|+|d| := by
      linarith [abs_add_le a b,abs_add_le (a+b) c,abs_add_le (a+b+c) d]
    exact (hAbs _ _ _ _).trans (by linarith only [h1,h2,h3,h4,hAB])
  · exact hF.mul_third_bound hY hf hg hy hA hB hG

end ShrinkingSpheres
