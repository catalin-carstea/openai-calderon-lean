import Proof.ScaledTwoJetProductBounds
import Proof.CoordinateScalarFirstRules
import Proof.SmoothFiniteJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma SmoothFiniteJetBound.coordinate_two_jets {f : X → ℝ} {y : X} {N : ℕ} {C : ℝ}
    (h : SmoothFiniteJetBound f y N C) (hN : 2 ≤ N) (i j : I) :
    |f y| ≤ C ∧ |coordDeriv i f y| ≤ C ∧ |coordDeriv j (coordDeriv i f) y| ≤ C := by
  have h0 := h.bound 0 (by omega)
  have h1 := h.bound 1 (by omega)
  have h2 := h.bound 2 hN
  rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h0
  rw [norm_iteratedFDeriv_one] at h1
  rw [norm_iteratedFDeriv_two_eq_nested] at h2
  have hd : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (h.smooth.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  refine ⟨h0,(coordDeriv_abs_le f y i).trans h1,?_⟩
  rw [coordinate_second_derivative f y hd j i]
  have hh := (((fderiv ℝ (fderiv ℝ f) y (axis j)).le_opNorm (axis i))).trans
    (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ f) y).le_opNorm (axis j)) (norm_nonneg _))
  simp only [norm_axis,mul_one,Real.norm_eq_abs] at hh
  exact hh.trans h2

/-- A sharp small scalar coefficient times a bounded background scalar
retains the same zero/first/second beta weights. The product estimate is
the SAME shared normed-space derivation used by coarse operator callers. -/
lemma small_scalar_two_jet_product_bounds {Y : Set X} (hY : IsOpen Y)
    (f g : X → ℝ) (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y)
    {y : X} (hy : y ∈ Y) (i j : I) (B G ε β : ℝ)
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (hf0 : |f y| ≤ B*ε/β^2) (hf1 : ∀ k,|coordDeriv k f y| ≤ B*ε/β)
    (hf2 : |coordDeriv j (coordDeriv i f) y| ≤ B*ε)
    (hg0 : |g y| ≤ G) (hg1 : ∀ k,|coordDeriv k g y| ≤ G)
    (hg2 : |coordDeriv j (coordDeriv i g) y| ≤ G) :
    |f y*g y| ≤ B*G*ε/β^2 ∧
      |coordDeriv i (fun x => f x*g x) y| ≤ 2*B*G*ε/β ∧
      |coordDeriv j (coordDeriv i (fun x => f x*g x)) y| ≤ 4*B*G*ε := by
  have hβ0 := zero_lt_one.trans_le hβ
  have hGrow (k : I) : |coordDeriv k g y| ≤ G*β :=
    (hg1 k).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ hG)
  have hGrow2 : |coordDeriv j (coordDeriv i g) y| ≤ G*β^2 :=
    hg2.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hβ : 1 ≤ β^2) hG)
  have hProduct := scaled_two_jet_product_bounds
    (g y) (coordDeriv i g y) (coordDeriv j g y) (coordDeriv j (coordDeriv i g) y)
    (f y) (coordDeriv i f y) (coordDeriv j f y) (coordDeriv j (coordDeriv i f) y)
    B G ε β hB hε hβ0 hf0 (hf1 i) (hf1 j) hf2
    (by simpa only [Real.norm_eq_abs] using hg0)
    (by simpa only [Real.norm_eq_abs] using hGrow i)
    (by simpa only [Real.norm_eq_abs] using hGrow j)
    (by simpa only [Real.norm_eq_abs] using hGrow2)
  simp only [Real.norm_eq_abs,smul_eq_mul] at hProduct
  have hDF := (hf.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hDG := (hg.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  refine ⟨hProduct.1,?_,?_⟩
  · rw [coordDeriv_mul_at f g hDF hDG i,add_comm]
    exact hProduct.2.1
  · rw [coordinate_second_mul hY hf hg hy j i]
    convert hProduct.2.2 using 1 <;> congr 1 <;> ring

end ShrinkingSpheres
