import Proof.CoordinateProductThreeJetAlgebra
import Proof.CoordinateFiniteSumCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy

/-- Values and two ordinary scalar jets at the same point and beta scale. -/
structure ScalarTwoJetBound (f : X → ℝ) (y : X) (β t : ℝ) : Prop where
  value : |f y| ≤ t
  first : ∀ i : I,|coordDeriv i f y| ≤ t*β
  second : ∀ i j : I,|coordDeriv j (coordDeriv i f) y| ≤ t*β^2

lemma ScalarTwoJetBound.mono {f : X → ℝ} {y : X} {β s t : ℝ}
    (h : ScalarTwoJetBound f y β s) (hβ : 0 ≤ β) (hst : s ≤ t) :
    ScalarTwoJetBound f y β t :=
  ⟨h.value.trans hst,fun i => (h.first i).trans (mul_le_mul_of_nonneg_right hst hβ),
    fun i j => (h.second i j).trans (mul_le_mul_of_nonneg_right hst (sq_nonneg β))⟩

lemma scalarTwoJetBound_zero (y : X) (β : ℝ) : ScalarTwoJetBound (fun _ : X => (0:ℝ)) y β 0 := by
  have hD (i : I) : coordDeriv i (fun _ : X => (0:ℝ)) = fun _ => (0:ℝ) := by
    funext x
    simp [coordDeriv]
  constructor <;> intros <;> simp only [hD,abs_zero,mul_zero,zero_mul,le_refl]

lemma ScalarTwoJetBound.mul {Y : Set X} (hY : IsOpen Y) {f g : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) (hg : ContDiffOn ℝ ∞ g Y) {y : X} (hy : y ∈ Y)
    {β s t : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hF : ScalarTwoJetBound f y β s) (hG : ScalarTwoJetBound g y β t) :
    ScalarTwoJetBound (fun x => f x*g x) y β (4*s*t) := by
  have h0 : |f y*g y| ≤ s*t := by
    rw [abs_mul]
    exact mul_le_mul hF.value hG.value (abs_nonneg _) hs
  have hMul {u v A B : ℝ} (hA : 0 ≤ A) (hu : |u| ≤ A) (hv : |v| ≤ B) :
      |u*v| ≤ A*B := by
    rw [abs_mul]
    exact mul_le_mul hu hv (abs_nonneg _) hA
  constructor
  · exact h0.trans (by nlinarith only [mul_nonneg hs ht])
  · intro i
    rw [coordinate_mul hY hf hg hy i]
    have h1 := hMul (mul_nonneg hs hβ) (hF.first i) hG.value
    have h2 := hMul hs hF.value (hG.first i)
    exact ((abs_add_le _ _).trans (add_le_add h1 h2)).trans
      (by nlinarith only [mul_nonneg (mul_nonneg hs ht) hβ])
  · intro i j
    rw [coordinate_second_mul hY hf hg hy j i]
    have h1 := hMul (mul_nonneg hs (sq_nonneg β)) (hF.second i j) hG.value
    have h2 := hMul (mul_nonneg hs hβ) (hF.first i) (hG.first j)
    have h3 := hMul (mul_nonneg hs hβ) (hF.first j) (hG.first i)
    have h4 := hMul hs hF.value (hG.second i j)
    exact ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)).trans
        ((add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans_eq (by ring))

lemma ScalarTwoJetBound.const_mul {Y : Set X} (hY : IsOpen Y) {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) {β t : ℝ}
    (hF : ScalarTwoJetBound f y β t) (c : ℝ) :
    ScalarTwoJetBound (fun x => c*f x) y β (|c| *t) := by
  have hc (i : I) : coordDeriv i (fun _ : X => c) = fun _ => (0:ℝ) := by
    funext x
    simp [coordDeriv]
  have hz (i : I) : coordDeriv i (fun _ : X => (0:ℝ)) = fun _ => (0:ℝ) := by
    funext x
    simp [coordDeriv]
  constructor
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hF.value (abs_nonneg c)
  · intro i
    rw [coordinate_mul hY contDiffOn_const hf hy i]
    simp only [hc,zero_mul,zero_add,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hF.first i) (abs_nonneg c)).trans_eq (by ring)
  · intro i j
    rw [coordinate_second_mul hY contDiffOn_const hf hy j i]
    simp only [hc,hz,zero_mul,zero_add,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hF.second i j) (abs_nonneg c)).trans_eq (by ring)

lemma ScalarTwoJetBound.sum {Y : Set X} (hY : IsOpen Y) {ι : Type*} [Fintype ι]
    (f : ι → X → ℝ) (hf : ∀ a,ContDiffOn ℝ ∞ (f a) Y)
    {y : X} (hy : y ∈ Y) {β : ℝ} (t : ι → ℝ)
    (hF : ∀ a,ScalarTwoJetBound (f a) y β (t a)) :
    ScalarTwoJetBound (fun x => ∑ a,f a x) y β (∑ a,t a) := by
  constructor
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a _ => (hF a).value))
  · intro i
    rw [coordinate_sum hY f hf hy i]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun a _ => (hF a).first i)).trans_eq
      (Finset.sum_mul _ _ _).symm)
  · intro i j
    rw [coordinate_second_sum hY f hf hy j i]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun a _ => (hF a).second i j)).trans_eq
      (Finset.sum_mul _ _ _).symm)

end ShrinkingSpheres.ParallelEnergy
