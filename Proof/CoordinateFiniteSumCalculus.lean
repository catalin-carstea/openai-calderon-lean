import Proof.CoordinateSecondJetCalculus

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma coordinate_sum {A : Type*} [Fintype A] {Y : Set X} (hY : IsOpen Y) (f : A → X → ℝ)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) Y) {y : X} (hy : y ∈ Y) (i : I) :
    coordDeriv i (fun x => ∑ a,f a x) y = ∑ a,coordDeriv i (f a) y := by
  have hs := HasFDerivAt.fun_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) =>
    ((hf a).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp) |>.hasFDerivAt)
  change (fderiv ℝ (fun x => ∑ a,f a x) y) (axis i) = _
  rw [hs.fderiv]
  simp only [sum_apply,coordDeriv]

lemma coordinate_second_sum {A : Type*} [Fintype A] {Y : Set X} (hY : IsOpen Y) (f : A → X → ℝ)
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) Y) {y : X} (hy : y ∈ Y) (i j : I) :
    coordDeriv i (coordDeriv j (fun x => ∑ a,f a x)) y =
      ∑ a,coordDeriv i (coordDeriv j (f a)) y := by
  have he : coordDeriv j (fun x => ∑ a,f a x) =ᶠ[𝓝 y] (fun x => ∑ a,coordDeriv j (f a) x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_sum hY f hf hx j
  change fderiv ℝ (coordDeriv j (fun x => ∑ a,f a x)) y (axis i) = _
  rw [he.fderiv_eq]
  exact coordinate_sum hY (fun a => coordDeriv j (f a))
    (fun a => contDiffOn_coordDeriv hY (hf a) j) hy i

end ShrinkingSpheres
