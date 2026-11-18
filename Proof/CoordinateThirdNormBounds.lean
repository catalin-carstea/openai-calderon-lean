import Proof.ProfileLogCovectorHigherJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma norm_trilinear_le_of_axis_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : X →L[ℝ] X →L[ℝ] X →L[ℝ] E) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ i j k,‖L (axis i) (axis j) (axis k)‖ ≤ C) : ‖L‖ ≤ 27*C := by
  have hh := norm_bilinear_le_of_axis_bound L (3*C) (by positivity) (fun i j =>
    norm_linear_le_of_axis_bound (L (axis i) (axis j)) C hC (hL i j))
  exact hh.trans_eq (by ring)

lemma coordinate_third_derivative {Y : Set X} (hY : IsOpen Y) (f : X → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y) {y : X} (hy : y ∈ Y) (i j k : I) :
    coordDeriv i (coordDeriv j (coordDeriv k f)) y =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) y (axis i) (axis j) (axis k) := by
  have hF : ContDiffOn ℝ ∞ (fderiv ℝ f) Y := hf.fderiv_of_isOpen (m:=∞) hY (by simp)
  have hFF : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ f)) Y := hF.fderiv_of_isOpen (m:=∞) hY (by simp)
  have hEq : coordDeriv j (coordDeriv k f) =ᶠ[𝓝 y]
      (fun x => fderiv ℝ (fderiv ℝ f) x (axis j) (axis k)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact coordinate_second_derivative f x ((hF.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)) j k
  have hD := ((hFF.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have h1 := hD.clm_apply (hasFDerivAt_const (𝕜:=ℝ) (axis j) y)
  have h2 := h1.clm_apply (hasFDerivAt_const (𝕜:=ℝ) (axis k) y)
  have hh := congrArg (fun A : X →L[ℝ] ℝ => A (axis i)) h2.fderiv
  change fderiv ℝ (coordDeriv j (coordDeriv k f)) y (axis i) = _
  rw [hEq.fderiv_eq]
  simpa only [_root_.add_apply,ContinuousLinearMap.comp_apply,zero_apply,map_zero,
    add_zero,zero_add,ContinuousLinearMap.flip_apply] using hh
end ShrinkingSpheres
