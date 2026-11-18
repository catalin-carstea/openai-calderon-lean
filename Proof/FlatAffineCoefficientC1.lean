import Proof.NormalizedStrongTaylorPointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

lemma flat_compact_coefficient_local_jets (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1) :
    (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F0 i j) z| ≤ 1) ∧
    (∀ i j,∀ z ∈ (ballOpens:Set X),fderiv ℝ (coefficientValue 2 (F0 i j)) z = 0) := by
  have hG (i j : I) (z : X) (hz : z ∈ (ballOpens:Set X)) :
      coefficientValue 2 (F0 i j) =ᶠ[𝓝 z] (fun _ : X => (1:Mat) i j) := by
    filter_upwards [ballOpens.isOpen.mem_nhds hz] with w hw
    exact congrArg (fun A : Mat => A i j) (hFlat w hw)
  constructor
  · intro i j z hz
    rw [(hG i j z hz).eq_of_nhds]
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  · intro i j z hz
    exact (hG i j z hz).fderiv_eq.trans (hasFDerivAt_const (𝕜:=ℝ) ((1:Mat) i j) z).fderiv

/-- Full local C1 coefficient size follows from the same flat affine
Taylor bounds; exterior cutoff derivatives do not enter. -/
theorem coefficient_local_C1_of_flat_affine
    (F F0 F1 : SmoothCoefficientMatrix 2) (r P Q : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hVal1 : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F1 i j) z| ≤ P)
    (hDer1 : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ P)
    (hValR : ∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 ((F-F0-r • F1) i j) z| ≤ Q*r^2)
    (hDerR : ∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 ((F-F0-r • F1) i j)) z‖ ≤ Q*r^2) :
    (∀ i j,∀ z ∈ (ballOpens:Set X),|coefficientValue 2 (F i j) z| ≤ 1+P+Q) ∧
    (∀ i j,∀ z ∈ (ballOpens:Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) z‖ ≤ 1+P+Q) := by
  let R := F-F0-r • F1
  obtain ⟨hVal0,hDer0⟩ := flat_compact_coefficient_local_jets F0 hFlat
  have hFun (i j : I) : coefficientValue 2 (F i j) =
      (fun w => coefficientValue 2 (R i j) w+coefficientValue 2 (F0 i j) w+r*coefficientValue 2 (F1 i j) w) := by
    funext w
    dsimp only [R]
    simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul,smul_eq_mul]
    ring
  have hNum : Q*r^2+1+r*P ≤ 1+P+Q := by
    have hr2 : r^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hr2 hQ,mul_le_mul_of_nonneg_right hr1 hP]
  constructor
  · intro i j z hz
    rw [hFun]
    exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      ((add_le_add (add_le_add (hValR i j z hz) (hVal0 i j z hz))
        (by rw [abs_mul,abs_of_nonneg hr];exact mul_le_mul_of_nonneg_left (hVal1 i j z hz) hr)).trans hNum)
  · intro i j z hz
    have hD := (((contDiff_coefficientValue 2 (R i j)).differentiable (by simp) z).hasFDerivAt.add
      ((contDiff_coefficientValue 2 (F0 i j)).differentiable (by simp) z).hasFDerivAt).add
      (((contDiff_coefficientValue 2 (F1 i j)).differentiable (by simp) z).hasFDerivAt.const_mul r)
    change HasFDerivAt (fun w => coefficientValue 2 (R i j) w+coefficientValue 2 (F0 i j) w+r*coefficientValue 2 (F1 i j) w) _ z at hD
    rw [hFun,hD.fderiv,hDer0 i j z hz,add_zero]
    have hB : ‖fderiv ℝ (coefficientValue 2 (R i j)) z+r • fderiv ℝ (coefficientValue 2 (F1 i j)) z‖ ≤ Q*r^2+r*P := by
      exact (norm_add_le _ _).trans (add_le_add (hDerR i j z hz)
        (by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr];exact mul_le_mul_of_nonneg_left (hDer1 i j z hz) hr))
    exact hB.trans (by linarith)

end ShrinkingSpheres
