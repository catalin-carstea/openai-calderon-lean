import Proof.NormalJacobiError
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

/-- Quantitative closeness to the identity of the actual vertical normal Jacobian. -/
theorem NormalCoordinates.normalVerticalJacobian_sub_id_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1) :
    ‖normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ X‖ ≤
      normalVariationErrorBudget K C D*‖v‖ := by
  have hB : 0 ≤ normalVariationErrorBudget K C D := by unfold normalVariationErrorBudget; positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg v))
  intro u
  have ht : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have herr := hN.position_variation_error_le hΩ hg hK hC hD hΓ0 hΓ1 hy v u hv hv1 ht
  have hvd : (1:ℝ) • v ∈ disk g y (R y) := by simpa only [one_smul] using interior_subset hv
  have he := hN.variation_position_eq hy v u 1 hvd
  simp only [one_smul] at he
  rw [he] at herr
  change ‖normalVerticalJacobian expMap y v u-u‖ ≤ _
  simpa only [one_smul,one_pow,mul_one] using herr

lemma NormalCoordinates.normalVerticalJacobian_isInvertible {Y Ω : Set X} {g : MetricField}
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y)) : (normalVerticalJacobian expMap y v).IsInvertible := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,v)) (y,v) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp)).hasFDerivAt
  have hSlice : HasFDerivAt (fun w : X => (y,w)) (ContinuousLinearMap.inr ℝ X X) v :=
    (hasFDerivAt_const (𝕜:=ℝ) y v).prodMk (hasFDerivAt_id v)
  have hd : HasFDerivAt (fun w : X => expMap (y,w)) (normalVerticalJacobian expMap y v) v := by
    exact hE.comp v hSlice
  have hBij := ((hN.2 y hy).2.2 v hv).2.1
  rw [hd.fderiv] at hBij
  refine ⟨(LinearEquiv.ofBijective (normalVerticalJacobian expMap y v).toLinearMap hBij).toContinuousLinearEquiv,?_⟩
  ext w
  rfl

lemma inverse_norm_le_two_of_half_sub_id (L : X →L[ℝ] X) (hL : L.IsInvertible)
    (hSmall : ‖L-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ)) : ‖L.inverse‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  let x := L.inverse y
  have hDiff : ‖L x-x‖ ≤ (1/2:ℝ)*‖x‖ := by
    have hd := (L-ContinuousLinearMap.id ℝ X).le_opNorm x
    change ‖L x-x‖ ≤ ‖L-ContinuousLinearMap.id ℝ X‖*‖x‖ at hd
    exact hd.trans (mul_le_mul_of_nonneg_right hSmall (norm_nonneg x))
  have hTri : ‖x‖ ≤ ‖L x‖+‖L x-x‖ := by
    calc
      ‖x‖ = ‖L x-(L x-x)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hEval : L x = y := hL.self_apply_inverse y
  rw [hEval] at hTri hDiff
  change ‖x‖ ≤ 2*‖y‖
  nlinarith only [hTri,hDiff]

/-- Uniform inverse bound on a quantitatively small admitted normal ball. -/
theorem NormalCoordinates.normalVerticalJacobian_inverse_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    (hSmall : normalVariationErrorBudget K C D*‖v‖ ≤ (1/2:ℝ)) :
    ‖(normalVerticalJacobian expMap y v).inverse‖ ≤ 2 :=
  inverse_norm_le_two_of_half_sub_id _ (hN.normalVerticalJacobian_isInvertible hy v (interior_subset hv))
    ((hN.normalVerticalJacobian_sub_id_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v hv hv1).trans hSmall)

end ShrinkingSpheres
