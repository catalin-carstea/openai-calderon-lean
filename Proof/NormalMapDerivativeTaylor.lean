import Proof.NormalMapSecondTaylor
import Proof.NormalJacobianInverse
import Proof.NormalMetricDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- First derivative Taylor control for an actual normal composition. The
    background derivative is transported along its geodesic, so no coordinate
    convexity or uniform frame derivative bound is needed. -/
theorem NormalCoordinates.map_derivative_taylor_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y Ω : Set X} (hΩ : IsOpen Ω) {K M1 M2 A B : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (F : X → E) (hSmooth : ContDiffOn ℝ ∞ F Ω)
    (hDF : ∀ x ∈ Ω,‖fderiv ℝ F x‖ ≤ M1)
    (hDDF : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ F) x‖ ≤ M2)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk g y (R y))
    (hJn : ‖normalVerticalJacobian expMap y v‖ ≤ A)
    (hJerr : ‖normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ X‖ ≤ B*‖v‖) :
    ‖fderiv ℝ (fun w => F (expMap (y,w))) v-fderiv ℝ F y‖ ≤
      (M2*K*A+M1*B)*‖v‖ := by
  let J := normalVerticalJacobian expMap y v
  let D := fderiv ℝ F
  have hDerr : ‖D (expMap (y,v))-D y‖ ≤ M2*K*‖v‖ := by
    have hb := hN.map_transport_bound hΩ hg hK hM2 D
      (hSmooth.fderiv_of_isOpen (m:=∞) hΩ (by simp)) hDDF hy v hv
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
    simpa only [one_smul,mul_one] using hb
  have hFx := (hSmooth.contDiffAt (hΩ.mem_nhds ((hN.2 y hy).2.2 v hv).1)).differentiableAt (by simp)
  have hComp : HasFDerivAt (fun w => F (expMap (y,w)))
      ((D (expMap (y,v))).comp J) v :=
    hFx.hasFDerivAt.comp v (hN.hasFDerivAt_velocity_slice hy v hv)
  rw [hComp.fderiv]
  have hEq : (D (expMap (y,v))).comp J-D y =
      (D (expMap (y,v))-D y).comp J+(D y).comp (J-ContinuousLinearMap.id ℝ X) := by
    rw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_id]
    abel
  change ‖(D (expMap (y,v))).comp J-D y‖ ≤ _
  rw [hEq]
  calc
    _ ≤ ‖(D (expMap (y,v))-D y).comp J‖+‖(D y).comp (J-ContinuousLinearMap.id ℝ X)‖ := norm_add_le _ _
    _ ≤ ‖D (expMap (y,v))-D y‖*‖J‖+‖D y‖*‖J-ContinuousLinearMap.id ℝ X‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (M2*K*‖v‖)*A+M1*(B*‖v‖) := by
      gcongr
      exact hDF y (hN.center_mem hy)
    _ = _ := by ring

end ShrinkingSpheres
