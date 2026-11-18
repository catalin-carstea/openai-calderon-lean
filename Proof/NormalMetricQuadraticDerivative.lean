import Proof.MetricDifferentialTransport
import Proof.NormalSecondVariationTaylor
import Proof.NormalMetricSecondTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

def normalReferenceMetricDerivativeBudget (K C D E M1 M2 : ℝ) : ℝ :=
  72*M2*K+63*M1*normalVariationErrorBudget K C D+
    36*M1*K*(C+secondVelocityPrincipalErrorBudget K C D E)+
    36*K*secondVelocityPrincipalErrorBudget K C D E+18*K*C*normalVariationErrorBudget K C D

/-- The unscaled reference normal metric derivative gains one initial-speed
    factor. The angular scaling supplies the second radius factor downstream. -/
theorem NormalCoordinates.normal_metric_velocity_derivative_small {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K C D E M1 M2 : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hΓ0 : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ C)
    (hΓ1 : ∀ x ∈ Ω,‖fderiv ℝ (connectionBilinear g) x‖ ≤ D)
    (hΓ2 : ∀ x ∈ Ω,‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) x‖ ≤ E)
    (hDg : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M1)
    (hDg2 : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fderiv ℝ (fun z => g z i j)) x‖ ≤ M2)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y)
    (v u w a : X) (hv : v ∈ interior (disk g y (R y))) (hv1 : ‖v‖ ≤ 1)
    (hSmall : ‖normalVerticalJacobian expMap y v-ContinuousLinearMap.id ℝ X‖ ≤ 1) :
    |fderiv ℝ (fun z => metricPair g (expMap (y,z))
      (normalVerticalJacobian expMap y z u) (normalVerticalJacobian expMap y z w)) v a| ≤
      normalReferenceMetricDerivativeBudget K C D E M1 M2*‖v‖*‖a‖*‖u‖*‖w‖ := by
  let x := expMap (y,v)
  let J := normalVerticalJacobian expMap y v
  let DJ := fderiv ℝ (normalVerticalJacobian expMap y) v
  let G := connectionBilinear g y
  let B := normalVariationErrorBudget K C D
  let H := secondVelocityPrincipalErrorBudget K C D E
  let N := C+H
  have hyΩ := hN.center_mem hy
  have hx : x ∈ Ω := by
    simpa only [one_smul] using hN.path_image hy v (interior_subset hv)
      (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hB : 0 ≤ B := by dsimp [B,normalVariationErrorBudget];positivity
  have hH : 0 ≤ H := by dsimp [H,secondVelocityPrincipalErrorBudget,secondNormalVariationBudget,normalVariationErrorBudget];positivity
  have hN0 : 0 ≤ N := add_nonneg hC hH
  have hJn (b : X) : ‖J b‖ ≤ 2*‖b‖ := by
    have hDiff := ((J-ContinuousLinearMap.id ℝ X).le_opNorm b).trans
      (mul_le_mul_of_nonneg_right hSmall (norm_nonneg b))
    have ht : ‖J b‖ ≤ ‖J b-b‖+‖b‖ := by
      calc
        _ = ‖(J b-b)+b‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    change ‖J b-b‖ ≤ 1*‖b‖ at hDiff
    nlinarith only [ht,hDiff]
  have hJOp := hN.normalVerticalJacobian_sub_id_bound hΩ hg hK hC hD hΓ0 hΓ1 hy v hv hv1
  have hJError (b : X) : ‖J b-b‖ ≤ B*‖v‖*‖b‖ :=
    ((J-ContinuousLinearMap.id ℝ X).le_opNorm b).trans (mul_le_mul_of_nonneg_right hJOp (norm_nonneg b))
  have hGNorm : ‖G‖ ≤ C := hΓ0 y hyΩ
  have hGn (b c : X) : ‖G b c‖ ≤ C*‖b‖*‖c‖ :=
    (norm_bilinear_apply_le _ _ _).trans (by gcongr)
  have hDJOp := hN.normalVerticalJacobian_derivative_error hΩ hg hK hC hD hE hΓ0 hΓ1 hΓ2 hy v hv hv1
  have hDJError (b c : X) : ‖DJ b c+G b c‖ ≤ H*‖v‖*‖b‖*‖c‖ :=
    (norm_bilinear_apply_le (DJ+G) b c).trans (by gcongr)
  have hDJn (b c : X) : ‖DJ b c‖ ≤ N*‖b‖*‖c‖ := by
    have ht : ‖DJ b c‖ ≤ ‖DJ b c+G b c‖+‖G b c‖ := by
      calc
        _ = ‖(DJ b c+G b c)-G b c‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    have he := (hDJError b c).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv1 hH) (norm_nonneg b)) (norm_nonneg c))
    exact ht.trans ((add_le_add he (hGn b c)).trans_eq (by dsimp [N];ring))
  have hTrip : |metricDifferential g x (J a) (J u) (J w)-metricDifferential g y a u w| ≤
      (72*M2*K+63*M1*B)*‖v‖*‖a‖*‖u‖*‖w‖ := by
    let t1 := metricDifferential g x (J a) (J u) (J w)-metricDifferential g y (J a) (J u) (J w)
    let t2 := metricDifferential g y (J a-a) (J u) (J w)
    let t3 := metricDifferential g y a (J u-u) (J w)
    let t4 := metricDifferential g y a u (J w-w)
    have hEq : metricDifferential g x (J a) (J u) (J w)-metricDifferential g y a u w = t1+t2+t3+t4 := by
      dsimp [t1,t2,t3,t4]
      simp only [map_sub,_root_.sub_apply]
      ring
    have h1 : |t1| ≤ 72*M2*K*‖v‖*‖a‖*‖u‖*‖w‖ := by
      have hb := hN.metricDifferential_transport_bound hΩ hg hK hM2 hDg2 hy v (interior_subset hv) (J a) (J u) (J w)
      exact hb.trans ((show 9*M2*K*‖v‖*‖J a‖*‖J u‖*‖J w‖ ≤
        9*M2*K*‖v‖*(2*‖a‖)*(2*‖u‖)*(2*‖w‖) by gcongr;exact hJn a;exact hJn u;exact hJn w).trans_eq (by ring))
    have h2 : |t2| ≤ 36*M1*B*‖v‖*‖a‖*‖u‖*‖w‖ := by
      have hb := metricDifferential_abs_le g y M1 hM1 (hDg y hyΩ) (J a-a) (J u) (J w)
      exact hb.trans ((show 9*M1*‖J a-a‖*‖J u‖*‖J w‖ ≤
        9*M1*(B*‖v‖*‖a‖)*(2*‖u‖)*(2*‖w‖) by gcongr;exact hJError a;exact hJn u;exact hJn w).trans_eq (by ring))
    have h3 : |t3| ≤ 18*M1*B*‖v‖*‖a‖*‖u‖*‖w‖ := by
      have hb := metricDifferential_abs_le g y M1 hM1 (hDg y hyΩ) a (J u-u) (J w)
      exact hb.trans ((show 9*M1*‖a‖*‖J u-u‖*‖J w‖ ≤
        9*M1*‖a‖*(B*‖v‖*‖u‖)*(2*‖w‖) by gcongr;exact hJError u;exact hJn w).trans_eq (by ring))
    have h4 : |t4| ≤ 9*M1*B*‖v‖*‖a‖*‖u‖*‖w‖ := by
      have hb := metricDifferential_abs_le g y M1 hM1 (hDg y hyΩ) a u (J w-w)
      exact hb.trans ((mul_le_mul_of_nonneg_left (hJError w) (by positivity)).trans_eq (by ring))
    rw [hEq]
    exact (abs_add_le _ _).trans ((add_le_add
      ((abs_add_le _ _).trans ((add_le_add
        ((abs_add_le _ _).trans (add_le_add h1 h2)) h3))) h4).trans_eq (by ring))
  have hMetricDiff : ‖metricBilinear g x-metricBilinear g y‖ ≤ 9*M1*K*‖v‖ :=
    hN.metricBilinear_transport_bound hΩ hg hK hM1 hg.1 hDg hy v (interior_subset hv)
  have hBaseNorm : ‖metricBilinear g y‖ ≤ 9*K := metricBilinear_norm_of_entry_bound g y K (hg.entry_abs_bound hK hyΩ)
  have hBilinear (b c d : X) :
      |metricPair g x (DJ b c) (J d)-metricPair g y (-G b c) d| ≤
      (18*M1*K*N+18*K*H+9*K*C*B)*‖v‖*‖b‖*‖c‖*‖d‖ := by
    let L := metricBilinear g x
    let L0 := metricBilinear g y
    have hEq : L (DJ b c) (J d)-L0 (-G b c) d =
        (L-L0) (DJ b c) (J d)+L0 (DJ b c+G b c) (J d)+L0 (-G b c) (J d-d) := by
      simp only [ContinuousLinearMap.sub_apply,map_add,map_sub,map_neg,_root_.add_apply,_root_.neg_apply]
      ring
    have h1 : ‖(L-L0) (DJ b c) (J d)‖ ≤ 18*M1*K*N*‖v‖*‖b‖*‖c‖*‖d‖ := by
      calc
        _ ≤ ‖L-L0‖*‖DJ b c‖*‖J d‖ := norm_bilinear_form_apply_le _ _ _
        _ ≤ (9*M1*K*‖v‖)*(N*‖b‖*‖c‖)*(2*‖d‖) := by gcongr;exact hDJn b c;exact hJn d
        _ = _ := by ring
    have h2 : ‖L0 (DJ b c+G b c) (J d)‖ ≤ 18*K*H*‖v‖*‖b‖*‖c‖*‖d‖ := by
      calc
        _ ≤ ‖L0‖*‖DJ b c+G b c‖*‖J d‖ := norm_bilinear_form_apply_le _ _ _
        _ ≤ (9*K)*(H*‖v‖*‖b‖*‖c‖)*(2*‖d‖) := by gcongr;exact hDJError b c;exact hJn d
        _ = _ := by ring
    have h3 : ‖L0 (-G b c) (J d-d)‖ ≤ 9*K*C*B*‖v‖*‖b‖*‖c‖*‖d‖ := by
      calc
        _ ≤ ‖L0‖*‖-G b c‖*‖J d-d‖ := norm_bilinear_form_apply_le _ _ _
        _ = ‖L0‖*‖G b c‖*‖J d-d‖ := by rw [norm_neg]
        _ ≤ (9*K)*(C*‖b‖*‖c‖)*(B*‖v‖*‖d‖) := by gcongr;exact hGn b c;exact hJError d
        _ = _ := by ring
    have hFinal : ‖L (DJ b c) (J d)-L0 (-G b c) d‖ ≤
        (18*M1*K*N+18*K*H+9*K*C*B)*‖v‖*‖b‖*‖c‖*‖d‖ := by
      rw [hEq]
      exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3).trans_eq (by ring))
    simpa only [L,L0,metricBilinear_apply,Real.norm_eq_abs] using hFinal
  have hSecond := hBilinear a u w
  have hThird : |metricPair g x (J u) (DJ a w)-metricPair g y u (-G a w)| ≤
      (18*M1*K*N+18*K*H+9*K*C*B)*‖v‖*‖a‖*‖u‖*‖w‖ := by
    rw [metricPair_symm g x (J u) (DJ a w) (hg.2 x hx).1,
      metricPair_symm g y u (-G a w) (hg.2 y hyΩ).1]
    exact (hBilinear a w u).trans_eq (by ring)
  have hZero : metricDifferential g y a u w+metricPair g y (-G a u) w+metricPair g y u (-G a w) = 0 := by
    have hh := connection_metric hΩ hg hK hyΩ a u w
    have hNeg1 : metricPair g y (-G a u) w = -metricPair g y (connection g y a u) w := by
      rw [← metricBilinear_apply]
      simp only [G,ContinuousLinearMap.neg_apply,connectionBilinear_apply,map_neg,_root_.neg_apply,metricBilinear_apply]
    have hNeg2 : metricPair g y u (-G a w) = -metricPair g y u (connection g y a w) := by
      rw [← metricBilinear_apply]
      simp only [G,ContinuousLinearMap.neg_apply,connectionBilinear_apply,map_neg,_root_.neg_apply,metricBilinear_apply]
    rw [hNeg1,hNeg2]
    linarith only [hh]
  rw [hN.normal_metric_velocity_derivative hΩ hg hy v u w a (interior_subset hv)]
  change |metricDifferential g x (J a) (J u) (J w)+metricPair g x (DJ a u) (J w)+metricPair g x (J u) (DJ a w)| ≤ _
  have hEq : metricDifferential g x (J a) (J u) (J w)+metricPair g x (DJ a u) (J w)+metricPair g x (J u) (DJ a w) =
      (metricDifferential g x (J a) (J u) (J w)-metricDifferential g y a u w)+
      (metricPair g x (DJ a u) (J w)-metricPair g y (-G a u) w)+
      (metricPair g x (J u) (DJ a w)-metricPair g y u (-G a w)) := by linarith only [hZero]
  rw [hEq]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add hTrip hSecond)) hThird).trans_eq (by
      dsimp [normalReferenceMetricDerivativeBudget,N,H,B];ring))

end ShrinkingSpheres
