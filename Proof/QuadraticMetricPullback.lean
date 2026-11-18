import Proof.NormalMetricCloseness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres

lemma norm_bilinear_form_apply_le (L : X →L[ℝ] X →L[ℝ] ℝ) (u v : X) :
    ‖L u v‖ ≤ ‖L‖*‖u‖*‖v‖ :=
  ((L u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (L.le_opNorm u) (norm_nonneg v))

/-- Metric compatibility cancels the first-order metric and Jacobian jets in a
    pullback. Only explicit Taylor remainder bounds are used quantitatively. -/
theorem norm_metric_pullback_quadratic_le
    (L L0 L1 : X →L[ℝ] X →L[ℝ] ℝ) (J G : X →L[ℝ] X)
    (s S0 S1 C EJ EL : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hS0 : 0 ≤ S0) (hS1 : 0 ≤ S1) (hC : 0 ≤ C) (hEJ : 0 ≤ EJ) (hEL : 0 ≤ EL)
    (hL0 : ‖L0‖ ≤ S0) (hL1 : ‖L1‖ ≤ S1*s) (hJ : ‖J‖ ≤ 2) (hG : ‖G‖ ≤ C*s)
    (hJError : ‖J-(ContinuousLinearMap.id ℝ X-G)‖ ≤ EJ*s^2)
    (hLError : ‖L-L0-L1‖ ≤ EL*s^2)
    (hCompat : ∀ u v,L1 u v = L0 (G u) v+L0 u (G v)) (u v : X) :
    ‖L (J u) (J v)-L0 u v‖ ≤
      (4*EL+(S0+S1)*EJ*(3+C)+S0*C^2+S1*(2*C+C^2))*s^2*‖u‖*‖v‖ := by
  let B := L0+L1
  let J0 := ContinuousLinearMap.id ℝ X-G
  have hBNorm : ‖B‖ ≤ S0+S1 :=
    (norm_add_le _ _).trans (add_le_add hL0 (hL1.trans
      ((mul_le_mul_of_nonneg_left hs1 hS1).trans_eq (mul_one _))))
  have hGn (w : X) : ‖G w‖ ≤ C*s*‖w‖ :=
    (G.le_opNorm w).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg w))
  have hJn (w : X) : ‖J w‖ ≤ 2*‖w‖ :=
    (J.le_opNorm w).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg w))
  have hJ0n (w : X) : ‖J0 w‖ ≤ (1+C)*‖w‖ := by
    change ‖w-G w‖ ≤ _
    have hb := (hGn w).trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hs1 hC).trans_eq (mul_one _)) (norm_nonneg w))
    exact (norm_sub_le _ _).trans ((add_le_add le_rfl hb).trans_eq (by ring))
  have hEn (w : X) : ‖J w-J0 w‖ ≤ EJ*s^2*‖w‖ :=
    ((J-J0).le_opNorm w).trans (mul_le_mul_of_nonneg_right hJError (norm_nonneg w))
  have hFirst : ‖L (J u) (J v)-B (J u) (J v)‖ ≤ 4*EL*s^2*‖u‖*‖v‖ := by
    have hEq : L (J u) (J v)-B (J u) (J v) = (L-L0-L1) (J u) (J v) := by
      dsimp [B];simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply];ring
    rw [hEq]
    calc
      _ ≤ ‖L-L0-L1‖*‖J u‖*‖J v‖ := norm_bilinear_form_apply_le _ _ _
      _ ≤ (EL*s^2)*(2*‖u‖)*(2*‖v‖) := by gcongr;exact hJn u;exact hJn v
      _ = _ := by ring
  have hMiddle : ‖B (J u) (J v)-B (J0 u) (J0 v)‖ ≤
      (S0+S1)*EJ*(3+C)*s^2*‖u‖*‖v‖ := by
    have hEq : B (J u) (J v)-B (J0 u) (J0 v) =
        B (J u-J0 u) (J v)+B (J0 u) (J v-J0 v) := by
      simp only [map_sub,_root_.sub_apply];ring
    rw [hEq]
    have h1 : ‖B (J u-J0 u) (J v)‖ ≤ (S0+S1)*(EJ*s^2*‖u‖)*(2*‖v‖) :=
      (norm_bilinear_form_apply_le _ _ _).trans (by gcongr;exact hEn u;exact hJn v)
    have h2 : ‖B (J0 u) (J v-J0 v)‖ ≤ (S0+S1)*((1+C)*‖u‖)*(EJ*s^2*‖v‖) :=
      (norm_bilinear_form_apply_le _ _ _).trans (by gcongr;exact hJ0n u;exact hEn v)
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hLast : ‖B (J0 u) (J0 v)-L0 u v‖ ≤
      (S0*C^2+S1*(2*C+C^2))*s^2*‖u‖*‖v‖ := by
    have hEq : B (J0 u) (J0 v)-L0 u v =
        L0 (G u) (G v)-L1 (G u) v-L1 u (G v)+L1 (G u) (G v) := by
      simp only [B,J0,ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,
        ContinuousLinearMap.add_apply,map_sub,_root_.sub_apply]
      rw [hCompat u v]
      ring
    have h1 : ‖L0 (G u) (G v)‖ ≤ S0*C^2*s^2*‖u‖*‖v‖ := by
      calc
        _ ≤ ‖L0‖*‖G u‖*‖G v‖ := norm_bilinear_form_apply_le _ _ _
        _ ≤ S0*(C*s*‖u‖)*(C*s*‖v‖) := by gcongr;exact hGn u;exact hGn v
        _ = _ := by ring
    have h2 : ‖L1 (G u) v‖ ≤ S1*C*s^2*‖u‖*‖v‖ := by
      calc
        _ ≤ ‖L1‖*‖G u‖*‖v‖ := norm_bilinear_form_apply_le _ _ _
        _ ≤ (S1*s)*(C*s*‖u‖)*‖v‖ := by gcongr;exact hGn u
        _ = _ := by ring
    have h3 : ‖L1 u (G v)‖ ≤ S1*C*s^2*‖u‖*‖v‖ := by
      calc
        _ ≤ ‖L1‖*‖u‖*‖G v‖ := norm_bilinear_form_apply_le _ _ _
        _ ≤ (S1*s)*‖u‖*(C*s*‖v‖) := by gcongr;exact hGn v
        _ = _ := by ring
    have h4 : ‖L1 (G u) (G v)‖ ≤ S1*C^2*s^2*‖u‖*‖v‖ := by
      calc
        _ ≤ ‖L1‖*‖G u‖*‖G v‖ := norm_bilinear_form_apply_le _ _ _
        _ ≤ (S1*s)*(C*s*‖u‖)*(C*s*‖v‖) := by gcongr;exact hGn u;exact hGn v
        _ = (S1*C^2*s^2*‖u‖*‖v‖)*s := by ring
        _ ≤ S1*C^2*s^2*‖u‖*‖v‖ :=
          (mul_le_mul_of_nonneg_left hs1 (by positivity)).trans_eq (mul_one _)
    rw [hEq]
    have hb := norm_add_le (L0 (G u) (G v)-L1 (G u) v-L1 u (G v)) (L1 (G u) (G v))
    have hb2 := norm_sub_le (L0 (G u) (G v)-L1 (G u) v) (L1 u (G v))
    have hb3 := norm_sub_le (L0 (G u) (G v)) (L1 (G u) v)
    nlinarith only [hb,hb2,hb3,h1,h2,h3,h4]
  have hSplit : L (J u) (J v)-L0 u v =
      (L (J u) (J v)-B (J u) (J v))+(B (J u) (J v)-B (J0 u) (J0 v))+
        (B (J0 u) (J0 v)-L0 u v) := by ring
  rw [hSplit]
  exact (norm_add_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add hFirst hMiddle)) hLast).trans_eq (by ring))

end ShrinkingSpheres
