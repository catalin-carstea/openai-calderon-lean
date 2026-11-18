import Proof.PoissonFirstVariationBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres

/-- The actual canonical inverse has the genuine quadratic affine Taylor
remainder, retaining the same two invertible operators. -/
theorem norm_operator_inverse_affine_remainder_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A A0 A1 : E →L[ℝ] F) (hA : A.IsInvertible) (hA0 : A0.IsInvertible)
    (r C C0 D P Q : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hInv : ‖A.inverse‖ ≤ C) (hInv0 : ‖A0.inverse‖ ≤ C0)
    (hDiff : ‖A-A0‖ ≤ D*r) (hFirst : ‖A1‖ ≤ P)
    (hTaylor : ‖A-A0-r • A1‖ ≤ Q*r^2) :
    ‖A.inverse-A0.inverse-r • (-(A0.inverse.comp (A1.comp A0.inverse)))‖ ≤
      C*(Q+C0*D*P)*C0*r^2 := by
  have hNorm := norm_poisson_first_variation_remainder_le (ContinuousLinearMap.id ℝ E)
    A A0 (A-A0) 0 A1 A0.inverse hA hA0 (by simp) (ContinuousLinearMap.norm_id_le)
    r C C0 D P Q hr hC hC0 hD hP hQ hInv hInv0 hDiff hFirst
    (by simpa only [sub_zero] using hTaylor)
  have hPa : A0.inverse-A.inverse.comp ((A-A0).comp A0.inverse) = A.inverse := by
    apply ContinuousLinearMap.ext
    intro f
    have hEq := inverse_sub_inverse_apply A A0 hA hA0 f
    change A.inverse f-A0.inverse f = A.inverse ((A0-A) (A0.inverse f)) at hEq
    have hNeg : (A-A0) (A0.inverse f) = -((A0-A) (A0.inverse f)) := by
      simp only [ContinuousLinearMap.sub_apply]
      abel
    change A0.inverse f-A.inverse ((A-A0) (A0.inverse f)) = A.inverse f
    rw [hNeg,map_neg]
    have hFinal := sub_eq_iff_eq_add.mp hEq
    exact (sub_neg_eq_add _ _).trans ((add_comm _ _).trans hFinal.symm)
  have hBound : ‖A.inverse-A0.inverse-r • (-(A0.inverse.comp (A1.comp A0.inverse)))‖ ≤
      C*(Q+C0*D*P)*‖A0.inverse‖*r^2 := by
    simpa only [ContinuousLinearMap.id_comp,hPa] using hNorm
  exact hBound.trans (by gcongr)

end ShrinkingSpheres
