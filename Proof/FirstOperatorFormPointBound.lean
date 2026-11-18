/- Three generic point estimates adapted from the selected ZIP. No specialized radius/frame budget is imported. -/
import Proof.LocalSupportedOperatorPairing
import Proof.WeightedErrorForms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.OperatorForms
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma abs_operator_pair_general (P : G →L[ℝ] F →L[ℝ] ℝ) (C : E →L[ℝ] F) (v : G) (u : E) :
    |P v (C u)| ≤ ‖P‖*‖C‖*(‖v‖*‖u‖) := by
  have hn : |P v (C u)| ≤ ‖P‖*‖v‖*‖C u‖ := by
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm₂ P v (C u)
  calc _ ≤ ‖P‖*‖v‖*‖C u‖ := hn
       _ ≤ ‖P‖*‖v‖*(‖C‖*‖u‖) := mul_le_mul_of_nonneg_left (C.le_opNorm u) (by positivity)
       _ = _ := by ring

lemma abs_operator_mass_pair (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G)
    (C : E →L[ℝ] F) (u : E) : |P (I u) (C u)| ≤ ‖P‖*‖I‖*‖C‖*‖u‖^2 := by
  calc _ ≤ ‖P‖*‖C‖*(‖I u‖*‖u‖) := abs_operator_pair_general P C (I u) u
       _ ≤ ‖P‖*‖C‖*((‖I‖*‖u‖)*‖u‖) :=
         mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (I.le_opNorm u) (norm_nonneg u)) (by positivity)
       _ = _ := by ring

 
lemma reduced_first_point_bound
    (P : G →L[ℝ] F →L[ℝ] ℝ) (I : E →L[ℝ] G) (C D : E →L[ℝ] F)
    (u : E) (du : G) (mu dmu beta Q M eps energy : ℝ)
    (hmu : 0 ≤ mu) (hb : 1 ≤ beta) (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (he : 0 ≤ energy) (hMass : ‖u‖^2 ≤ energy) (hMixed : ‖du‖*‖u‖ ≤ energy)
    (hC : ‖C‖ ≤ Q*eps/beta) (hD : ‖D‖ ≤ Q*eps) (hdmu : |dmu| ≤ M*mu) :
    |dmu*P (I u) (C u)+mu*P du (C u)+mu*P (I u) (D u)| ≤
      (‖P‖*Q*((M+1)*‖I‖+2)*eps)*(mu*energy) := by
  have hbpos : 0 < beta := lt_of_lt_of_le zero_lt_one hb
  have hi : beta⁻¹ ≤ 1 := (inv_le_one₀ hbpos).mpr hb
  have hMassInv : beta⁻¹*‖u‖^2 ≤ energy := by
    have h := mul_le_mul_of_nonneg_right hi (sq_nonneg ‖u‖)
    exact (by simpa only [one_mul] using h : beta⁻¹*‖u‖^2 ≤ ‖u‖^2).trans hMass
  have hMixedInv : beta⁻¹*(‖du‖*‖u‖) ≤ energy := by
    have h := mul_le_mul_of_nonneg_right hi (mul_nonneg (norm_nonneg du) (norm_nonneg u))
    exact (by simpa only [one_mul] using h : beta⁻¹*(‖du‖*‖u‖) ≤ ‖du‖*‖u‖).trans hMixed
  have h1 : |dmu*P (I u) (C u)| ≤ (‖P‖*Q*M*‖I‖*eps)*(mu*energy) := by
    rw [abs_mul]
    calc _ ≤ (M*mu)*(‖P‖*‖I‖*‖C‖*‖u‖^2) :=
           mul_le_mul hdmu (abs_operator_mass_pair P I C u) (abs_nonneg _) (by positivity)
         _ ≤ (M*mu)*(‖P‖*‖I‖*(Q*eps/beta)*‖u‖^2) := by gcongr
         _ = (‖P‖*Q*M*‖I‖*eps*mu)*(beta⁻¹*‖u‖^2) := by rw [div_eq_mul_inv]; ring
         _ ≤ (‖P‖*Q*M*‖I‖*eps*mu)*energy := mul_le_mul_of_nonneg_left hMassInv (by positivity)
         _ = _ := by ring
  have h2 : |mu*P du (C u)| ≤ (‖P‖*Q*eps)*(mu*energy) := by
    rw [abs_mul,abs_of_nonneg hmu]
    calc _ ≤ mu*(‖P‖*‖C‖*(‖du‖*‖u‖)) := mul_le_mul_of_nonneg_left (abs_operator_pair_general P C du u) hmu
         _ ≤ mu*(‖P‖*(Q*eps/beta)*(‖du‖*‖u‖)) := by gcongr
         _ = (‖P‖*Q*eps*mu)*(beta⁻¹*(‖du‖*‖u‖)) := by rw [div_eq_mul_inv]; ring
         _ ≤ (‖P‖*Q*eps*mu)*energy := mul_le_mul_of_nonneg_left hMixedInv (by positivity)
         _ = _ := by ring
  have h3 : |mu*P (I u) (D u)| ≤ (‖P‖*Q*‖I‖*eps)*(mu*energy) := by
    rw [abs_mul,abs_of_nonneg hmu]
    calc _ ≤ mu*(‖P‖*‖I‖*‖D‖*‖u‖^2) := mul_le_mul_of_nonneg_left (abs_operator_mass_pair P I D u) hmu
         _ ≤ mu*(‖P‖*‖I‖*(Q*eps)*‖u‖^2) := by gcongr
         _ ≤ mu*(‖P‖*‖I‖*(Q*eps)*energy) := by gcongr
         _ = _ := by ring
  have ht := (abs_add_le (dmu*P (I u) (C u)+mu*P du (C u)) (mu*P (I u) (D u))).trans
    (add_le_add (abs_add_le (dmu*P (I u) (C u)) (mu*P du (C u))) le_rfl)
  have h0 : 0 ≤ ‖P‖*Q*eps*mu*energy := by positivity
  nlinarith only [ht,h1,h2,h3,h0]

end ShrinkingSpheres.OperatorForms
