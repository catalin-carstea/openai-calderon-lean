import Proof.BilinearPoissonComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
namespace ShrinkingSpheres

/-- A coefficient energy Taylor model and its actual Poisson Taylor model
    give the quadratic boundary energy remainder, with the first variation
    retained explicitly. -/
theorem norm_bilinear_poisson_taylor_le
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (E E0 E1 : H →L[ℝ] H →L[ℝ] ℝ) (P P0 P1 : F →L[ℝ] H)
    (r D L A B C : ℝ) (hr : 0 ≤ r) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hE : ‖E‖ ≤ D) (hE1 : ‖E1‖ ≤ L)
    (hEError : ‖E-E0-r • E1‖ ≤ A*r^2)
    (hPError : ‖P-P0-r • P1‖ ≤ B*r^2)
    (hP1 : ‖P1‖ ≤ C) (hEDiff : ‖E-E0‖ ≤ (L+A)*r) :
    ‖E.bilinearComp P P0-E0.bilinearComp P0 P0-
      r • (E0.bilinearComp P1 P0+E1.bilinearComp P0 P0)‖ ≤
      (D*B+(L+A)*C+A*‖P0‖)*‖P0‖*r^2 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro f z
  simp only [_root_.sub_apply,_root_.smul_apply,_root_.add_apply,ContinuousLinearMap.bilinearComp_apply,smul_eq_mul]
  have hAlg : E (P f) (P0 z)-E0 (P0 f) (P0 z)-
      r*(E0 (P1 f) (P0 z)+E1 (P0 f) (P0 z)) =
      E ((P-P0-r • P1) f) (P0 z)+r*(E-E0) (P1 f) (P0 z)+
        (E-E0-r • E1) (P0 f) (P0 z) := by
    simp only [_root_.sub_apply,_root_.smul_apply,map_sub,map_smul,smul_eq_mul]
    ring
  rw [hAlg]
  have hPe : ‖(P-P0-r • P1) f‖ ≤ (B*r^2)*‖f‖ :=
    ((P-P0-r • P1).le_opNorm f).trans (mul_le_mul_of_nonneg_right hPError (norm_nonneg _))
  have hPv : ‖P1 f‖ ≤ C*‖f‖ := (P1.le_opNorm f).trans (mul_le_mul_of_nonneg_right hP1 (norm_nonneg _))
  have h1 : ‖E ((P-P0-r • P1) f) (P0 z)‖ ≤ D*((B*r^2)*‖f‖)*(‖P0‖*‖z‖) :=
    (E.le_opNorm₂ _ _).trans (by gcongr;exact P0.le_opNorm z)
  have h2 : ‖r*(E-E0) (P1 f) (P0 z)‖ ≤ r*(((L+A)*r)*(C*‖f‖)*(‖P0‖*‖z‖)) := by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (((E-E0).le_opNorm₂ _ _).trans (by
      gcongr
      exact P0.le_opNorm z)) hr
  have h3 : ‖(E-E0-r • E1) (P0 f) (P0 z)‖ ≤ (A*r^2)*(‖P0‖*‖f‖)*(‖P0‖*‖z‖) :=
    ((E-E0-r • E1).le_opNorm₂ _ _).trans (by
      gcongr
      exact P0.le_opNorm f
      exact P0.le_opNorm z)
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    ((add_le_add (add_le_add h1 h2) h3).trans_eq (by ring))

end ShrinkingSpheres
