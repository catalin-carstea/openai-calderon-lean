import Proof.OperatorPoissonTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
namespace ShrinkingSpheres

/-- Product of three genuine affine operator expansions, with explicit
first variation and a shared quadratic bound. -/
theorem norm_operator_triple_taylor_le
    {H U V W : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A A0 A1 : V →L[ℝ] W) (K K0 K1 : U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U)
    (r CA DA QA CK DK QK CP QP : ℝ)
    (hr : 0 ≤ r) (hCA : 0 ≤ CA) (hDA : 0 ≤ DA) (hQA : 0 ≤ QA)
    (hCK : 0 ≤ CK) (hDK : 0 ≤ DK) (hQK : 0 ≤ QK) (hCP : 0 ≤ CP) (hQP : 0 ≤ QP)
    (hA : ‖A‖ ≤ CA) (hADiff : ‖A-A0‖ ≤ (DA+QA)*r)
    (hAR : ‖A-A0-r • A1‖ ≤ QA*r^2)
    (hK : ‖K‖ ≤ CK) (hKDiff : ‖K-K0‖ ≤ (DK+QK)*r)
    (hKR : ‖K-K0-r • K1‖ ≤ QK*r^2) (hK1 : ‖K1‖ ≤ DK)
    (hPR : ‖P-P0-r • P1‖ ≤ QP*r^2) (hP1 : ‖P1‖ ≤ CP) :
    ‖A.comp (K.comp P)-A0.comp (K0.comp P0)-
      r • (A0.comp (K0.comp P1+K1.comp P0)+A1.comp (K0.comp P0))‖ ≤
      (CA*(CK*QP+(DK+QK)*CP+QK*‖P0‖)+
        (DA+QA)*(‖K0‖*CP+DK*‖P0‖)+QA*‖K0.comp P0‖)*r^2 := by
  have hKP := norm_operator_poisson_taylor_le K K0 K1 P P0 P1
    r CK DK QK CP QP hr hCK hDK hQK hCP hQP hK hKDiff hKR hPR hP1
  have hFirst : ‖K0.comp P1+K1.comp P0‖ ≤ ‖K0‖*CP+DK*‖P0‖ :=
    (norm_add_le _ _).trans (add_le_add
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left hP1 (norm_nonneg _)))
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hK1 (norm_nonneg _))))
  exact norm_operator_poisson_taylor_le A A0 A1 (K.comp P) (K0.comp P0)
    (K0.comp P1+K1.comp P0) r CA DA QA (‖K0‖*CP+DK*‖P0‖)
    (CK*QP+(DK+QK)*CP+QK*‖P0‖) hr hCA hDA hQA (by positivity) (by positivity)
    hA hADiff hAR hKP hFirst

/-- A fixed boundary trace and its fixed multiplier offset preserve the
quadratic gain, and the offset cancels from the first variation. -/
theorem norm_trace_triple_taylor_le
    {H U V W Z : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : W →L[ℝ] Z) (N : H →L[ℝ] Z)
    (A A0 A1 : V →L[ℝ] W) (K K0 K1 : U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U)
    (r C : ℝ)
    (h : ‖A.comp (K.comp P)-A0.comp (K0.comp P0)-
      r • (A0.comp (K0.comp P1+K1.comp P0)+A1.comp (K0.comp P0))‖ ≤ C*r^2) :
    ‖(T.comp (A.comp (K.comp P))+N)-(T.comp (A0.comp (K0.comp P0))+N)-
      r • T.comp (A0.comp (K0.comp P1+K1.comp P0)+A1.comp (K0.comp P0))‖ ≤
      (‖T‖*C)*r^2 := by
  have hEq : (T.comp (A.comp (K.comp P))+N)-(T.comp (A0.comp (K0.comp P0))+N)-
      r • T.comp (A0.comp (K0.comp P1+K1.comp P0)+A1.comp (K0.comp P0)) =
      T.comp (A.comp (K.comp P)-A0.comp (K0.comp P0)-
        r • (A0.comp (K0.comp P1+K1.comp P0)+A1.comp (K0.comp P0))) := by
    simp only [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
    abel
  rw [hEq]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_left h (norm_nonneg T)).trans_eq (by ring))

end ShrinkingSpheres
