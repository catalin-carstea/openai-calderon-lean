import Proof.InverseAffineRemainderFactorization
import Proof.FiniteJetBudgetAlgebra
import Proof.OperatorFamilyJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F U Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def poissonAffineRemainderJetBudget (N : ℕ) (CI C0 CD C1 CQ : ℝ) (H : Z →L[ℝ] U) : ℝ :=
  2^N*CI*(CQ+2^N*CD*C0*C1)*‖H‖

/-- Every finite mixed parameter jet of the SAME Poisson Taylor remainder
    keeps its quadratic radius gain. All inverse jets and coefficient/operator
    remainder jets are explicit premises for the native downstream caller. -/
theorem norm_iteratedFDeriv_poisson_affine_remainder_le
    (A : P → E →L[ℝ] F) (A0 : E →L[ℝ] F) (T T1 : P → U →L[ℝ] F)
    (T0 : U →L[ℝ] F) (H : Z →L[ℝ] U) (x : P)
    (hA : ContDiffAt ℝ ∞ A x) (hT : ContDiffAt ℝ ∞ T x) (hT1 : ContDiffAt ℝ ∞ T1 x)
    (hAx : (A x).IsInvertible) (hA0 : A0.IsInvertible) (hFlat : T0.comp H = 0)
    (N : ℕ) (r CI C0 CD C1 CQ : ℝ) (hr : 0 ≤ r)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hCD : 0 ≤ CD) (hC1 : 0 ≤ C1) (hCQ : 0 ≤ CQ)
    (hNI0 : ‖A0.inverse‖ ≤ C0)
    (hInvJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => (A p).inverse) x‖ ≤ CI)
    (hDiffJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => A p-A0) x‖ ≤ CD*r)
    (hFirstJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j T1 x‖ ≤ C1)
    (hRemainderJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => T p-T0-r • T1 p) x‖ ≤ CQ*r^2)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => (A p).inverse.comp ((T p).comp H)-
      r • A0.inverse.comp ((T1 p).comp H)) x‖ ≤
      poissonAffineRemainderJetBudget N CI C0 CD C1 CQ H*r^2 := by
  let Inv := fun p => (A p).inverse
  let Delta := fun p => A p-A0
  let Q := fun p => T p-T0-r • T1 p
  let L := fun p => A0.inverse.comp ((T1 p).comp H)
  let D := fun p => (Delta p).comp (L p)
  let QH := fun p => (Q p).comp H
  let R := fun p => QH p-r • D p
  let CR := (CQ+2^N*CD*C0*C1)*‖H‖
  have hInv : ContDiffAt ℝ ∞ Inv x := hAx.contDiffAt_map_inverse.comp x hA
  have hDelta : ContDiffAt ℝ ∞ Delta x := hA.sub contDiffAt_const
  have hQ : ContDiffAt ℝ ∞ Q x := (hT.sub contDiffAt_const).sub (hT1.const_smul r)
  have hL : ContDiffAt ℝ ∞ L x := contDiffAt_const.clm_comp (hT1.clm_comp contDiffAt_const)
  have hD : ContDiffAt ℝ ∞ D x := hDelta.clm_comp hL
  have hQH : ContDiffAt ℝ ∞ QH x := hQ.clm_comp contDiffAt_const
  have hR : ContDiffAt ℝ ∞ R x := hQH.sub (hD.const_smul r)
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hLJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j L x‖ ≤ C0*‖H‖*C1 :=
    (norm_iteratedFDeriv_operator_sandwich_le A0.inverse H T1 x hT1 j).trans
      (mul_le_mul (mul_le_mul_of_nonneg_right hNI0 (norm_nonneg H)) (hFirstJets j hj)
        (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg H)))
  have hDJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j D x‖ ≤
      2^N*(CD*r)*(C0*‖H‖*C1) :=
    norm_iteratedFDeriv_operator_comp_common_bound Delta L x hDelta hL N (CD*r) (C0*‖H‖*C1)
      (mul_nonneg hCD hr) (by positivity) hDiffJets hLJ j hj
  have hQHJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j QH x‖ ≤ ‖H‖*(CQ*r^2) := by
    have hh := norm_iteratedFDeriv_operator_sandwich_le (ContinuousLinearMap.id ℝ F) H Q x hQ j
    simp only [ContinuousLinearMap.id_comp] at hh
    have hId : ‖ContinuousLinearMap.id ℝ F‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hNH : ‖ContinuousLinearMap.id ℝ F‖*‖H‖ ≤ ‖H‖ :=
      (mul_le_mul_of_nonneg_right hId (norm_nonneg H)).trans_eq (one_mul _)
    exact hh.trans (mul_le_mul hNH (hRemainderJets j hj) (norm_nonneg _) (norm_nonneg H))
  have hRJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j R x‖ ≤ CR*r^2 := by
    have hh := norm_iteratedFDeriv_sub_at_le QH (fun p => r • D p) x hQH (hD.const_smul r) j
    rw [norm_iteratedFDeriv_const_smul_at D x hD r j,abs_of_nonneg hr] at hh
    exact hh.trans ((add_le_add (hQHJ j hj) (mul_le_mul_of_nonneg_left (hDJ j hj) hr)).trans_eq
      (by dsimp only [CR];ring))
  have hProduct := norm_iteratedFDeriv_operator_comp_common_bound Inv R x hInv hR N CI (CR*r^2)
    hCI (by positivity) hInvJets hRJ n hn
  have he := poisson_affine_remainder_factorization_germ A A0 T T1 T0 H x hA.continuousAt hAx hA0 hFlat r
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hProduct.trans_eq (by dsimp only [poissonAffineRemainderJetBudget,CR];ring)

end ShrinkingSpheres
