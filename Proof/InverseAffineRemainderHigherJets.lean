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

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def inverseAffineRemainderJetBudget (N : ℕ) (CI C0 CD C1 CQ : ℝ) : ℝ :=
  2^N*CI*C0*(CQ+2^N*CD*C0*C1)

theorem norm_iteratedFDeriv_inverse_affine_remainder_le
    (A A1 : P → E →L[ℝ] F) (A0 : E →L[ℝ] F) (x : P)
    (hA : ContDiffAt ℝ ∞ A x) (hA1 : ContDiffAt ℝ ∞ A1 x)
    (hAx : (A x).IsInvertible) (hA0 : A0.IsInvertible)
    (N : ℕ) (r CI C0 CD C1 CQ : ℝ) (hr : 0 ≤ r)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hCD : 0 ≤ CD) (hC1 : 0 ≤ C1) (hCQ : 0 ≤ CQ)
    (hNI0 : ‖A0.inverse‖ ≤ C0)
    (hInvJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => (A p).inverse) x‖ ≤ CI)
    (hDiffJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => A p-A0) x‖ ≤ CD*r)
    (hFirstJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j A1 x‖ ≤ C1)
    (hRemainderJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => A p-A0-r • A1 p) x‖ ≤ CQ*r^2)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => (A p).inverse-A0.inverse+
      r • A0.inverse.comp ((A1 p).comp A0.inverse)) x‖ ≤
      inverseAffineRemainderJetBudget N CI C0 CD C1 CQ*r^2 := by
  let Inv := fun p => (A p).inverse
  let Delta := fun p => A p-A0
  let Q := fun p => A p-A0-r • A1 p
  let L := fun p => A0.inverse.comp ((A1 p).comp A0.inverse)
  let D := fun p => (Delta p).comp (L p)
  let QI := fun p => (Q p).comp A0.inverse
  let R := fun p => -(QI p)+r • D p
  let CR := C0*(CQ+2^N*CD*C0*C1)
  have hInv : ContDiffAt ℝ ∞ Inv x := hAx.contDiffAt_map_inverse.comp x hA
  have hDelta : ContDiffAt ℝ ∞ Delta x := hA.sub contDiffAt_const
  have hQ : ContDiffAt ℝ ∞ Q x := hDelta.sub (hA1.const_smul r)
  have hL : ContDiffAt ℝ ∞ L x := contDiffAt_const.clm_comp (hA1.clm_comp contDiffAt_const)
  have hD : ContDiffAt ℝ ∞ D x := hDelta.clm_comp hL
  have hQI : ContDiffAt ℝ ∞ QI x := hQ.clm_comp contDiffAt_const
  have hR : ContDiffAt ℝ ∞ R x := hQI.neg.add (hD.const_smul r)
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hLJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j L x‖ ≤ C0*C0*C1 :=
    (norm_iteratedFDeriv_operator_sandwich_le A0.inverse A0.inverse A1 x hA1 j).trans
      (mul_le_mul (mul_le_mul hNI0 hNI0 (norm_nonneg _) hC0) (hFirstJets j hj)
        (norm_nonneg _) (mul_nonneg hC0 hC0))
  have hDJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j D x‖ ≤
      2^N*(CD*r)*(C0*C0*C1) :=
    norm_iteratedFDeriv_operator_comp_common_bound Delta L x hDelta hL N (CD*r) (C0*C0*C1)
      (mul_nonneg hCD hr) (by positivity) hDiffJets hLJ j hj
  have hQIJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j QI x‖ ≤ C0*(CQ*r^2) := by
    have hh := norm_iteratedFDeriv_operator_sandwich_le (ContinuousLinearMap.id ℝ F) A0.inverse Q x hQ j
    simp only [ContinuousLinearMap.id_comp] at hh
    have hId : ‖ContinuousLinearMap.id ℝ F‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hNI : ‖ContinuousLinearMap.id ℝ F‖*‖A0.inverse‖ ≤ C0 :=
      (mul_le_mul hId hNI0 (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    exact hh.trans (mul_le_mul hNI (hRemainderJets j hj) (norm_nonneg _) hC0)
  have hRJ (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j R x‖ ≤ CR*r^2 := by
    have hh := norm_iteratedFDeriv_add_at_le (fun p => -(QI p)) (fun p => r • D p) x
      hQI.neg (hD.const_smul r) j
    rw [norm_iteratedFDeriv_neg_at QI x hQI j,norm_iteratedFDeriv_const_smul_at D x hD r j,abs_of_nonneg hr] at hh
    exact hh.trans ((add_le_add (hQIJ j hj) (mul_le_mul_of_nonneg_left (hDJ j hj) hr)).trans_eq
      (by dsimp only [CR];ring))
  have hProduct := norm_iteratedFDeriv_operator_comp_common_bound Inv R x hInv hR N CI (CR*r^2)
    hCI (by positivity) hInvJets hRJ n hn
  have he := inverse_affine_remainder_factorization_germ A A1 A0 x hA.continuousAt hAx hA0 r
  have he2 : (fun p => -((A p).inverse.comp ((A p-A0-r • A1 p).comp A0.inverse))+
        r • (A p).inverse.comp ((A p-A0).comp (A0.inverse.comp ((A1 p).comp A0.inverse)))) =
      fun p => (Inv p).comp (R p) := by
    funext p
    simp only [Inv,R,QI,Q,D,Delta,L,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.comp_smul]
  rw [he2] at he
  rw [(he.iteratedFDeriv ℝ n).eq_of_nhds]
  exact hProduct.trans_eq (by dsimp only [inverseAffineRemainderJetBudget,CR];ring)

end ShrinkingSpheres
