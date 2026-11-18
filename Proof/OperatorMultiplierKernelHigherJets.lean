import Proof.BilinearTaylorHigherJets
import Proof.MultiplierTaylorGainKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {Q H U V W Z : Type*}
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def multiplierKernelTaylorJetBudget (N : ℕ) (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U)
    (K0 : U →L[ℝ] V) (CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 : ℝ) : ℝ :=
  let CR := bilinearTaylorJetBudget N (ContinuousLinearMap.compL ℝ U V W) CI CDI CQI CQK CK1 K0
  let CFirst := C0*CK1+C0*C0*CA1*‖K0‖
  ‖T‖*bilinearTaylorJetBudget N (ContinuousLinearMap.compL ℝ H U W)
    (2^N*CI*CK) (CFirst+CR) CR CQP CP1 H0

/-- The same inverse/forcing/Poisson Taylor product keeps the quadratic gain
    in every finite mixed parameter derivative. The inverse first variation
    is the actual negative sandwich by the same flat inverse. -/
theorem norm_iteratedFDeriv_operatorMultiplierTaylorKernel_le
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I : Q → V →L[ℝ] W) (I0 : V →L[ℝ] W)
    (A1 : Q → W →L[ℝ] V) (K K1 : Q → U →L[ℝ] V) (K0 : U →L[ℝ] V)
    (P P1 : Q → H →L[ℝ] U) (x : Q)
    (hI : ContDiffAt ℝ ∞ I x) (hA1 : ContDiffAt ℝ ∞ A1 x)
    (hK : ContDiffAt ℝ ∞ K x) (hK1 : ContDiffAt ℝ ∞ K1 x)
    (hP : ContDiffAt ℝ ∞ P x) (hP1 : ContDiffAt ℝ ∞ P1 x)
    (N : ℕ) (r CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hCA1 : 0 ≤ CA1) (hCK : 0 ≤ CK)
    (hCDI : 0 ≤ CDI) (hCQI : 0 ≤ CQI) (hCQK : 0 ≤ CQK) (hCK1 : 0 ≤ CK1)
    (hCQP : 0 ≤ CQP) (hCP1 : 0 ≤ CP1) (hNI0 : ‖I0‖ ≤ C0)
    (hIJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j I x‖ ≤ CI)
    (hA1Jets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j A1 x‖ ≤ CA1)
    (hKJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j K x‖ ≤ CK)
    (hK1Jets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j K1 x‖ ≤ CK1)
    (hIDiff : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => I p-I0) x‖ ≤ CDI*r)
    (hIRem : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => I p-I0-
      r • (-(I0.comp ((A1 p).comp I0)))) x‖ ≤ CQI*r^2)
    (hKRem : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => K p-K0-r • K1 p) x‖ ≤ CQK*r^2)
    (hPRem : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => P p-H0-r • P1 p) x‖ ≤ CQP*r^2)
    (hP1Jets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j P1 x‖ ≤ CP1)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => operatorMultiplierTaylorKernel T H0 (I p) I0 (A1 p)
      (K p) K0 (K1 p) (P p) H0 (P1 p) r) x‖ ≤
        multiplierKernelTaylorJetBudget N T H0 K0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1*r^2 := by
  let I1 := fun p => -(I0.comp ((A1 p).comp I0))
  let C := fun p => (I p).comp (K p)
  let C0op := I0.comp K0
  let C1 := fun p => I0.comp (K1 p)+(I1 p).comp K0
  let CR := bilinearTaylorJetBudget N (ContinuousLinearMap.compL ℝ U V W) CI CDI CQI CQK CK1 K0
  let CFirst := C0*CK1+C0*C0*CA1*‖K0‖
  have hI1 : ContDiffAt ℝ ∞ I1 x := (contDiffAt_const.clm_comp (hA1.clm_comp contDiffAt_const)).neg
  have hC : ContDiffAt ℝ ∞ C x := hI.clm_comp hK
  have hC1 : ContDiffAt ℝ ∞ C1 x :=
    (contDiffAt_const.clm_comp hK1).add (hI1.clm_comp contDiffAt_const)
  have hCR : 0 ≤ CR := by dsimp only [CR,bilinearTaylorJetBudget];positivity
  have hFirst : 0 ≤ CFirst := by dsimp only [CFirst];positivity
  have hCJets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j C x‖ ≤ 2^N*CI*CK :=
    norm_iteratedFDeriv_operator_comp_common_bound I K x hI hK N CI CK hCI hCK hIJets hKJets j hj
  have hI1Jets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j I1 x‖ ≤ C0*C0*CA1 := by
    rw [norm_iteratedFDeriv_neg_at _ x (contDiffAt_const.clm_comp (hA1.clm_comp contDiffAt_const)) j]
    exact (norm_iteratedFDeriv_operator_sandwich_le I0 I0 A1 x hA1 j).trans
      (mul_le_mul (mul_le_mul hNI0 hNI0 (norm_nonneg _) hC0) (hA1Jets j hj) (norm_nonneg _) (by positivity))
  have hC1Jets (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j C1 x‖ ≤ CFirst := by
    have hL := norm_iteratedFDeriv_operator_postcomp_fixed_le I0 K1 x hK1 j
    have hR := norm_iteratedFDeriv_operator_precomp_fixed_le I1 K0 x hI1 j
    have hSum := norm_iteratedFDeriv_add_at_le (fun p => I0.comp (K1 p)) (fun p => (I1 p).comp K0)
      x (contDiffAt_const.clm_comp hK1) (hI1.clm_comp contDiffAt_const) j
    exact hSum.trans ((add_le_add
      (hL.trans (mul_le_mul hNI0 (hK1Jets j hj) (norm_nonneg _) hC0))
      (hR.trans (mul_le_mul_of_nonneg_left (hI1Jets j hj) (norm_nonneg _)))).trans_eq (by dsimp only [CFirst];ring))
  have hCRem (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun p => C p-C0op-r • C1 p) x‖ ≤ CR*r^2 :=
    norm_iteratedFDeriv_bilinear_affine_remainder_le (ContinuousLinearMap.compL ℝ U V W)
      I I1 I0 K K1 K0 x hI hI1 hK hK1 N r CI CDI CQI CQK CK1 hr hCI hCDI hCQI hCQK hCK1
      hIJets hIDiff hIRem hKRem hK1Jets j hj
  have hCDiff (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun p => C p-C0op) x‖ ≤ (CFirst+CR)*r :=
    norm_iteratedFDeriv_difference_of_affine_remainder_le C C1 C0op x hC hC1 j r CFirst CR
      hr hr1 hFirst hCR (hC1Jets j hj) (hCRem j hj)
  let R := fun p => (C p).comp (P p)-C0op.comp H0-
    r • (C0op.comp (P1 p)+(C1 p).comp H0)
  have hR : ContDiffAt ℝ ∞ R x := ((hC.clm_comp hP).sub contDiffAt_const).sub
    (((contDiffAt_const.clm_comp hP1).add (hC1.clm_comp contDiffAt_const)).const_smul r)
  have hRN := norm_iteratedFDeriv_bilinear_affine_remainder_le (ContinuousLinearMap.compL ℝ H U W)
    C C1 C0op P P1 H0 x hC hC1 hP hP1 N r (2^N*CI*CK) (CFirst+CR) CR CQP CP1
      hr (by positivity) (by positivity) hCR hCQP hCP1 hCJets hCDiff hCRem hPRem hP1Jets n hn
  have hEq : (fun p => operatorMultiplierTaylorKernel T H0 (I p) I0 (A1 p)
      (K p) K0 (K1 p) (P p) H0 (P1 p) r) = fun p => T.comp (R p) := by
    funext p
    simp only [operatorMultiplierTaylorKernel,R,C,C0op,C1,I1,ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_assoc]
    abel
  rw [hEq]
  exact (norm_iteratedFDeriv_operator_postcomp_fixed_le T R x hR n).trans
    ((mul_le_mul_of_nonneg_left hRN (norm_nonneg _)).trans_eq (by dsimp only [multiplierKernelTaylorJetBudget,CR,CFirst];ring))

end ShrinkingSpheres
