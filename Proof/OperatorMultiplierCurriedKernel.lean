import Proof.MultiplierTaylorGainKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P Q H U V W Z : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def operatorMultiplierSandwichL (A : V →L[ℝ] W) (K : Q →L[ℝ] U →L[ℝ] V) (B : H →L[ℝ] U) :
    Q →L[ℝ] H →L[ℝ] W :=
  ((ContinuousLinearMap.compL ℝ H V W) A).comp
    ((((ContinuousLinearMap.compL ℝ H U V).flip) B).comp K)

lemma operatorMultiplierSandwichL_apply (A : V →L[ℝ] W) (K : Q →L[ℝ] U →L[ℝ] V) (B : H →L[ℝ] U) (q : Q) :
    operatorMultiplierSandwichL A K B q = A.comp ((K q).comp B) := rfl

theorem contDiffAt_operatorMultiplierSandwichL
    (A : P → V →L[ℝ] W) (K : P → Q →L[ℝ] U →L[ℝ] V) (B : P → H →L[ℝ] U) (x : P)
    (hA : ContDiffAt ℝ ∞ A x) (hK : ContDiffAt ℝ ∞ K x) (hB : ContDiffAt ℝ ∞ B x) :
    ContDiffAt ℝ ∞ (fun p => operatorMultiplierSandwichL (A p) (K p) (B p)) x :=
  (((ContinuousLinearMap.compL ℝ H V W).contDiff.contDiffAt.comp x hA).clm_comp
    ((((ContinuousLinearMap.compL ℝ H U V).flip).contDiff.contDiffAt.comp x hB).clm_comp hK))

/-- The true multiplier Taylor kernel, curried in its linear multiplier
    slot. Its canonical operator factors are identical to the fixed-input kernel. -/
def operatorMultiplierTaylorKernelInMultiplierL
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I I0 : V →L[ℝ] W) (A1 : W →L[ℝ] V)
    (K K0 K1 : Q →L[ℝ] U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U) (r : ℝ) : Q →L[ℝ] H →L[ℝ] Z :=
  operatorMultiplierSandwichL (T.comp I) K P-operatorMultiplierSandwichL (T.comp I0) K0 P0-
    r • (operatorMultiplierSandwichL (T.comp I0) K0 P1+operatorMultiplierSandwichL (T.comp I0) K1 H0+
      operatorMultiplierSandwichL (T.comp (-(I0.comp (A1.comp I0)))) K0 H0)

theorem operatorMultiplierTaylorKernelInMultiplierL_apply
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I I0 : V →L[ℝ] W) (A1 : W →L[ℝ] V)
    (K K0 K1 : Q →L[ℝ] U →L[ℝ] V) (P P0 P1 : H →L[ℝ] U) (r : ℝ) (q : Q) :
    operatorMultiplierTaylorKernelInMultiplierL T H0 I I0 A1 K K0 K1 P P0 P1 r q =
      operatorMultiplierTaylorKernel T H0 I I0 A1 (K q) (K0 q) (K1 q) P P0 P1 r := by
  simp only [operatorMultiplierTaylorKernelInMultiplierL,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,operatorMultiplierSandwichL_apply,
    operatorMultiplierTaylorKernel,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul,ContinuousLinearMap.comp_assoc]

theorem contDiffAt_operatorMultiplierTaylorKernelInMultiplierL
    (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (I : P → V →L[ℝ] W) (I0 : V →L[ℝ] W)
    (A1 : P → W →L[ℝ] V) (K K1 : P → Q →L[ℝ] U →L[ℝ] V) (K0 : Q →L[ℝ] U →L[ℝ] V)
    (P0 : H →L[ℝ] U) (W0 W1 : P → H →L[ℝ] U) (r : ℝ) (x : P)
    (hI : ContDiffAt ℝ ∞ I x) (hA1 : ContDiffAt ℝ ∞ A1 x)
    (hK : ContDiffAt ℝ ∞ K x) (hK1 : ContDiffAt ℝ ∞ K1 x)
    (hW0 : ContDiffAt ℝ ∞ W0 x) (hW1 : ContDiffAt ℝ ∞ W1 x) :
    ContDiffAt ℝ ∞ (fun p => operatorMultiplierTaylorKernelInMultiplierL T H0 (I p) I0 (A1 p)
      (K p) K0 (K1 p) (W0 p) P0 (W1 p) r) x := by
  have hA : ContDiffAt ℝ ∞ (fun p => T.comp (I p)) x := contDiffAt_const.clm_comp hI
  have hFirst : ContDiffAt ℝ ∞ (fun p => T.comp (-(I0.comp ((A1 p).comp I0)))) x :=
    contDiffAt_const.clm_comp ((contDiffAt_const.clm_comp (hA1.clm_comp contDiffAt_const)).neg)
  exact ((contDiffAt_operatorMultiplierSandwichL _ _ _ x hA hK hW0).sub contDiffAt_const).sub
    ((((contDiffAt_operatorMultiplierSandwichL _ _ _ x contDiffAt_const contDiffAt_const hW1).add
      (contDiffAt_operatorMultiplierSandwichL _ _ _ x contDiffAt_const hK1 contDiffAt_const)).add
        (contDiffAt_operatorMultiplierSandwichL _ _ _ x hFirst contDiffAt_const contDiffAt_const)).const_smul r)

end ShrinkingSpheres
