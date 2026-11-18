import Proof.OperatorMultiplierKernelHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {H U V W Z : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def multiplierKernelTaylorScalarJetBudget (N : ℕ) (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U)
    (normK0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 : ℝ) : ℝ :=
  let CR := ‖(ContinuousLinearMap.compL ℝ U V W)‖*2^N*(CI*CQK+CQI*normK0+CDI*CK1)
  let CFirst := C0*CK1+C0*C0*CA1*normK0
  ‖T‖*‖(ContinuousLinearMap.compL ℝ H U W)‖*2^N*
    ((2^N*CI*CK)*CQP+CR*‖H0‖+(CFirst+CR)*CP1)

theorem multiplierKernelTaylorJetBudget_le_scalar
    (N : ℕ) (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U) (K0 : U →L[ℝ] V)
    (normK0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 : ℝ)
    (hK0 : ‖K0‖ ≤ normK0) (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hCA1 : 0 ≤ CA1)
    (hCQI : 0 ≤ CQI) (hCP1 : 0 ≤ CP1) :
    multiplierKernelTaylorJetBudget N T H0 K0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 ≤
      multiplierKernelTaylorScalarJetBudget (V:=V) N T H0 normK0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 := by
  unfold multiplierKernelTaylorJetBudget multiplierKernelTaylorScalarJetBudget bilinearTaylorJetBudget
  dsimp only
  simp only [mul_assoc]
  gcongr

/-- The kernel Taylor budget is linear in all multiplier-dependent inputs.
    This is the quantitative step needed before a multiplier may move. -/
theorem multiplierKernelTaylorScalarJetBudget_homogeneous
    (N : ℕ) (T : W →L[ℝ] Z) (H0 : H →L[ℝ] U)
    (normK0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1 s : ℝ) :
    multiplierKernelTaylorScalarJetBudget (V:=V) N T H0 (normK0*s) CI C0 CA1 (CK*s) CDI CQI (CQK*s) (CK1*s) CQP CP1 =
      multiplierKernelTaylorScalarJetBudget (V:=V) N T H0 normK0 CI C0 CA1 CK CDI CQI CQK CK1 CQP CP1*s := by
  unfold multiplierKernelTaylorScalarJetBudget
  ring

end ShrinkingSpheres
