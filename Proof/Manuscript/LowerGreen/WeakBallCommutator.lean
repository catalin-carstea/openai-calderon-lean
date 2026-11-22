module

public import Proof.CalderonN.ActualRelativeWeakEnergyJets
public import Proof.Manuscript.LowerGreen.FirstOrderBallFamily
public import Proof.CalderonN.WeakEnergyOperatorFamily
public import Proof.CalderonN.BallRegularity.SmoothCommonSupportStrongOperator

import Proof.CalderonN.BallRegularity.StrongDerivativeValues
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
open CalderonN CalderonN.BallDirichlet TauCeti

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency true

namespace CalderonPaper.LowerGreen

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {n : ℕ} [NeZero n]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Turn an L² coefficient multiplier into a test against a fixed weak
value or first derivative. -/
def weakCoefficientPairingL (D : FixedBallH1Zero n →L[ℝ] FixedBallL2 n) :
    (FixedBallL2 n →L[ℝ] FixedBallL2 n) →L[ℝ]
    (FixedBallL2 n →L[ℝ] FixedBallH1Zero n →L[ℝ] ℝ) :=
  ContinuousLinearMap.compL ℝ (FixedBallL2 n) (FixedBallL2 n) (FixedBallH1Zero n →L[ℝ] ℝ)
    (((ContinuousLinearMap.compL ℝ (FixedBallH1Zero n) (FixedBallL2 n) ℝ).flip D).comp (innerSL ℝ))

theorem weakCoefficientPairingL_apply (D : FixedBallH1Zero n →L[ℝ] FixedBallL2 n)
    (B : FixedBallL2 n →L[ℝ] FixedBallL2 n) (f : FixedBallL2 n) (φ : FixedBallH1Zero n) :
    weakCoefficientPairingL D B f φ = ⟪B f,D φ⟫_ℝ := by
  simp only [weakCoefficientPairingL,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,innerSL_apply_apply]

private def ballZeroValueL (n : ℕ) : FixedBallH1Zero n →L[ℝ] FixedBallL2 n :=
  TauCeti.W1p0.valueL

private def ballZeroGradientL {n : ℕ} (i : I n) : FixedBallH1Zero n →L[ℝ] FixedBallL2 n :=
  (unitBallCoordinateGradientL (dim := n) i).comp (fixedBallZeroInclusionL n)

/- The coefficients of a differential cutoff satisfy div b = 2c. -/
def weakFirstOrderSumL
    (B : I n → FixedBallL2 n →L[ℝ] FixedBallL2 n) (C : FixedBallL2 n →L[ℝ] FixedBallL2 n) :
    FixedBallL2 n →L[ℝ] FixedBallH1Zero n →L[ℝ] ℝ :=
  -((∑ i : I n, weakCoefficientPairingL (ballZeroGradientL i) (B i)) +
    weakCoefficientPairingL (ballZeroValueL n) C)

omit [NeZero n] in
theorem weakFirstOrderSumL_apply
    (B : I n → FixedBallL2 n →L[ℝ] FixedBallL2 n) (C : FixedBallL2 n →L[ℝ] FixedBallL2 n)
    (f : FixedBallL2 n) (φ : FixedBallH1Zero n) :
    weakFirstOrderSumL B C f φ =
      -(∑ i, ⟪B i f,unitBallCoordinateGradientL i (φ : FixedBallH1 n)⟫_ℝ) -
      ⟪C f,W1p.value (φ : FixedBallH1 n)⟫_ℝ := by
  unfold weakFirstOrderSumL
  simp only [neg_apply, add_apply, sum_apply, weakCoefficientPairingL_apply,
    ballZeroValueL, W1p0.valueL_apply, ballZeroGradientL,
    ContinuousLinearMap.comp_apply, fixedBallZeroInclusionL, Submodule.subtypeL_apply]
  exact neg_add _ _

/-- The distributional extension of the first-order cutoff commutator. -/
@[expose] def weakFirstOrderBallL (b : I n → SmoothCoefficientJets n 1) (c : SmoothCoefficientJets n 1) :
    FixedBallL2 n →L[ℝ] FixedBallH1Zero n →L[ℝ] ℝ :=
  weakFirstOrderSumL (fun i => coefficientMultiplier fixedSobolevCalculus 0 (b i))
    (coefficientMultiplier fixedSobolevCalculus 0 c)

variable [FiniteDimensional ℝ P]

theorem contDiff_weakFirstOrderBallL_family
    (b : I n → P × X n → ℝ) (c : P × X n → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ContDiff ℝ ∞ c)
    (K : Set (X n)) (hK : IsCompact K)
    (hbK : ∀ i p z, z ∉ K → b i (p,z) = 0)
    (hcK : ∀ p z, z ∉ K → c (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => weakFirstOrderBallL
      (fun i => commonSupportCoefficientFamily 1 (b i) (hb i) K hK (hbK i) p)
      (commonSupportCoefficientFamily 1 c hc K hK hcK p)) := by
  let B (i : I n) (p : P) : FixedBallL2 n →L[ℝ] FixedBallL2 n :=
    coefficientMultiplier fixedSobolevCalculus 0
      (commonSupportCoefficientFamily 1 (b i) (hb i) K hK (hbK i) p)
  let C (p : P) : FixedBallL2 n →L[ℝ] FixedBallL2 n :=
    coefficientMultiplier fixedSobolevCalculus 0 (commonSupportCoefficientFamily 1 c hc K hK hcK p)
  have hB (i : I n) : ContDiff ℝ ∞ (B i) :=
    contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0 (b i) (hb i) K hK (hbK i)
  have hC : ContDiff ℝ ∞ C :=
    contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0 c hc K hK hcK
  change ContDiff ℝ ∞ (fun p => weakFirstOrderSumL (fun i => B i p) (C p))
  unfold weakFirstOrderSumL
  have hSum : ContDiff ℝ ∞ (fun p => ∑ i : I n, weakCoefficientPairingL (ballZeroGradientL i) (B i p)) :=
    ContDiff.sum (fun i _ => (weakCoefficientPairingL (ballZeroGradientL i)).contDiff.comp (hB i))
  exact (hSum.add ((weakCoefficientPairingL (ballZeroValueL n)).contDiff.comp hC)).neg

end CalderonPaper.LowerGreen

end
