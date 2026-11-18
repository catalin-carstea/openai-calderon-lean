import Proof.OperatorMultiplierCurriedKernel
import Proof.ClosedLocalMultiplierForcing
import Proof.CommonSupportNativeMultiplierKernelHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The same native gained Taylor kernel, as a bounded linear operator in
    its multiplier slot before a moving geometric multiplier is chosen. -/
def commonSupportNativeMultiplierKernelInMultiplierL
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P) :
    SmoothCoefficientJets 3 →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  operatorMultiplierTaylorKernelInMultiplierL (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
    (strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse
    (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
    (strongDirichletOperator fixedSobolevCalculus 0 (F1 p))
    (closedNativeBulkMultiplierForcingL (commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz p))
    (nativeBulkMultiplierForcingBilinearL F0)
    (closedNativeBulkMultiplierForcingL (commonSupportClosedCoefficientMatrixFamily 2 a1 ha1 S1 hS1 hz1 p))
    (commonSupportWeakHalfLift a ha p) fixedHarmonicH1LiftL
    (weakFirstPoissonVariationL 1 (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) r

theorem commonSupportNativeMultiplierKernelInMultiplierL_apply
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P) (Q : SmoothCoefficientJets 3) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p Q =
      operatorMultiplierTaylorKernel (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
        (strongDirichletOperator fixedSobolevCalculus 0 (F p)).inverse
        (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
        (strongDirichletOperator fixedSobolevCalculus 0 (F1 p))
        (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F p) (fun _ => 0) Q)
        (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
        (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 p) (fun _ => 0) Q)
        (commonSupportWeakHalfLift a ha p) fixedHarmonicH1LiftL
        (weakFirstPoissonVariationL 1 (fun z => a1 (p,z)) (commonSupportEnergyMemLp a1 ha1 p)) r := by
  intro F F1
  simp only [commonSupportNativeMultiplierKernelInMultiplierL,operatorMultiplierTaylorKernelInMultiplierL_apply,
    commonSupportClosedCoefficientMatrixFamily]
  rw [closedNativeBulkMultiplierForcingL_eq_on_smooth,closedNativeBulkMultiplierForcingL_eq_on_smooth]
  rfl

theorem contDiffAt_commonSupportNativeMultiplierKernelInMultiplierL
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P)
    (hStrong : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hWeak : (commonSupportZeroWeakEnergy a ha p).IsInvertible) :
    ContDiffAt ℝ ∞ (commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r) p := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let A := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)
  have hA := (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha S hS hz).contDiffAt (x:=p)
  have hInvMap : ContDiffAt ℝ ∞ (fun L : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => L.inverse) (A p) :=
    hStrong.contDiffAt_map_inverse
  have hI : ContDiffAt ℝ ∞ (fun t => (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse) p :=
    hInvMap.comp (f:=A) p hA
  have hA1 := (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a1 ha1 S1 hS1 hz1).contDiffAt (x:=p)
  have hK : ContDiffAt ℝ ∞ (fun t => closedNativeBulkMultiplierForcingL
      (commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz t)) p :=
    closedNativeBulkMultiplierForcingL.contDiff.contDiffAt.comp p
      (contDiff_commonSupportClosedCoefficientMatrixFamily 2 a ha S hS hz).contDiffAt
  have hK1 : ContDiffAt ℝ ∞ (fun t => closedNativeBulkMultiplierForcingL
      (commonSupportClosedCoefficientMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)) p :=
    closedNativeBulkMultiplierForcingL.contDiff.contDiffAt.comp p
      (contDiff_commonSupportClosedCoefficientMatrixFamily 2 a1 ha1 S1 hS1 hz1).contDiffAt
  have hW : ContDiffAt ℝ ∞ (commonSupportWeakHalfLift a ha) p := by
    rw [commonSupportWeakHalfLift_eq_affineInverseCorrection]
    exact contDiffAt_affineInverseCorrectionFamily (P:=P) (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      (U:=BallH1) (Z:=SphereSobolev (1/2:ℝ)) _ _ _ _ p hWeak
      (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).contDiffAt
      (contDiff_commonSupportWeakEnergy a ha S hS hz).contDiffAt
  have hW1 := (contDiff_commonSupport_weakFirstPoisson a1 ha1 S1 hS1 hz1 1).contDiffAt (x:=p)
  exact contDiffAt_operatorMultiplierTaylorKernelInMultiplierL _ _ _ _ _ _ _ _ _ _ _ _ p
    hI hA1 hK hK1 hW hW1

end ShrinkingSpheres
