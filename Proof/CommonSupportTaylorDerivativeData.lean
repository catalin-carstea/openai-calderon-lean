import Proof.CommonSupportAffineOperatorFamilies
import Proof.CommonSupportDirectionalGenerators
import Proof.AffineWeakEnergyFamilyIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL fullCoefficientOperatorL strongCoefficientOperatorL

/-- Constant baseline changes do not change the actual affine residual derivative. -/
lemma fderiv_affine_taylor_family_eq {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A A1 D : P → E) (A00 A0 : E) (r : ℝ) (x : P)
    (hFamily : ∀ p,A p = A00+r • A1 p+D p) :
    fderiv ℝ (fun p => A p-A0-r • A1 p) x = fderiv ℝ D x := by
  have hFun : (fun p => A p-A0-r • A1 p) = fun p => (A00-A0)+D p := by
    funext p;rw [hFamily];module
  rw [hFun,fderiv_const_add]

/-- Native Taylor derivatives for the actual principal and first-model
    coefficient witnesses. The tangent estimate uses scalarity only locally. -/
structure CommonSupportTaylorDerivativeBounds
    (a a1 : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r : ℝ) (F0 : SmoothCoefficientMatrix 2) (q : ℝ) : Prop where
  strong : ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz t)-
    strongDirichletOperator fixedSobolevCalculus 0 F0-
    r • strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)) 0‖ ≤
      2*strongC1OperatorBudget fixedSobolevCalculus*q
  full : ‖fderiv ℝ (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz t)-
    fullCoefficientOperatorL fixedSobolevCalculus 0 F0-
    r • fullCoefficientOperatorL fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)) 0‖ ≤
      2*fullC1OperatorBudget fixedSobolevCalculus*q
  fullWeak : ‖fderiv ℝ (fun t => commonSupportFullWeakEnergy a ha t-TauCeti.PDE.energyFormH1L (flatCoefficientBound 1)-
    r • commonSupportFullWeakEnergy a1 ha1 t) 0‖ ≤ weakFullDerivativeBudget*q
  weak : ‖fderiv ℝ (fun t => commonSupportWeakEnergy a ha t-
    nativeCoefficientWeakEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
    r • commonSupportWeakEnergy a1 ha1 t) 0‖ ≤ weakFullDerivativeBudget*q
  zeroWeak : ‖fderiv ℝ (fun t => commonSupportZeroWeakEnergy a ha t-
    nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)-
    r • commonSupportZeroWeakEnergy a1 ha1 t) 0‖ ≤ weakFullDerivativeBudget*q
  normal : ‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)-
    ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-
    r • negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t)) 0‖ ≤
      boundaryHalfDerivativeBudget*(36*q)
  tangent : ∀ j : I,‖fderiv ℝ (fun t => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)) 0‖ ≤
    boundaryHalfDerivativeBudget*(78*q)

/-- Quadratic native derivatives of the SAME affine coefficient residual
    give all Taylor derivative inputs for the Poisson and low radial clients. -/
theorem commonSupport_taylor_derivative_bounds_of_residual
    (a a1 aD : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r q : ℝ) (F0 : SmoothCoefficientMatrix 2)
    (hField : ∀ p,aD p = a p-r • a1 p)
    (hND : CommonSupportNativeDerivativeBounds aD haD SD hSD hzD q)
    (V : Set ℝ) (hV : IsOpen V) (h0V : (0:ℝ) ∈ V) (s : ℝ → X → ℝ)
    (hScalar : ∀ t ∈ V,∀ w : UnitSphere,a1 (t,w.val) = s t w.val • (1:Mat)) :
    CommonSupportTaylorDerivativeBounds a a1 ha ha1 S S1 hS hS1 hz hz1 r F0 q := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
  have hOps := commonSupport_operator_sub_smul_families a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField
  have hAffine (p) (z) (_ : z ∈ (ballOpens:Set X)) : a (p,z) = (0:ℝ) • (1:Mat)+r • a1 (p,z)+aD (p,z) := by
    rw [hField];module
  have hWeak := commonSupport_weakEnergy_affine_families a a1 aD ha ha1 haD 0 r hAffine
  have hRearrange {E : Type} [AddCommGroup E] [Module ℝ E] (A A1 D : E) (h : A-r • A1 = D) :
      A = 0+r • A1+D := by rw [← h];module
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [fderiv_affine_taylor_family_eq
      (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t))
      (fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t))
      (fun t => strongDirichletOperator fixedSobolevCalculus 0 (FD t))
      0 (strongDirichletOperator fixedSobolevCalculus 0 F0) r (0:ℝ) (fun t => hRearrange _ _ _ (hOps.1 t))]
    exact hND.strong
  · rw [fderiv_affine_taylor_family_eq
      (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F t))
      (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t))
      (fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (FD t))
      0 (fullCoefficientOperatorL fixedSobolevCalculus 0 F0) r (0:ℝ) (fun t => hRearrange _ _ _ (hOps.2.1 t))]
    exact hND.full
  · rw [fderiv_affine_taylor_family_eq _ _ _ _ _ r 0 hWeak.1]
    exact hND.fullWeak
  · rw [fderiv_affine_taylor_family_eq _ _ _ _ _ r 0 hWeak.2.1]
    exact hND.weak
  · rw [fderiv_affine_taylor_family_eq _ _ _ _ _ r 0 hWeak.2.2]
    exact hND.zeroWeak
  · rw [fderiv_affine_taylor_family_eq
      (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t))
      (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t))
      (fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily aD haD SD hSD hzD t))
      0 (ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) r (0:ℝ) (fun t => hRearrange _ _ _ (hOps.2.2.1 t))]
    exact hND.normal
  · intro j
    have hT1 (t : ℝ) (ht : t ∈ V) : negativeBoundaryCoefficientMulL
        (tangentCoefficientJetsFamily a1 ha1 S1 hS1 hz1 j t) = 0 := by
      rw [commonSupport_negative_tangent_multiplier_eq]
      apply negativeTangentCoefficient_scalar_zero (F1 t) (s t)
      intro w
      change coefficientMatrixField 2 (F1 t) w.val = _
      rw [coefficientMatrixField_commonSupportMatrixFamily]
      exact hScalar t ht w
    have hNear : (fun t => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)) =ᶠ[𝓝 0]
        (fun t => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily aD haD SD hSD hzD j t)) := by
      filter_upwards [hV.mem_nhds h0V] with t ht
      have hZero := congrArg (fun B : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
        negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)-r • B) (hT1 t ht)
      have hSame : negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)-
          r • negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a1 ha1 S1 hS1 hz1 j t) =
          negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t) :=
        hZero.trans (by simp only [smul_zero,sub_zero])
      exact hSame.symm.trans (hOps.2.2.2 j t)
    rw [hNear.fderiv_eq]
    exact hND.tangent j

end ShrinkingSpheres
