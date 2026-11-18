import Proof.CommonSupportAffineCoefficient
import Proof.BoundaryAffineCoefficient
import Proof.BoundaryTaylorIdentity
import Proof.CommonSupportLowRadialRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

/-- Actual raw affine coefficient families have exactly the same strong,
    full and boundary affine identities, independent of exterior cutoffs. -/
theorem commonSupport_operator_sub_smul_families
    (a a1 aD : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ)
    (hField : ∀ p,aD p = a p-r • a1 p) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
    (∀ t,strongDirichletOperator fixedSobolevCalculus 0 (F t)-
      r • strongDirichletOperator fixedSobolevCalculus 0 (F1 t) = strongDirichletOperator fixedSobolevCalculus 0 (FD t)) ∧
    (∀ t,fullCoefficientOperatorL fixedSobolevCalculus 0 (F t)-
      r • fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t) = fullCoefficientOperatorL fixedSobolevCalculus 0 (FD t)) ∧
    (∀ t,negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)-
      r • negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t) =
        negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily aD haD SD hSD hzD t)) ∧
    ∀ j t,negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)-
      r • negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a1 ha1 S1 hS1 hz1 j t) =
        negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily aD haD SD hSD hzD j t) := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
  have hCoeff := commonSupport_matrix_sub_smul_field a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    have h := strongDirichletOperator_congr_on_ball fixedSobolevCalculus 0 (F t-r • F1 t) (FD t) (fun z _ => hCoeff t z)
    change (strongCoefficientOperatorL fixedSobolevCalculus 0) (F t-r • F1 t) = _ at h
    rw [(strongCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
      (strongCoefficientOperatorL fixedSobolevCalculus 0).map_smul] at h
    exact h
  · intro t
    have h := fullCoefficientOperator_congr_on_ball fixedSobolevCalculus 0 (F t-r • F1 t) (FD t) (fun z _ => hCoeff t z)
    rw [(fullCoefficientOperatorL fixedSobolevCalculus 0).map_sub,
      (fullCoefficientOperatorL fixedSobolevCalculus 0).map_smul] at h
    exact h
  · intro t
    rw [commonSupport_negative_normal_multiplier_eq,commonSupport_negative_normal_multiplier_eq,
      commonSupport_negative_normal_multiplier_eq]
    have h := negativeBoundaryCoefficientMulL_congr_sphere (normalCoefficientJet (F t-r • F1 t))
      (normalCoefficientJet (FD t)) (normalCoefficientJet_value_congr_sphere _ _ (fun w => hCoeff t w.val))
    rw [negativeNormalCoefficient_sub_smul] at h
    exact h
  · intro j t
    rw [commonSupport_negative_tangent_multiplier_eq,commonSupport_negative_tangent_multiplier_eq,
      commonSupport_negative_tangent_multiplier_eq]
    have h := negativeBoundaryCoefficientMulL_congr_sphere (tangentCoefficientJet (F t-r • F1 t) j)
      (tangentCoefficientJet (FD t) j) (tangentCoefficientJet_value_congr_sphere _ _ (fun w => hCoeff t w.val) j)
    rw [negativeTangentCoefficient_sub_smul] at h
    exact h

end ShrinkingSpheres
