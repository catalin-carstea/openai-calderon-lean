import Proof.CoefficientOperatorLocality
import Proof.BoundaryAffineCoefficient
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

/-- A raw compact affine coefficient identity is inherited by every native
    jet representative, with no dependence on its support witness. -/
theorem commonSupport_matrix_sub_smul_field
    (a a1 aD : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ)
    (hField : ∀ p,aD p = a p-r • a1 p) :
    ∀ t z,coefficientMatrixField 2
      (commonSupportMatrixFamily 2 a ha S hS hz t-r • commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t) z =
        coefficientMatrixField 2 (commonSupportMatrixFamily 2 aD haD SD hSD hzD t) z := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
  have hA (t : ℝ) (z : X) : coefficientMatrixField 2 (F t) z = a (t,z) :=
    congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 a ha S hS hz t)
  have hA1 (t : ℝ) (z : X) : coefficientMatrixField 2 (F1 t) z = a1 (t,z) :=
    congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)
  have hAD (t : ℝ) (z : X) : coefficientMatrixField 2 (FD t) z = aD (t,z) :=
    congrArg (fun f : X → Mat => f z) (coefficientMatrixField_commonSupportMatrixFamily 2 aD haD SD hSD hzD t)
  have hCoeff (t : ℝ) (z : X) : coefficientMatrixField 2 (F t-r • F1 t) z = coefficientMatrixField 2 (FD t) z := by
    ext i j
    change coefficientValue 2 ((F t-r • F1 t) i j) z = _
    simp only [Pi.sub_apply,Pi.smul_apply,coefficientValue_sub_local,coefficientValue_smul]
    change coefficientMatrixField 2 (F t) z i j-r*coefficientMatrixField 2 (F1 t) z i j = coefficientMatrixField 2 (FD t) z i j
    rw [hA,hA1,hAD,hField]
    rfl
  exact hCoeff

end ShrinkingSpheres
