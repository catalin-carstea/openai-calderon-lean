import Proof.CoarseOneBoundaryAffine
import Proof.CommonSupportAffineCoefficient
import Proof.RadialAdjointCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

theorem commonSupport_coarse_one_sub_smul_families
    (a a1 aD : ℝ × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ)
    (hField : ∀ p,aD p = a p-r • a1 p) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
    (∀ t,coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F t))))-
      r • coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (F1 t)))) =
        coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet (FD t))))) ∧
    (∀ t,oneBoundaryCoefficientMulL (normalCoefficientJet (F t))-
      r • oneBoundaryCoefficientMulL (normalCoefficientJet (F1 t)) = oneBoundaryCoefficientMulL (normalCoefficientJet (FD t))) ∧
    (∀ t,coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j)-
      r • coarseBoundaryTangentialL (fun j => tangentCoefficientJet (F1 t) j) =
        coarseBoundaryTangentialL (fun j => tangentCoefficientJet (FD t) j)) ∧
    ∀ t,adjointBoundaryTangentialL (fun j => tangentCoefficientJet (F t) j)-
      r • adjointBoundaryTangentialL (fun j => tangentCoefficientJet (F1 t) j) =
        adjointBoundaryTangentialL (fun j => tangentCoefficientJet (FD t) j) := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let FD := commonSupportMatrixFamily 2 aD haD SD hSD hzD
  have hCoeff := commonSupport_matrix_sub_smul_field a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField
  have hOps (t : ℝ) := radial_boundary_operators_congr_sphere (F t-r • F1 t) (FD t) (fun w => hCoeff t w.val)
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    exact (coarseNormalCoefficient_sub_smul (F t) (F1 t) r).symm.trans (hOps t).1
  · intro t
    exact (oneNormalCoefficient_sub_smul (F t) (F1 t) r).symm.trans (hOps t).2.1
  · intro t
    exact (coarseBoundaryTangential_sub_smul (F t) (F1 t) r).symm.trans (hOps t).2.2.1
  · intro t
    exact (adjointBoundaryTangential_sub_smul (F t) (F1 t) r).symm.trans (hOps t).2.2.2

end ShrinkingSpheres
