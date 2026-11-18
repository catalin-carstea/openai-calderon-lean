import Proof.BoundaryMultiplierFamilyRegularity
import Proof.BoundaryAngularAdjoint
import Proof.Archive.NativeBoundaryCoefficientFamilies

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma commonSupport_normal_sphereValue
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (p : P) (w : UnitSphere) :
    coefficientValue 2 (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p)) w.val =
      normalCoefficientFunction a (p,w.val) := by
  rw [coefficientValue_normalCoefficientJet]
  change (∑ i : I,∑ j : I,w.val i*coefficientMatrixField 2
    (commonSupportMatrixFamily 2 a ha S hS hz p) w.val i j*w.val j) = _
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  rfl

lemma commonSupport_tangent_sphereValue
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (j : I) (p : P) (w : UnitSphere) :
    coefficientValue 2 (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j) w.val =
      tangentCoefficientFunction a j (p,w.val) := by
  rw [coefficientValue_tangentCoefficientJet]
  change (∑ i : I,w.val i*coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz p) w.val i j)-
    (∑ i : I,∑ k : I,w.val i*coefficientMatrixField 2
      (commonSupportMatrixFamily 2 a ha S hS hz p) w.val i k*w.val k)*w.val j = _
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  rfl

theorem contDiff_commonSupport_coarseNormalMul
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))))) := by
  have hSmooth := contDiff_coarseSphereScalarMulL_joint (normalCoefficientFunction a)
    (contDiff_normalCoefficientFunction a ha)
  have hEq (p : P) : smoothSphereValue (coefficientSmoothData
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))) =
      (⟨fun w : UnitSphere => normalCoefficientFunction a (p,w.val),
        (contDiff_normalCoefficientFunction a ha).continuous.comp
          (continuous_const.prodMk continuous_subtype_val)⟩ : C(UnitSphere,ℝ)) := by
    ext w
    exact commonSupport_normal_sphereValue a ha S hS hz p w
  simpa only [← hEq] using hSmooth

theorem contDiff_commonSupport_coarseTangentMul
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (j : I) :
    ContDiff ℝ ∞ (fun p => coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData
      (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j)))) := by
  have hSmooth := contDiff_coarseSphereScalarMulL_joint (tangentCoefficientFunction a j)
    (contDiff_tangentCoefficientFunction a ha j)
  have hEq (p : P) : smoothSphereValue (coefficientSmoothData
      (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j)) =
      (⟨fun w : UnitSphere => tangentCoefficientFunction a j (p,w.val),
        (contDiff_tangentCoefficientFunction a ha j).continuous.comp
          (continuous_const.prodMk continuous_subtype_val)⟩ : C(UnitSphere,ℝ)) := by
    ext w
    exact commonSupport_tangent_sphereValue a ha S hS hz j p w
  simpa only [← hEq] using hSmooth

theorem contDiff_commonSupport_oneNormalMul
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => oneBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))) := by
  have hSmooth := contDiff_oneBoundaryCoefficientMulL_commonSupport (normalCoefficientFunction a)
    (contDiff_normalCoefficientFunction a ha) S hS (normalCoefficientFunction_support a S hz)
  have hEq (p : P) : oneBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p)) =
      oneBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p) := by
    apply oneBoundaryCoefficientMulL_congr_sphere
    intro w
    exact (commonSupport_normal_sphereValue a ha S hS hz p w).trans
      (coefficientValue_commonSupportCoefficientFamily 2 (normalCoefficientFunction a)
        (contDiff_normalCoefficientFunction a ha) S hS (normalCoefficientFunction_support a S hz) p w.val).symm
  have hFun := funext hEq
  rw [hFun]
  exact hSmooth

theorem contDiff_commonSupport_oneTangentMul
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (j : I) :
    ContDiff ℝ ∞ (fun p => oneBoundaryCoefficientMulL
      (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j)) := by
  have hSmooth := contDiff_oneBoundaryCoefficientMulL_commonSupport (tangentCoefficientFunction a j)
    (contDiff_tangentCoefficientFunction a ha j) S hS (tangentCoefficientFunction_support a S hz j)
  have hEq (p : P) : oneBoundaryCoefficientMulL
      (tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j) =
      oneBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j p) := by
    apply oneBoundaryCoefficientMulL_congr_sphere
    intro w
    exact (commonSupport_tangent_sphereValue a ha S hS hz j p w).trans
      (coefficientValue_commonSupportCoefficientFamily 2 (tangentCoefficientFunction a j)
        (contDiff_tangentCoefficientFunction a ha j) S hS (tangentCoefficientFunction_support a S hz j) p w.val).symm
  have hFun := funext hEq
  rw [hFun]
  exact hSmooth

theorem contDiff_commonSupport_coarseBoundaryTangential
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => coarseBoundaryTangentialL
      (fun j => tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j)) := by
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro i _
  exact (contDiff_commonSupport_coarseTangentMul a ha S hS hz j).clm_comp contDiff_const

theorem contDiff_commonSupport_adjointBoundaryTangential
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => adjointBoundaryTangentialL
      (fun j => tangentCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p) j)) := by
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro i _
  exact (contDiff_const.clm_comp
    (contDiff_const.clm_comp (contDiff_commonSupport_oneTangentMul a ha S hS hz j))).neg

end ShrinkingSpheres
