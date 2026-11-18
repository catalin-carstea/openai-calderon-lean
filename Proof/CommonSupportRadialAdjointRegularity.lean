import Proof.CommonSupportBoundaryOperatorRegularity
import Proof.RadialConormalReconstruction
import Proof.Archive.BanachInverseFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Reconstruct the conormal from a full radial response, then take its
    physical adjoint using the actual normal reciprocal and tangent adjoint. -/
def radialAdjointFromResponseL (F : SmoothCoefficientMatrix 2)
    (D : SphereSobolev 1 →L[ℝ] SphereSobolev 0) : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  conormalRadialAdjointL F
    ((coarseSphereScalarMulL (smoothSphereValue (coefficientSmoothData (normalCoefficientJet F)))).comp D+
      coarseBoundaryTangentialL (fun j => tangentCoefficientJet F j))

theorem radialAdjointFromResponseL_pairing (F : SmoothCoefficientMatrix 2)
    (D N : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hD : D = conormalRadialL F N)
    (hPos : ∀ w : UnitSphere,0 < coefficientValue 2 (normalCoefficientJet F) w.val)
    (hN : ∀ u v,⟪N u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,N v⟫_ℝ) :
    ∀ u v,⟪D u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,radialAdjointFromResponseL F D v⟫_ℝ := by
  rw [hD]
  unfold radialAdjointFromResponseL
  rw [conormal_reconstruct_from_radial F N hPos]
  apply conormalRadialL_adjoint F N
  · intro w
    exact (congrArg (fun f : X → ℝ => 0 < f w.val) (coefficientValue_normalCoefficientJet F)).mp (hPos w)
  · exact hN

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem contDiffOn_commonSupport_radialAdjointFromResponse
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (S : Set X) (hS : IsCompact S)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0)
    (D : P → SphereSobolev 1 →L[ℝ] SphereSobolev 0) (V : Set P) (hD : ContDiffOn ℝ ∞ D V)
    (hInv : ∀ p ∈ V,(oneBoundaryCoefficientMulL
      (normalCoefficientJet (commonSupportMatrixFamily 2 a ha S hS hz p))).IsInvertible) :
    ContDiffOn ℝ ∞ (fun p => radialAdjointFromResponseL (commonSupportMatrixFamily 2 a ha S hS hz p) (D p)) V := by
  have hC := (contDiff_commonSupport_coarseNormalMul a ha S hS hz).contDiffOn (s:=V)
  have hT := (contDiff_commonSupport_coarseBoundaryTangential a ha S hS hz).contDiffOn (s:=V)
  have hTd := (contDiff_commonSupport_adjointBoundaryTangential a ha S hS hz).contDiffOn (s:=V)
  have hM := (contDiff_commonSupport_oneNormalMul a ha S hS hz).contDiffOn (s:=V)
  have hMI := contDiffOn_banachInverseFamily _ V hM hInv
  exact (((hC.clm_comp hD).add hT).sub hTd).clm_comp hMI

end ShrinkingSpheres
