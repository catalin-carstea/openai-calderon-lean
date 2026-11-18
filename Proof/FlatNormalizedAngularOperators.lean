import Proof.FlatRaisingCancellation
import Proof.Archive.BoundedAngularShift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.AngularShiftGraph
open OAI.AnisotropicCalderon.SpectralWeightedGraph OAI.AnisotropicCalderon.SpectralCoreRegularity
open OAI.AnisotropicCalderon.BoundedAngularShift

theorem sphereHarmonicCoordinate_zeroEquiv_symm (k : ℕ) (v : SphereSobolev 0) :
    sphereHarmonicCoordinate orthogonalSphereHarmonics denseSphereHarmonics k
      ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm v) =
        sphereSobolevCoefficientL 0 k v := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have h := sphereSobolevCoefficientL_zeroEquiv orthogonalSphereHarmonics denseSphereHarmonics k (Z.symm v)
  rw [Z.apply_symm_apply] at h
  exact h.symm

theorem sphereSobolev_one_physical_besselGraph (u : SphereSobolev 1) :
    ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) u),
      (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
        (sphereSobolevBesselEquiv 1 1 u)) ∈
      sphereBesselGraph orthogonalSphereHarmonics denseSphereHarmonics 1 := by
  intro k
  rw [sphereHarmonicCoordinate_zeroEquiv_symm,sphereHarmonicCoordinate_zeroEquiv_symm,
    sphereSobolevCoefficientL_inclusion]
  have hOrder : sphereSobolevCoefficientL 0 k (sphereSobolevBesselEquiv 1 1 u) =
      sphereSobolevCoefficientL ((1:ℝ)-1) k (sphereSobolevBesselEquiv 1 1 u) :=
    congrArg (fun s : ℝ => sphereSobolevCoefficientL s k (sphereSobolevBesselEquiv 1 1 u))
      (sub_self (1:ℝ)).symm
  exact hOrder.trans (sphereSobolevCoefficientL_besselEquiv 1 1 k u)

/-- Exact bounded-operator realization of the flat lowering action. -/
theorem coordinateBoundaryGradientL_normalized (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u : SphereSobolev 1) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (boundaryGradientL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u) =
        normalizedDerivative sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevBesselEquiv 1 1 u)) :=
  sphereDerivativeGraph_output_unique sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
    _ _ _ (coordinateBoundaryGradientL_graph Q hQ i u)
      (normalizedDerivative_graph _ _ _ i _ _ (sphereSobolev_one_physical_besselGraph u))

/-- Exact bounded-operator realization of the actual flat L2 adjoint. -/
theorem coordinateBoundaryGradientAdjointL_normalized (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (u : SphereSobolev 1) :
    (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u) =
        normalizedRaising sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
          ((sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
            (sphereSobolevBesselEquiv 1 1 u)) :=
  sphereRaisingGraph_output_unique sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i
    _ _ _ (coordinateBoundaryGradientAdjointL_graph Q hQ i u)
      (normalizedRaising_graph _ _ _ i _ _ (sphereSobolev_one_physical_besselGraph u))

/-- The leading contracted second adjoint vanishes whenever the first outputs
    lie in H1. The shared intermediate witnesses are explicit. -/
theorem coordinateBoundaryGradientAdjointL_contracted_double_zero (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (u : SphereSobolev 1) (v : I → SphereSobolev 1)
    (hv : ∀ i,sphereSobolevInclusionL 1 0 (by norm_num) (v i) =
      boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u) :
    (∑ i : I,boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL (v i)) = 0 := by
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  have hFirst (i : I) := coordinateBoundaryGradientAdjointL_graph Q hQ i u
  have hSecond (i : I) := coordinateBoundaryGradientAdjointL_graph Q hQ i (v i)
  have hSecond' (i : I) :
      (Z.symm (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL u),
        Z.symm (boundaryGradientAdjointL (coordinateBoundaryCoefficients Q i) sphereSobolevDegreeL (v i))) ∈
      sphereRaisingGraph sphereFischerInner orthogonalSphereHarmonics denseSphereHarmonics i := by
    have hHere := hSecond i
    rw [hv i] at hHere
    exact hHere
  have h := sphereRaisingGraph_contracted_double_zero _ _ _ hFirst hSecond'
  apply Z.symm.injective
  exact (map_sum Z.symm _ _).trans (h.trans Z.symm.map_zero.symm)

end ShrinkingSpheres
