import Proof.PhysicalPotentialRemainderCoarse
import Proof.PhysicalPrincipalResidual
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

lemma potentialRemainderCoarseL_actual (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (u : SphereSobolev 2) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.potentialRemainderCoarseL y (sphereSobolevInclusionL 2 1 (by norm_num) u))=
    P.potentialRemainderHalfL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u) := by
  have h := DFunLike.congr_fun (P.potentialRemainderCoarseL_balanced hy)
    (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)
  simpa only [balancedCoarsePotentialL,ContinuousLinearMap.comp_apply,
    sphereSobolevInclusionL_trans_apply] using h

def truncatedResidualValue (P : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev 2) (y : X) : SphereSobolev (-(1/2:ℝ)) :=
  P.residualValue U y-sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (P.potentialRemainderCoarseL y (sphereSobolevInclusionL 2 1 (by norm_num) (U y)))

/-- Exact truncated physical normal form. Only the complementary output is
subtracted: the scalar second-base, full first-base and ALL quadratic words
are retained with the original physical witnesses. -/
lemma truncatedResidualValue_balanced_normal_form (P : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev 2) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    P.truncatedResidualValue U y=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
          highSectionCovariantHessian d U y i j))+
      (∑ j : I,P.firstDerivativeHalfL y j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d U y (d.frame y j))))+
      P.potentialQuadraticHalfL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)) := by
  rw [truncatedResidualValue,P.residualValue_balanced_normal_form U hy he,
    P.remainingPotentialHalfL_quadratic_remainder,P.potentialRemainderCoarseL_actual hy]
  simp only [_root_.add_apply]
  abel

/-- The SAME physical second-trace realization yields the actual truncated
residual, with no missing potential group and no identification by equality
of Sobolev carrier types. -/
theorem canonical_principal_truncated_residual (P : PhysicalPrincipalData Y d CF CT)
    {Ω : Set X} (hY : IsOpen Y) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {φ : Field} (hφ : Test Y d.γ d.frame φ)
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (L : ℂ →L[ℝ] ℝ)
    (C : AngularComponentData E d.radius L) :
    let F := fun p => L (E.representative p)
    let hF : ContDiff ℝ ∞ F := L.contDiff.comp E.representativeSmooth
    let U := ambientSobolevSection 2 (by norm_num) F hF
    ∃ S : SecondTraceSectionOutput Y d P.adjoint P.center P.tensor φ L F hF,
      ∀ y ∈ Y,sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (expandedPrincipalSection d P.adjoint P.center P.tensor U
          (fun j => ambientSobolevSection 1 (by norm_num) (S.representative j) (S.smooth j)) y-
          (2:ℝ) • sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (C.raisingOutput y)-
          firstCorrectionCrossRemainderL Q d y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))-
          P.potentialRemainderCoarseL y (sphereSobolevInclusionL 2 1 (by norm_num) (U y)))=
        P.truncatedResidualValue U y := by
  obtain ⟨S,hS⟩ := P.canonical_principal_residual hY hd hK Q hQ hφ E L C
  refine ⟨S,?_⟩
  intro y hy
  rw [map_sub,hS y hy]
  rfl
end PhysicalPrincipalData
end ShrinkingSpheres
