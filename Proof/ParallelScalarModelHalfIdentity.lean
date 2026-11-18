import Proof.ParallelScalarModelWeakSections
import Proof.ParallelScalarFirstBalancedIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

def scalarModelHalfCorrectedDensity (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius;
  let S := scalarFiveHalfSecondSection d A U y;
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) A U y;
  4*metricDensity d.γ y*(sphereSobolevDualPairing (1/2:ℝ) S (scalarModelForwardWeakSection d U y)-
    sphereSobolevDualPairing (1/2:ℝ) (S+F) (scalarModelAdjointWeakSection d U y))

def scalarModelDefectPairDensity (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
    (scalarFiveHalfDefectSection d (metricDensity d.γ) (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y)
    (scalarModelAdjointWeakSection d U y)

/-- Exact balanced realization of the literal corrected model/scalar
pair, retaining both the model defect and the physical scalar transpose. -/
theorem scalarModelCorrectedDensity_half_eq {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) {y : X} (hy : y ∈ Y) :
    scalarModelCorrectedDensity d U y=scalarModelHalfCorrectedDensity d U y := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let S := scalarFiveHalfSecondSection d A U y
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) A U y
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hU2 : ContDiff ℝ ∞ (fiveHalfToTwoSection U) :=
    (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hS : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) S=
      scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y :=
    scalarFiveHalfSecondSection_inclusion hY d hg hK he A U hU hy
  have hTranspose := scalarCovariantSecondTransposeSection_eq_add_defect hY d hg hK he
    (metricDensity d.γ) (hg.contDiffOn_density hK) A
    (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK)
    (fun x hx => (hd.principal_properties hK (hSub hx)).1.isHermitian.smul (by simp [isSelfAdjoint_iff]))
    (fiveHalfToTwoSection U) hU2.contDiffOn hy (metricDensity_pos hg hK hy).ne'
  have hSF : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (S+F)=
      scalarCovariantSecondTransposeSection d (metricDensity d.γ) A (fiveHalfToTwoSection U) y := by
    rw [map_add,hS,scalarFiveHalfDefectSection_inclusion d _ A U hU y]
    exact hTranspose.symm
  have hForward := scalar_model_raising_weak_graph d U y (hU.differentiable (by simp) y)
  have hAdjoint := scalar_model_corrected_lowering_weak_graph Q hQ d U y (hU.differentiable (by simp) y)
  have hPair (s : SphereSobolev (1/2:ℝ)) (z : SphereSobolev 0) :
      ⟪z,sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) s⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ) s (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) z) := by
    rw [sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),real_inner_comm]
  change 4*metricDensity d.γ y*(⟪modelRaisingSection d (fiveHalfToTwoSection U) y,
      scalarCovariantSecondSection d A (fiveHalfToTwoSection U) y⟫_ℝ-
    ⟪modelLoweringSection d (fiveHalfToTwoSection U) y-modelAdjointDefectSection d (fiveHalfToTwoSection U) y,
      scalarCovariantSecondTransposeSection d (metricDensity d.γ) A (fiveHalfToTwoSection U) y⟫_ℝ)=_
  rw [← hS,← hSF,hPair,hPair,hForward,hAdjoint]
  rfl

end ShrinkingSpheres.ParallelEnergy
