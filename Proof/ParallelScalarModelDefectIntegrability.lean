import Proof.ParallelScalarModelHalfIdentity
import Proof.ParallelScalarModelIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

/-- The complete scalar defect/model-adjoint pairing is qualitatively
integrable on the actual supported core before its beta-weighted bound. -/
theorem scalarModelDefectPairDensity_integrableOn {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (scalarModelDefectPairDensity d U) Y := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let V := fiveHalfToTwoSection U
  let F0 := scalarCovariantAdjointDefectSection d (metricDensity d.γ) A V
  let M0 := fun x => modelLoweringSection d V x-modelAdjointDefectSection d V x
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hV : ContDiff ℝ ∞ V := (sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU
  have hV0 (x : X) (hx : x ∉ S) : V x=0 := by simp only [V,fiveHalfToTwoSection,hU0 x hx,map_zero]
  have hF0 := contDiff_supported_scalarCovariantAdjointDefectSection hY d hg hK he
    (metricDensity d.γ) (hg.contDiffOn_density hK) (fun x hx => (metricDensity_pos hg hK hx).ne') A
    (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK) V hV S hS.isClosed hSY hV0
  have hLog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hModels := contDiff_supported_modelCovariantSections hY d hg hK he hLog V hV S hS.isClosed hSY hV0
  have hM0 : ContDiff ℝ ∞ M0 := hModels.2.1.sub hModels.2.2
  have hM00 (x : X) (hx : x ∉ S) : M0 x=0 := by
    have hh := modelCovariantSections_zero_off d V S hS.isClosed hV0 x hx
    exact sub_eq_zero.mpr (hh.2.1.trans hh.2.2.symm)
  have hInt := OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) (metricDensity d.γ)
    F0 M0 (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev 0)) S hS
    (fun x hx => (hg.contDiffOn_density hK).contDiffAt (hY.mem_nhds (hSY hx))) hF0.1 hM0 hM00
    (fun _ _ => contDiffAt_const)
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  have hRep (x : X) : scalarModelDefectPairDensity d U x=metricDensity d.γ x*⟪F0 x,M0 x⟫_ℝ := by
    have hAdj := scalar_model_corrected_lowering_weak_graph Q hQ d U x (hU.differentiable (by simp) x)
    rw [scalarModelDefectPairDensity,← hAdj,sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num),
      scalarFiveHalfDefectSection_inclusion d _ A U hU x]
  rw [show scalarModelDefectPairDensity d U=(fun x => metricDensity d.γ x*⟪F0 x,M0 x⟫_ℝ) from funext hRep]
  exact hInt.integrableOn

end ShrinkingSpheres.ParallelEnergy
