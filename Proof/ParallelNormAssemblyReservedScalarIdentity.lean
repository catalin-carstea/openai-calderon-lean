import Proof.ParallelNormAssemblyReservedScalarDefectDefinition
import Proof.ParallelNormAssemblyReservedScalarGreen
import Proof.ParallelNormAssemblyReservedScalarWeights
import Proof.ParallelNormAssemblyReservedQuadraticSkew
import Proof.ParallelNormAssemblyReservedAdjointWeakGraph
import Proof.ParallelNormAssemblyReservedModelPairTrace
import Proof.ParallelScalarFirstHighSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

lemma scalar_potential_second_pair_trace (d : Data)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
      (scalarFiveHalfSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y)
      (C y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)))=
    scalarQuadraticSecondDensity d (scalarPotentialWeight d) C
      (fun b x => fiveHalfSectionCovariantDerivativeL d U x (axis b)) U y := by
  have hH (b : I) : (fun x => fiveHalfSectionCovariantDerivativeL d U x (axis b))=
      fiveHalfCovariantDerivative d U (axis b) :=
    funext (fun x => (five_half_covariant_derivative_reserved_eq d U x (axis b)).symm)
  simp only [scalarQuadraticSecondDensity,hH,scalarFiveHalfSecondSection,sphereSobolevDualPairing,
    sum_inner,real_inner_smul_left,Finset.mul_sum,scalarPotentialWeight]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Exact raw scalar/potential split into the symmetric scalar/skew
quadratic Green density and the independent actual transpose defect.
Both original orientations, the SAME W and factor two are preserved. -/
theorem component_scalar_potential_leading_weak_eq {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε CF CT CB CS CG CK CN CJ : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (A : PotentialAdjointFirstJetPacket P ε CN CJ)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (T L : X → SphereL2) {y : X} (hy : y ∈ Y) :
    componentSectorDensity P WF W U T L 4 y+scalarPotentialDefectCoreDensity P W U y=
      2*scalarQuadraticSecondDensity d (scalarPotentialWeight d)
        (fun x => P.potentialQuadraticHalfL x-A.weak x)
        (fun b x => fiveHalfSectionCovariantDerivativeL d U x (axis b)) U y := by
  let S := scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U) y
  let F := scalarCovariantAdjointDefectSection d (metricDensity d.γ)
    (scalarPrincipalMatrix d.γ d.g₂ d.radius) (fiveHalfToTwoSection U) y
  let SH := scalarFiveHalfSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  let V := P.potentialQuadraticCoreSection W U y
  let VA := P.potentialQuadraticAdjointCoreSection W U y
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hSym (x : X) (hx : x ∈ Y) : (scalarPrincipalMatrix d.γ d.g₂ d.radius x).IsHermitian :=
    (hd.principal_properties hK (hSub hx)).1.isHermitian.smul (by simp [isSelfAdjoint_iff])
  have hTranspose := scalarCovariantSecondTransposeSection_eq_add_defect hY d hg hK he
    (metricDensity d.γ) (hg.contDiffOn_density hK) (scalarPrincipalMatrix d.γ d.g₂ d.radius)
    (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK) hSym (fiveHalfToTwoSection U)
    (show ContDiffOn ℝ ∞ (fiveHalfToTwoSection U) Y from
      ((sphereSobolevInclusionL (5/2:ℝ) 2 (by norm_num)).contDiff.comp hU).contDiffOn)
    hy (metricDensity_pos hg hK hy).ne'
  have hS : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) SH=S :=
    scalarFiveHalfSecondSection_inclusion hY d hg hK he _ U hU hy
  have hV : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) V=P.potentialQuadraticHalfL y u := by
    simp only [V,PhysicalPrincipalData.potentialQuadraticCoreSection,dite_eq_left hy]
    exact P.potentialQuadraticCoreL_balanced hy (W y hy) (U y)
  have hVA : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num) VA=A.weak y u :=
    (actual_potential_adjoint_section_weak_graph P W U hy).trans (A.actual_graph CG CK y hy (W y hy) u)
  have hPF : ⟪S,V⟫_ℝ=sphereSobolevDualPairing (1/2:ℝ) SH (P.potentialQuadraticHalfL y u) := by
    rw [←hS,←hV]
    exact (sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) SH V).symm
  have hPA : ⟪S,VA⟫_ℝ=sphereSobolevDualPairing (1/2:ℝ) SH (A.weak y u) := by
    rw [←hS,←hVA]
    exact (sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) SH VA).symm
  have hSplit : componentSectorDensity P WF W U T L 4 y+scalarPotentialDefectCoreDensity P W U y=
      2*metricDensity d.γ y*(⟪S,V⟫_ℝ-⟪S,VA⟫_ℝ) := by
    simp only [componentSectorDensity,weightedSquareSector,componentForwardOutputs,componentAdjointOutputs,
      scalarPotentialDefectCoreDensity,hTranspose,inner_add_left]
    change 2*metricDensity d.γ y*(⟪S,V⟫_ℝ-(⟪S,VA⟫_ℝ+⟪F,VA⟫_ℝ))+
      2*metricDensity d.γ y*⟪F,VA⟫_ℝ=_
    ring
  rw [hSplit,hPF,hPA]
  have hTrace := scalar_potential_second_pair_trace d (fun x => P.potentialQuadraticHalfL x-A.weak x) U y
  rw [←hTrace]
  simp only [_root_.sub_apply,sphereSobolevDualPairing,inner_sub_right,SH,u]
  ring

end ShrinkingSpheres.ParallelEnergy
