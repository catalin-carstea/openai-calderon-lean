import Proof.ParallelNormAssemblyUniform
import Proof.UniformPhysicalModelDefectResidualIntegral
import Proof.ModelCovariantAdjunction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

/-- The SAME smooth actual model-adjoint-defect source, on the genuine
five-half common core; its two-inclusion is the existing ambient defect. -/
def componentDefectSource (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) : X → SphereSobolev (5/2:ℝ) :=
  ambientModelDefectFiveHalfSection d G hG

lemma defect_residual_real_form_eq_core (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (hV : ContDiff ℝ ∞ (componentDefectSource d G hG)) {y : X} (hy : y ∈ Y) :
    P.modelDefectResidualRealForm G hG y=
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num)
          (ambientHigherSobolevSection (5/2:ℝ) (by norm_num) G hG y),
        P.truncatedCovariantCoreSection W (componentDefectSource d G hG) y⟫_ℝ := by
  have hVtwo : fiveHalfToTwoSection (componentDefectSource d G hG)=ambientModelAdjointDefectSection d G hG :=
    funext (ambientModelDefectFiveHalfSection_two d G hG)
  have hCore := P.truncatedCovariantCoreSection_balanced hY hΩ hd hK W
    (componentDefectSource d G hG) hV hy
  rw [hVtwo] at hCore
  unfold PhysicalPrincipalData.modelDefectResidualRealForm
  rw [← hCore,sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)]
  congr 1
  rw [← ambientHigherSobolevSection_inclusion (5/2:ℝ) (1/2:ℝ)
    (by norm_num) (by norm_num) (by norm_num) G hG y,sphereSobolevInclusionL_trans_apply]

/-- The physical pairing of the model-adjoint defect against the complete
actual formal-adjoint residual. -/
def componentDefectAdjointPairing (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) : ℝ :=
  metricDensity d.γ y*
    ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (componentDefectSource d G hG y),
      P.truncatedFormalAdjointCore WF W
        (ambientHigherSobolevSection (5/2:ℝ) (by norm_num) G hG) y⟫_ℝ

/-- Exact physical adjunction identifies the defect pairing with the
already bounded SAME-residual/model-defect form. No formal unbounded
operator transpose or carrier-type identification is substituted. -/
theorem defect_pairing_integral_eq (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0 : ∀ y ∉ S,ambientSobolevSection 2 (by norm_num) G hG y=0) :
    IntegrableOn (componentDefectAdjointPairing P WF W G hG) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*P.modelDefectResidualRealForm G hG y) Y ∧
    (∫ y in Y,componentDefectAdjointPairing P WF W G hG y)=
      ∫ y in Y,metricDensity d.γ y*P.modelDefectResidualRealForm G hG y := by
  let U := ambientHigherSobolevSection (5/2:ℝ) (by norm_num) G hG
  let V := componentDefectSource d G hG
  have hU : ContDiff ℝ ∞ U := contDiff_ambientHigherSobolevSection (5/2:ℝ) (by norm_num) G hG
  have h0U (y) (hy : y ∉ S) : U y=0 :=
    ambientHigherSobolevSection_zero_of_coarse (5/2:ℝ) 2 (by norm_num) (by norm_num) (by norm_num) G hG (h0 y hy)
  have he (i : I) : ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hlog : ContDiffOn ℝ ∞ (fun y => Real.log (d.radius y)) Y :=
    hd.2.2.2.2.1.1.log (fun y hy => (hd.2.2.2.2.1.2 y hy).1.ne')
  have hVS := contDiff_supported_ambientModelDefectFiveHalfSection hY d G hG hlog he S hS.isClosed hSY h0
  have hV : ContDiff ℝ ∞ V := hVS.1
  have h0V : ∀ y ∉ S,V y=0 := hVS.2
  have hGreen := P.truncatedCoreOperators_green hY hΩ hSub hd hK WF W hCG hCK U V hU hV S hS hSY h0U h0V
  have hEq : (fun y => metricDensity d.γ y*
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),P.truncatedCovariantCoreSection W V y⟫_ℝ)
      =ᵐ[volume.restrict Y] (fun y => metricDensity d.γ y*P.modelDefectResidualRealForm G hG y) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    exact congrArg (fun z => metricDensity d.γ y*z)
      (defect_residual_real_form_eq_core P hY hΩ hSub hd hK W G hG hV hy).symm
  refine ⟨hGreen.2.1,hGreen.1.congr hEq,?_⟩
  exact hGreen.2.2.symm.trans (integral_congr_ae hEq)

/-- Both real and imaginary actual defect/adjoint pairings. -/
def defectAdjointComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  componentDefectAdjointPairing P WF W (fun p => (E.representative p).re)
      (Complex.reCLM.contDiff.comp E.representativeSmooth) y+
  componentDefectAdjointPairing P WF W (fun p => (E.representative p).im)
      (Complex.imCLM.contDiff.comp E.representativeSmooth) y

theorem defect_complex_pairing_integral_eq (P : PhysicalPrincipalData Y d CF CT)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    IntegrableOn (defectAdjointComplexDensity P WF W E) Y ∧
      (∫ y in Y,defectAdjointComplexDensity P WF W E y)=∫ y in Y,P.modelDefectResidualDensity E y := by
  have hR := defect_pairing_integral_eq P hY hΩ hSub hd hK WF W hCG hCK
    (fun p => (E.representative p).re) (Complex.reCLM.contDiff.comp E.representativeSmooth)
    E.supportSet E.compactSupportSet E.supportSubset (fun _ hy => E.realSobolevSection_zero 2 (by norm_num) hy)
  have hI := defect_pairing_integral_eq P hY hΩ hSub hd hK WF W hCG hCK
    (fun p => (E.representative p).im) (Complex.imCLM.contDiff.comp E.representativeSmooth)
    E.supportSet E.compactSupportSet E.supportSubset (fun _ hy => E.imagSobolevSection_zero 2 (by norm_num) hy)
  refine ⟨hR.1.add hI.1,?_⟩
  unfold defectAdjointComplexDensity PhysicalPrincipalData.modelDefectResidualDensity
  simp only [mul_add]
  rw [integral_add hR.1 hI.1,integral_add hR.2.1 hI.2.1,hR.2.2,hI.2.2]

end ShrinkingSpheres.ParallelEnergy
