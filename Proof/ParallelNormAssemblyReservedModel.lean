import Proof.ParallelNormAssemblyReservedReduction
import Proof.ConstantBoundaryCoefficients

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

/-- The chosen five-half defect source has precisely the actual coarse
model-defect output, by the genuine model-defect inclusion square. -/
lemma componentDefectSource_zero (d : Data) (G : X × X → ℝ) (hG : ContDiff ℝ ∞ G) (y : X) :
    sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (componentDefectSource d G hG y)=
      modelAdjointDefectSection d (ambientSobolevSection 2 (by norm_num) G hG) y := by
  have hI : sphereSobolevInclusionL ((7/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  have hh := DFunLike.congr_fun (modelAdjointDefectSobolevL_inclusion (7/2:ℝ) 1 (by norm_num) d y)
    (ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG y)
  simp only [ContinuousLinearMap.comp_apply,hI,
    ambientHigherSobolevSection_inclusion (7/2:ℝ) 1 (by norm_num) (by norm_num) (by norm_num)] at hh
  change sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num)
      (modelAdjointDefectSobolevL (7/2:ℝ) d y (ambientHigherSobolevSection (7/2:ℝ) (by norm_num) G hG y))=_
  rw [← hh]
  unfold modelAdjointDefectSection modelAdjointDefectSobolevL
  simp only [_root_.sum_apply,_root_.smul_apply,
    ambientSobolevSection_inclusion 2 1 (by norm_num) (by norm_num) (by norm_num)]

/-- On the actual selected angular model, lowering minus the SAME defect
is literally the genuine physically weighted model-adjoint section. -/
lemma corrected_lowering_output_eq {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (L : ℂ →L[ℝ] ℝ)
    (C : AngularComponentData E d.radius L) (hφ : smoothNear φ (bundle Y d.γ))
    {y : X} (hy : y ∈ Y) :
    let G := fun p => L (E.representative p)
    let hG := L.contDiff.comp E.representativeSmooth
    let U := ambientSobolevSection 2 (by norm_num) G hG
    sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (C.loweringOutput y)-
      sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (componentDefectSource d G hG y)=
      modelLoweringSection d U y-modelAdjointDefectSection d U y := by
  dsimp only
  rw [componentDefectSource_zero]
  congr 1
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hFrame (x : X) (hx : x ∈ Y) := hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hh := congrArg (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics)
    (C.canonical_lowering_section_eq hY hg hK he hFrame hφ Q hQ hy)
  simpa only [LinearIsometryEquiv.apply_symm_apply,modelLoweringSection] using hh.symm

end ShrinkingSpheres.ParallelEnergy
