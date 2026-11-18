import Proof.ActualSecondTraceDefinitions
import Proof.CompleteAdjointTensorGraph
import Proof.SecondTraceSectionExpansion
import Proof.PhysicalSecondTraceSection
import Proof.CanonicalFrameTraceSection
import Proof.FrameTraceRepresentatives
import Proof.SmoothHighCovariantSections
import Proof.UniformCompleteFirstAdjointGraph
import Proof.CompleteAdjointPhysicalSection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.SmoothSphereFields

/-- Retain the actual error tensor graph with the SAME second-trace witness. -/
theorem uniform_actual_second_trace_assembly_with_error_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ G : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ a,ContDiffOn ℝ ∞ (G a) Y) →
      (∀ a,∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x (axis a) (A x) (G a x)) →
      (∀ a,∀ x ∈ Y,‖actualFirstAdjointErrorFamily d (axis a) A (G a) x‖ ≤ C0*d.radius x) →
      ∃ S : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        (∀ i j,ContDiffOn ℝ ∞ (S i j) Y) ∧
        (∀ y ∈ Y,∀ i j,CoarseCovariantRotationGraph d y (d.frame y i)
          (actualFrameFirstAdjointErrorFamily d A G j)
          ((∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
            actualFrameFirstAdjointErrorFamily d A G k y)+S i j y)) ∧
        (∀ y ∈ Y,∀ i j,‖S i j y‖ ≤ CE*d.radius y*beta d.γ d.radius y) ∧
        ∀ φ : Field,smoothNear φ (bundle Y d.γ) →
        (∃ T : Set X,IsCompact T ∧ T ⊆ Y ∧ ∀ x ∈ Y \ T,∀ w ∈ sphereAt d.γ x,φ (x,w)=0) →
        ∀ L : ℂ →L[ℝ] ℝ,∀ F : X × X → ℝ,∀ hF : ContDiff ℝ ∞ F,
        (∀ x ∈ Y,∀ w : UnitSphere,F (x,w.val)=L (φ (x,frameVector d.frame x w.val))) →
        Nonempty (SecondTraceSectionOutput Y d A G S φ L F hF) := by
  classical
  obtain ⟨ηC,CE,hηC,hηC1,hCE,hCov⟩ :=
    uniform_complete_first_adjoint_covariant_graph_with_error_graph hY hΩ hSub hm K ρ c₀ M Cj hK hρ C0 hC0
  obtain ⟨ηV,QV,hηV,hQV,hSection⟩ := uniform_complete_adjoint_section_realization hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηN,QN,hηN,hQN,hNormal⟩ := uniform_actual_frozen_adjoint_normal_form hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηC (min ηV ηN),CE,lt_min hηC (lt_min hηV hηN),(min_le_left _ _).trans hηC1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA G hGS hG hE
  have hSmallC := hSmall.trans (min_le_left _ _)
  have hSmallV := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallN := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨S,hSS,hS⟩ := hCov floor hf ε hε hSmallC d hd R A hAS hR hA G hGS hG hE
  refine ⟨S,hSS,(fun y hy i j => (hS y hy i j).1),
    (fun y hy i j => (hS y hy i j).2.2),?_⟩
  intro φ hφ hcpt L F hF hRep
  have hVExists (j : I) : ∃ V : X × X → ℝ,∃ hV : ContDiff ℝ ∞ V,
      (∀ x ∈ Y,∀ w : UnitSphere,V (x,w.val)=L (frameAdjointField d.adjoint d.frame j φ (x,frameVector d.frame x w.val))) ∧
      ∀ x ∈ Y,completeFirstAdjointFamily d A G j x (ambientSobolevSection 1 (by norm_num) F hF x)=
        sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics (ambientSphereL2 V hV x) := by
    obtain ⟨T,hT,hTY,V,hV,hVRep,hVZero,hVOp⟩ :=
      hSection floor hf ε hε hSmallV d hd R A hR hA G hG j φ hφ hcpt L F hF hRep
    exact ⟨V,hV,hVRep,hVOp⟩
  choose V hVS hVRep hVOp using hVExists
  have hWExists (j : I) : ∃ W : X × X → ℝ,ContDiff ℝ ∞ W ∧
      ∀ x ∈ Y,∀ w : UnitSphere,W (x,w.val)=L (frameTraceDerivative d.γ d.adjoint d.frame j φ (x,frameVector d.frame x w.val)) := by
    obtain ⟨T,hT,hTY,W,hW,hWRep,hWZero⟩ := hd.exists_frameTrace_scalar_representative hY hSub (zero_lt_one.trans_le hK) hφ hcpt j L
    exact ⟨W,hW,hWRep⟩
  choose W hWS hWRep using hWExists
  let U := ambientSobolevSection 2 (by norm_num) F hF
  let D : I → X → SphereSobolev 1 := fun j x => highSectionCovariantDerivative d U x (d.frame x j)
  let V1 : I → X → SphereSobolev 1 := fun j => ambientSobolevSection 1 (by norm_num) (V j) (hVS j)
  let W1 : I → X → SphereSobolev 1 := fun j => ambientSobolevSection 1 (by norm_num) (W j) (hWS j)
  let C := completeFirstAdjointFamily d A G
  have hKp := zero_lt_one.trans_le hK
  have hEll : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he := fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hFrame := fun x hx => hd.1.2.2.2.2.2.2.2 x (hSub hx)
  have hES : ∀ j,ContDiffOn ℝ ∞ (actualFrameFirstAdjointErrorFamily d A G j) Y := by
    apply contDiffOn_actualFrameFirstAdjointErrorFamily d A G he
    intro a
    exact contDiffOn_actualFirstAdjointErrorFamily (axis a) hY hΩ hSub hd.1 hKp hd.2.2.2.2.1.1
      (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A (G a) hAS (hGS a)
  have hCS (j : I) : ContDiffOn ℝ ∞ (C j) Y := hd.contDiffOn_completeFirstAdjointFamily hY hΩ hSub hKp A G hES j
  have hUS : ContDiff ℝ ∞ U := contDiff_ambientSobolevSection 2 (by norm_num) F hF
  have hDS (j : I) : ContDiffOn ℝ ∞ (D j) Y :=
    contDiffOn_highSectionCovariantDerivative_frame hY d hEll hKp he U hUS.contDiffOn j
  refine ⟨{ representative:=V,smooth:=hVS,rep:=hVRep,normal:=hVOp,second:=?_ }⟩
  intro y hy i j
  let J : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun k => completeFirstAdjointTensorJetL d S y i k
  have hOut (k : I) : (fun x => sphereSobolevInclusionL 1 0 (by norm_num) (V1 k x)) =ᶠ[𝓝 y]
      (fun x => C k x (sphereSobolevInclusionL 2 1 (by norm_num) (U x))) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    change sphereSobolevInclusionL 1 0 (by norm_num) (ambientSobolevSection 1 (by norm_num) (V k) (hVS k) x)=_
    rw [ambientSobolevSection_coarse,ambientSobolevSection_inclusion]
    exact (hVOp k x hx).symm
  have hFirst (k : I) : W1 k =ᶠ[𝓝 y] (fun x => D k x+V1 k x) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact canonical_frameTrace_oneSection_eq hY d hEll hKp he hFrame φ hφ L F (W k) (V k) hF (hWS k) (hVS k) k
      hRep (hWRep k) (hVRep k) hx
  have hGraph (k : I) : CoarseCovariantRotationGraph d y (d.frame y i) (C k)
      ((∑ l : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) k l • C l y)+J k) := by
    have hh := (hS y hy i k).2.1
    have hEq :
        (∑ l : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) k l • C l y)+
          (-(d.radius y)⁻¹*fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y i)) • flatOneRaisingL k+
          hessianBilinear d.γ (fun x => Real.log (d.radius x)) y (d.frame y i) (d.frame y k) • sphereSobolevDegreeL+
          (firstFrameAdjointCovariantJetL d y (d.frame y i) k).comp (sphereSobolevInclusionL 1 0 (by norm_num))+S i k y=
        (∑ l : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) k l • C l y)+J k := by
      dsimp only [J,completeFirstAdjointTensorJetL]
      abel
    exact hEq ▸ hh
  have hAlg := second_trace_section_expansion d y i j C J U D V1 W1
    (fun k => ((hCS k).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (hUS.differentiable (by simp) y)
    (fun k => ((hDS k).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (fun k => (contDiff_ambientSobolevSection 1 (by norm_num) (V k) (hVS k)).differentiable (by simp) y)
    hOut hFirst rfl hGraph
  have hInput : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) (W1 j y)) =ᵐ[sphereProbability]
      fun w : UnitSphere => L (frameTraceDerivative d.γ d.adjoint d.frame j φ (y,frameVector d.frame y w.val)) := by
    change _=ᵐ[sphereProbability] _
    rw [show W1 j y=ambientSobolevSection 1 (by norm_num) (W j) (hWS j) y from rfl,
      ambientSobolevSection_coarse,LinearIsometryEquiv.symm_apply_apply]
    exact (ambientSphereL2_ae (W j) (hWS j) y).trans (Eventually.of_forall (hWRep j y hy))
  have hSmooth := hd.frameTraceDerivative_smoothNear hY hSub hKp hφ j
  have hAdjoint : (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm (C i y (W1 j y))
      =ᵐ[sphereProbability] fun w : UnitSphere => L (frameAdjointField d.adjoint d.frame i
        (frameTraceDerivative d.γ d.adjoint d.frame j φ) (y,frameVector d.frame y w.val)) := by
    have hh := frame_adjoint_normal_form_of_axes QN hQN d y (hFrame y hy)
      (fun a => actualFirstAdjointErrorFamily d (axis a) A (G a) y) i
      (frameTraceDerivative d.γ d.adjoint d.frame j φ) L (W1 j y)
      (fun a => hNormal floor hf ε hε hSmallN d hd R A hR hA a (G a) (hG a) y hy _ hSmooth L _ hInput)
    simpa only [C,completeFirstAdjointFamily_eq_normal_form QN hQN,_root_.add_apply,ContinuousLinearMap.comp_apply,
      actualFrameFirstAdjointErrorFamily,_root_.sum_apply,_root_.smul_apply] using hh
  have hPhysical := physical_second_trace_section_ae hY d hEll hKp he hFrame φ L W hWS hWRep hy i j hSmooth (C i y) hAdjoint
  have hExpanded : oneSectionCovariantDerivative d (W1 j) y (d.frame y i)-
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
        sphereSobolevInclusionL 1 0 (by norm_num) (W1 k y))+C i y (W1 j y)=
      expandedSecondTraceSection d A G S U V1 y i j := hAlg
  change (sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics).symm
    (expandedSecondTraceSection d A G S U V1 y i j) =ᵐ[sphereProbability] _
  rw [← hExpanded]
  exact hPhysical
end ShrinkingSpheres
