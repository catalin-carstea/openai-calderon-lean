import Proof.CanonicalTruncatedPrincipalFibre
import Proof.SobolevOutputFibreDomain
import Proof.PhysicalMinusTwoProductNorm
import Proof.FirstCorrectionCrossRegularity
import Proof.PhysicalPotentialRemainderSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

private def retainedComponent (T C J R : X → SphereL2) (y : X) : SphereL2 :=
  (2:ℝ) • T y+C y+J y+R y

private lemma retained_component_domains {Y S : Set X} (hY : IsOpen Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (μ : X → ℝ) (hμ : ContinuousOn μ Y) (hμ0 : ∀ y ∈ Y,0 ≤ μ y)
    (T C J R : X → SphereL2)
    (hT : MemLp T 2 (volume.restrict Y)) (hC : MemLp C 2 (volume.restrict Y))
    (hJ : MemLp J 2 (volume.restrict Y)) (hR : MemLp R 2 (volume.restrict Y))
    (h0 : ∀ y ∈ Y,y ∉ S → T y=0 ∧ C y=0 ∧ J y=0 ∧ R y=0) :
    MemLp (retainedComponent T C J R) 2 (volume.restrict Y) ∧
    MemLp (fun y => J y+R y) 2 (volume.restrict Y) ∧
    IntegrableOn (fun y => μ y*‖retainedComponent T C J R y‖^2) Y ∧
    IntegrableOn (fun y => μ y*‖J y+R y‖^2) Y := by
  have hAll : MemLp (retainedComponent T C J R) 2 (volume.restrict Y) :=
    (((hT.const_smul (2:ℝ)).add hC).add hJ).add hR
  have hSum : MemLp (fun y => J y+R y) 2 (volume.restrict Y) := hJ.add hR
  have h0All (y) (hy : y ∈ Y) (hs : y ∉ S) : retainedComponent T C J R y=0 := by
    have hh := h0 y hy hs
    simp only [retainedComponent,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,smul_zero,add_zero]
  have h0Sum (y) (hy : y ∈ Y) (hs : y ∉ S) : J y+R y=0 := by
    rw [(h0 y hy hs).2.2.1,(h0 y hy hs).2.2.2,add_zero]
  exact ⟨hAll,hSum,integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hAll h0All μ hμ hμ0,
    integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hSum h0Sum μ hμ hμ0⟩

private lemma retained_component_sub_norm
    (Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0) (t j r : SphereL2) (c : SphereSobolev 0) :
    ‖(2:ℝ) • t+Z.symm c+j+r-(j+r)‖^2=‖(2:ℝ) • Z t+c‖^2 := by
  have hVec : (2:ℝ) • t+Z.symm c+j+r-(j+r)=(2:ℝ) • t+Z.symm c := by abel
  rw [hVec]
  calc
    _ = ‖Z ((2:ℝ) • t+Z.symm c)‖^2 := congrArg (fun z : ℝ => z^2) (Z.norm_map _).symm
    _ = _ := by rw [map_add,map_smul,LinearIsometryEquiv.apply_symm_apply]

private lemma point_fibre_eq_of_section_eq
    (Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0)
    (Core : (X → SphereSobolev (5/2:ℝ)) → X → SphereSobolev 0)
    (J R : SphereSobolev 1 →L[ℝ] SphereSobolev 0) (t : SphereL2) (y : X)
    {U U' : X → SphereSobolev (5/2:ℝ)} {v v' : SphereSobolev 1}
    (hU : U=U') (hv : v=v') :
    Z.symm ((2:ℝ) • Z t+Core U y+J v+R v)=
      Z.symm ((2:ℝ) • Z t+Core U' y+J v'+R v') := by
  rw [hU,hv]

/-- Exact original physical norm of the retained principal trace. The
two complements are the SAME realized J and R supplied to the final
lower-bound caller; the retained fibre is twice raising plus the actual
constructed truncated residual. -/
theorem PhysicalPrincipalData.norm_principal_minus_complements
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (hφ : Test Y d.γ d.frame φ) (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (D : AngularModelData E d.radius)
    (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ))
    (J : SobolevFamilyOutput d E (fun y => firstCorrectionCrossRemainderL Q d y))
    (R : SobolevFamilyOutput d E P.potentialRemainderCoarseL) :
    let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    ‖PP.output-J.realization.output-R.realization.output‖^2=
      (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) • Z (D.realComponent.raisingOutput y)+
        P.truncatedCovariantCoreSection W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)+
      (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) • Z (D.imagComponent.raisingOutput y)+
        P.truncatedCovariantCoreSection W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2) := by
  extract_lets Z
  let Zi : SphereSobolev 0 →L[ℝ] SphereL2 := Z.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Cr := fun y => Z.symm (P.truncatedCovariantCoreSection W Ur y)
  let Ci := fun y => Z.symm (P.truncatedCovariantCoreSection W Ui y)
  have hZi : (fun a : SphereSobolev 0 => Zi a)=(fun a : SphereSobolev 0 => Z.symm a) := rfl
  let Fr := retainedComponent D.realComponent.raisingOutput Cr J.realSection R.realSection
  let Fi := retainedComponent D.imagComponent.raisingOutput Ci J.imagSection R.imagSection
  have hUr := E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUi := E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have h0Ur (y) (hy : y ∉ E.supportSet) : Ur y=0 := E.realHigherSobolevSection_zero _ _ (by norm_num) hy
  have h0Ui (y) (hy : y ∉ E.supportSet) : Ui y=0 := E.imagHigherSobolevSection_zero _ _ (by norm_num) hy
  have hCoreR := (P.truncatedCoreOperators_memLp hY hΩ hSub hd hK WF W hCG hCK Ur hUr
    E.supportSet E.compactSupportSet E.supportSubset h0Ur 2).1
  have hCoreI := (P.truncatedCoreOperators_memLp hY hΩ hSub hd hK WF W hCG hCK Ui hUi
    E.supportSet E.compactSupportSet E.supportSubset h0Ui 2).1
  have hJR := J.sections_memLp hY (hd.contDiffOn_firstCorrectionCrossRemainderL hY hΩ hK Q) 2
  have hRR := R.sections_memLp hY (P.potentialRemainderCoarseL_smooth hY hΩ hd hK) 2
  have hTR : MemLp D.realComponent.raisingOutput 2 (volume.restrict Y) :=
    D.realComponent.contDiff_raisingOutput.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.intro E.compactSupportSet (fun _ hx => D.realComponent.raisingOutput_zero hx))
  have hTI : MemLp D.imagComponent.raisingOutput 2 (volume.restrict Y) :=
    D.imagComponent.contDiff_raisingOutput.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.intro E.compactSupportSet (fun _ hx => D.imagComponent.raisingOutput_zero hx))
  have hCr : MemLp Cr 2 (volume.restrict Y) := by
    have hh := Zi.comp_memLp' hCoreR
    change MemLp (fun y => (fun a : SphereSobolev 0 => Zi a) (P.truncatedCovariantCoreSection W Ur y)) 2 (volume.restrict Y) at hh
    rw [hZi] at hh
    exact hh
  have hCi : MemLp Ci 2 (volume.restrict Y) := by
    have hh := Zi.comp_memLp' hCoreI
    change MemLp (fun y => (fun a : SphereSobolev 0 => Zi a) (P.truncatedCovariantCoreSection W Ui y)) 2 (volume.restrict Y) at hh
    rw [hZi] at hh
    exact hh
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have hρ := (hg.contDiffOn_density hK).continuousOn
  have h0R (y) (hy : y ∈ Y) (hs : y ∉ E.supportSet) :
      D.realComponent.raisingOutput y=0 ∧ Cr y=0 ∧ J.realSection y=0 ∧ R.realSection y=0 := by
    refine ⟨D.realComponent.raisingOutput_zero hs,?_,(J.sections_zero_on_domain hy hs).1,(R.sections_zero_on_domain hy hs).1⟩
    change Z.symm (P.truncatedCovariantCoreSection W Ur y)=0
    rw [(P.truncatedCoreOperators_zero_off hY hSub hd hK WF W Ur hUr E.supportSet
      E.compactSupportSet.isClosed E.supportSubset h0Ur hs).1,map_zero]
  have h0I (y) (hy : y ∈ Y) (hs : y ∉ E.supportSet) :
      D.imagComponent.raisingOutput y=0 ∧ Ci y=0 ∧ J.imagSection y=0 ∧ R.imagSection y=0 := by
    refine ⟨D.imagComponent.raisingOutput_zero hs,?_,(J.sections_zero_on_domain hy hs).2,(R.sections_zero_on_domain hy hs).2⟩
    change Z.symm (P.truncatedCovariantCoreSection W Ui y)=0
    rw [(P.truncatedCoreOperators_zero_off hY hSub hd hK WF W Ui hUi E.supportSet
      E.compactSupportSet.isClosed E.supportSubset h0Ui hs).1,map_zero]
  have hRD := retained_component_domains hY E.compactSupportSet E.supportSubset _ hρ
    (fun _ _ => Real.sqrt_nonneg _) D.realComponent.raisingOutput Cr J.realSection R.realSection hTR hCr hJR.1 hRR.1 h0R
  have hID := retained_component_domains hY E.compactSupportSet E.supportSubset _ hρ
    (fun _ _ => Real.sqrt_nonneg _) D.imagComponent.raisingOutput Ci J.imagSection R.imagSection hTI hCi hJR.2 hRR.2 h0I
  have hReal (y) (hy : y ∈ Y) : Fr y =ᵐ[sphereProbability] (fun v => (PP.representative (y,v)).re) := by
    have hc := P.canonical_truncated_plus_complements_ae hY hΩ hSub hd hK Q hQ W hφ E Complex.reCLM D.realComponent hy
    have hPoint : Fr y=Z.symm ((2:ℝ) • Z (D.realComponent.raisingOutput y)+
        P.truncatedCovariantCoreSection W Ur y+firstCorrectionCrossRemainderL Q d y (E.realSobolevSection 1 (by norm_num) y)+
        P.potentialRemainderCoarseL y (E.realSobolevSection 1 (by norm_num) y)) := by
      dsimp only [Fr,retainedComponent,Cr,Zi]
      rw [J.realEq y hy,R.realEq y hy]
      simp only [map_add,map_smul,LinearIsometryEquiv.symm_apply_apply]
      rfl
    rw [hPoint]
    dsimp only at hc
    have hc' := hc.trans (Eventually.of_forall (fun v => congrArg Complex.re (PP.eqOn y hy v).symm))
    let F := fun p => Complex.reCLM (E.representative p)
    have hF : ContDiff ℝ ∞ F := Complex.reCLM.contDiff.comp E.representativeSmooth
    have hUeq : Ur=ambientHigherSobolevSection (5/2:ℝ) (by norm_num) F hF := rfl
    have hVeq : E.realSobolevSection 1 (by norm_num) y=ambientSobolevSection 1 (by norm_num) F hF y := rfl
    have he := point_fibre_eq_of_section_eq Z (P.truncatedCovariantCoreSection W)
      (firstCorrectionCrossRemainderL Q d y) (P.potentialRemainderCoarseL y)
      (D.realComponent.raisingOutput y) y hUeq hVeq
    have he' := congrArg (fun v : SphereL2 => (v : UnitSphere → ℝ)) he
    apply Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq he')
    convert hc' using 1
  have hImag (y) (hy : y ∈ Y) : Fi y =ᵐ[sphereProbability] (fun v => (PP.representative (y,v)).im) := by
    have hc := P.canonical_truncated_plus_complements_ae hY hΩ hSub hd hK Q hQ W hφ E Complex.imCLM D.imagComponent hy
    have hPoint : Fi y=Z.symm ((2:ℝ) • Z (D.imagComponent.raisingOutput y)+
        P.truncatedCovariantCoreSection W Ui y+firstCorrectionCrossRemainderL Q d y (E.imagSobolevSection 1 (by norm_num) y)+
        P.potentialRemainderCoarseL y (E.imagSobolevSection 1 (by norm_num) y)) := by
      dsimp only [Fi,retainedComponent,Ci,Zi]
      rw [J.imagEq y hy,R.imagEq y hy]
      simp only [map_add,map_smul,LinearIsometryEquiv.symm_apply_apply]
      rfl
    rw [hPoint]
    dsimp only at hc
    have hc' := hc.trans (Eventually.of_forall (fun v => congrArg Complex.im (PP.eqOn y hy v).symm))
    let F := fun p => Complex.imCLM (E.representative p)
    have hF : ContDiff ℝ ∞ F := Complex.imCLM.contDiff.comp E.representativeSmooth
    have hUeq : Ui=ambientHigherSobolevSection (5/2:ℝ) (by norm_num) F hF := rfl
    have hVeq : E.imagSobolevSection 1 (by norm_num) y=ambientSobolevSection 1 (by norm_num) F hF y := rfl
    have he := point_fibre_eq_of_section_eq Z (P.truncatedCovariantCoreSection W)
      (firstCorrectionCrossRemainderL Q d y) (P.potentialRemainderCoarseL y)
      (D.imagComponent.raisingOutput y) y hUeq hVeq
    have he' := congrArg (fun v : SphereL2 => (v : UnitSphere → ℝ)) he
    apply Filter.EventuallyEq.trans (Filter.EventuallyEq.of_eq he')
    convert hc' using 1
  have hNorm := PP.norm_sub_two_product_outputs hY hρ J.realization R.realization Fr Fi hReal hImag
    hRD.1.aestronglyMeasurable hID.1.aestronglyMeasurable hRD.2.1.aestronglyMeasurable hID.2.1.aestronglyMeasurable
    hRD.2.2.1 hID.2.2.1 hRD.2.2.2 hID.2.2.2
  change ‖PP.output-J.realization.output-R.realization.output‖^2=_ at hNorm
  rw [hNorm]
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    apply congrArg (fun z : ℝ => metricDensity d.γ y*z)
    dsimp only [Fr,retainedComponent,Cr,Zi]
    rw [retained_component_sub_norm Z]
  · apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    apply congrArg (fun z : ℝ => metricDensity d.γ y*z)
    dsimp only [Fi,retainedComponent,Ci,Zi]
    rw [retained_component_sub_norm Z]

end ShrinkingSpheres
