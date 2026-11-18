import Proof.CanonicalRetainedPrincipalNorm
import Proof.UniformPhysicalTruncatedCoreCalculus
import Proof.TruncatedPrincipalEnergyReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

/-- The exact square of the retained physical principal output. -/
def PhysicalPrincipalData.truncatedForwardSquare
    {Y : Set X} {d : Data} {CF CT CG CK : ℝ}
    (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) : ℝ :=
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) • Z (D.realComponent.raisingOutput y)+
    P.truncatedCovariantCoreSection W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)+
  (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) • Z (D.imagComponent.raisingOutput y)+
    P.truncatedCovariantCoreSection W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)

/-- The physically weighted square of twice lowering plus the constructed
formal adjoint of the SAME scalar/first/potential residual. -/
def PhysicalPrincipalData.truncatedAdjointSquare
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) : ℝ :=
  let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
  (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) • Z (D.realComponent.loweringOutput y)+
    P.truncatedFormalAdjointCore WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)+
  (∫ y in Y,metricDensity d.γ y*‖(2:ℝ) • Z (D.imagComponent.loweringOutput y)+
    P.truncatedFormalAdjointCore WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2)

def physicalAngularModelGap {Y : Set X} {d : Data} {φ : Field}
    {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius) : ℝ :=
  ((∫ y in Y,metricDensity d.γ y*‖D.realComponent.raisingOutput y‖^2)+
    (∫ y in Y,metricDensity d.γ y*‖D.imagComponent.raisingOutput y‖^2))-
  ((∫ y in Y,metricDensity d.γ y*‖D.realComponent.loweringOutput y‖^2)+
    (∫ y in Y,metricDensity d.γ y*‖D.imagComponent.loweringOutput y‖^2))

lemma physicalAngularModelGap_eq {Y : Set X} {d : Data} {φ : Field}
    {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (O : AngularProductOutputs D) :
    physicalAngularModelGap D=‖O.raising.output‖^2-‖O.lowering.output‖^2 := by
  rw [O.raising.normSq,O.lowering.normSq]
  rfl

lemma PhysicalPrincipalData.truncatedAdjointSquare_nonneg
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    0 ≤ P.truncatedAdjointSquare WF W E D := by
  unfold truncatedAdjointSquare
  exact add_nonneg (integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)))
    (integral_nonneg (fun y => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)))

private lemma integrable_model_core_square {Y S : Set X}
    (hY : IsOpen Y) (hS : IsCompact S) (hSY : S ⊆ Y)
    (μ : X → ℝ) (hμ : ContinuousOn μ Y) (hμ0 : ∀ y ∈ Y,0 ≤ μ y)
    (Z : SphereL2 ≃ₗᵢ[ℝ] SphereSobolev 0)
    (T : X → SphereL2) (hT : ContDiff ℝ ∞ T) (h0T : ∀ y ∉ S,T y=0)
    (U : X → SphereSobolev 0) (hU : MemLp U 2 (volume.restrict Y))
    (h0U : ∀ y ∉ S,U y=0) :
    IntegrableOn (fun y => μ y*‖(2:ℝ) • Z (T y)+U y‖^2) Y := by
  have hZT : MemLp (fun y => Z (T y)) 2 (volume.restrict Y) :=
    (Z.contDiff.comp hT).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.intro hS (fun y hy => by
        change Z (T y)=0
        rw [h0T y hy,map_zero]))
  have hSum := (hZT.const_smul (2:ℝ)).add hU
  exact integrableOn_local_weighted_norm_sq_of_memLp hY.measurableSet hS hSY _ hSum
    (fun y _ hy => by
      change (2:ℝ) • Z (T y)+U y=0
      rw [h0T y hy,map_zero,smul_zero,h0U y hy,add_zero]) μ hμ hμ0

/-- Each model-plus-core square in the norm comparison is genuinely
integrable. This uses the actual common core domain and compact test
support, separately for each of the four outputs. -/
theorem PhysicalPrincipalData.truncatedModelSquares_integrable
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    let Z := sphereSobolevZeroEquiv orthogonalSphereHarmonics denseSphereHarmonics
    IntegrableOn (fun y => metricDensity d.γ y*‖(2:ℝ) • Z (D.realComponent.raisingOutput y)+
      P.truncatedCovariantCoreSection W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*‖(2:ℝ) • Z (D.imagComponent.raisingOutput y)+
      P.truncatedCovariantCoreSection W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*‖(2:ℝ) • Z (D.realComponent.loweringOutput y)+
      P.truncatedFormalAdjointCore WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2) Y ∧
    IntegrableOn (fun y => metricDensity d.γ y*‖(2:ℝ) • Z (D.imagComponent.loweringOutput y)+
      P.truncatedFormalAdjointCore WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y‖^2) Y := by
  extract_lets Z
  let Ur := E.realHigherSobolevSection (5/2:ℝ) (by norm_num)
  let Ui := E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUr := E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)
  have hUi := E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)
  have h0Ur (y) (hy : y ∉ E.supportSet) : Ur y=0 := E.realHigherSobolevSection_zero _ _ (by norm_num) hy
  have h0Ui (y) (hy : y ∉ E.supportSet) : Ui y=0 := E.imagHigherSobolevSection_zero _ _ (by norm_num) hy
  have hR := P.truncatedCoreOperators_memLp hY hΩ hSub hd hK WF W hCG hCK Ur hUr
    E.supportSet E.compactSupportSet E.supportSubset h0Ur 2
  have hI := P.truncatedCoreOperators_memLp hY hΩ hSub hd hK WF W hCG hCK Ui hUi
    E.supportSet E.compactSupportSet E.supportSubset h0Ui 2
  have hzR (y) (hy : y ∉ E.supportSet) := P.truncatedCoreOperators_zero_off hY hSub hd hK WF W
    Ur hUr E.supportSet E.compactSupportSet.isClosed E.supportSubset h0Ur hy
  have hzI (y) (hy : y ∉ E.supportSet) := P.truncatedCoreOperators_zero_off hY hSub hd hK WF W
    Ui hUi E.supportSet E.compactSupportSet.isClosed E.supportSubset h0Ui hy
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have hw := (hg.contDiffOn_density hK).continuousOn
  have hw0 : ∀ y ∈ Y,0 ≤ metricDensity d.γ y := fun _ _ => Real.sqrt_nonneg _
  refine ⟨?_,?_,?_,?_⟩
  · exact integrable_model_core_square hY E.compactSupportSet E.supportSubset _ hw hw0 Z
      D.realComponent.raisingOutput D.realComponent.contDiff_raisingOutput
      (fun _ hy => D.realComponent.raisingOutput_zero hy) _ hR.1 (fun _ hy => (hzR _ hy).1)
  · exact integrable_model_core_square hY E.compactSupportSet E.supportSubset _ hw hw0 Z
      D.imagComponent.raisingOutput D.imagComponent.contDiff_raisingOutput
      (fun _ hy => D.imagComponent.raisingOutput_zero hy) _ hI.1 (fun _ hy => (hzI _ hy).1)
  · exact integrable_model_core_square hY E.compactSupportSet E.supportSubset _ hw hw0 Z
      D.realComponent.loweringOutput D.realComponent.contDiff_loweringOutput
      (fun _ hy => D.realComponent.loweringOutput_zero hy) _ hR.2 (fun _ hy => (hzR _ hy).2)
  · exact integrable_model_core_square hY E.compactSupportSet E.supportSubset _ hw hw0 Z
      D.imagComponent.loweringOutput D.imagComponent.contDiff_loweringOutput
      (fun _ hy => D.imagComponent.loweringOutput_zero hy) _ hI.2 (fun _ hy => (hzI _ hy).2)

/-- Precise internal analytic obligation. All constants and the cutoff are
chosen before profiles, and the common operator/adjoint families before tests.
The comparison is of actual physical fibre squares, not arbitrary Hilbert
partners. This proposition is NOT a hypothesis of the selected result. -/
def UniformPhysicalTruncatedNormComparison (Y Ω : Set X) (K ρ c₀ : ℝ) {m : ℕ}
    (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CF CT : ℝ) : Prop :=
  ∃ Q : SmoothCoefficientJets 2,∃ B η CE CB CS CG CK : ℝ,
    (∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) ∧
    0 < η ∧ 0 ≤ CE ∧ 0 ≤ CG ∧ 0 ≤ CK ∧
    ∀ floor,B ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ P : PhysicalPrincipalData Y d CF CT,
      ∃ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∃ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      PhysicalTruncatedCoreCalculus P WF W ∧
      ∀ φ,Test Y d.γ d.frame φ →
      ∀ (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius),
        |(P.truncatedForwardSquare W E D-P.truncatedAdjointSquare WF W E D)-
          4*physicalAngularModelGap D| ≤ CE*ε*(energyNorm Y d φ)^2

/-- Checked downstream caller for the exact remaining uniform comparison. -/
theorem uniform_truncated_lowerBound_of_physical_normComparison
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ CF CT : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hK : 1 ≤ K) (h : UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT) :
    UniformTruncatedPrincipalLowerBound Y Ω K ρ c₀ M Cj CF CT := by
  obtain ⟨Q,B,η,CE,CB,CS,CG,CK,hQ,hη,hCE,hCG,hCK,produce⟩ := h
  refine ⟨Q,B,η,CE,hQ,hη,hCE,?_⟩
  intro floor hf ε hε hSmall d hd P φ hφ E D O PP J R
  obtain ⟨WF,W,hCalc,hCompare⟩ := produce floor hf ε hε hSmall d hd P
  have hNorm := P.norm_principal_minus_complements hY hΩ hSub hd (zero_lt_one.trans_le hK)
    Q hQ WF W hCG hCK hφ E D PP J R
  have hLower := (abs_le.mp (hCompare φ hφ E D)).1
  have hPartner := P.truncatedAdjointSquare_nonneg WF W E D
  have hGap := physicalAngularModelGap_eq D O
  dsimp only at hNorm
  have hNorm' : ‖PP.output-J.realization.output-R.realization.output‖^2=P.truncatedForwardSquare W E D := by
    dsimp only [PhysicalPrincipalData.truncatedForwardSquare]
    convert hNorm using 1
  change 4*(‖O.raising.output‖^2-‖O.lowering.output‖^2) ≤
    ‖PP.output-J.realization.output-R.realization.output‖^2+CE*ε*(energyNorm Y d φ)^2
  rw [hNorm',← hGap]
  linarith

/-- The exact physical comparison suffices for the unchanged selected
coercivity statement, through the existing complete complement absorption. -/
theorem uniformEstimate_of_physical_truncated_normComparison
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (hc₀ : 0 < c₀)
    (h : ∀ CF CT : ℝ,0 ≤ CF → 0 ≤ CT →
      UniformPhysicalTruncatedNormComparison Y Ω K ρ c₀ M Cj CF CT) :
    ∃ floor ε₀ C : ℝ,1 ≤ floor ∧ 0 < ε₀ ∧ 0 < C ∧
      UniformEstimate Y Ω K ρ c₀ M Cj floor ε₀ C := by
  apply uniformEstimate_of_truncatedPrincipalLowerBound hY hΩ hSub hm K ρ c₀ M Cj hK hρ hc₀
  intro CF CT hCF hCT
  exact uniform_truncated_lowerBound_of_physical_normComparison hY hΩ hSub hK (h CF CT hCF hCT)

end ShrinkingSpheres
