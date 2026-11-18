import Proof.NativeFirstErrorHigherAdjointCommutator
import Proof.UniformNativeAntisymmetricHigherKernel
import Proof.RelativeCenterAngularCoefficient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2700
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Physical first-error adjoint commutators have one shared higher witness
    for their graph and quadratic radius estimate, for any genuine endpoints. -/
def NativeFirstErrorHigherAdjointCommutatorData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (CC CH CS : ℝ) : Prop :=
  ∀ a b : X,
    ∀ Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH,
    ∀ Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH,
    ∀ Ha Hb : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp Hb=
      (s.firstAdjointErrorFamily Cb ((y,frameVectorLinear d.frame y),0)).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) →
    GradedHigherEndpointCommutatorBound (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
      (s.firstAdjointHalfErrorFamily Ca ((y,frameVectorLinear d.frame y),0)).adjoint
      (s.firstAdjointHalfErrorFamily Cb ((y,frameVectorLinear d.frame y),0)) Ha Hb
      (CS*‖a‖*‖b‖*(d.radius y)^2)

/-- All constants precede the admitted radius profile, frame and physical
    coefficient families. The already selected native generator is retained. -/
theorem uniform_native_first_error_higher_adjoint_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CC CH : ℝ) (hCC : 0 ≤ CC) (CG : ℝ) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ G : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      NativeFirstErrorHigherAdjointCommutatorData s CC CH CS := by
  obtain ⟨ηS,CK,CJ,BS,hηS,hηS1,_hCK,_hCJ,hBS,hScalar⟩ := uniform_native_scalar_generator_rotation_data
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0 ha0
  obtain ⟨ηG,BG,hηG,_hηG1,_hBG,hHigher⟩ := uniform_native_higher_generator_commutator
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  obtain ⟨ηK,CKN,CKH,hηK,_hηK1,hCKN,hCKH,hKernel⟩ := uniform_native_antisymmetric_higher_kernel_data
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0 ha0
  obtain ⟨CAng,hCAng,hAngular⟩ := RelativeCenterErrorCoefficientFamily.uniform_angularCoefficient_two_jets
    (Ω:=Ω) hΩ (show 2 ≤ m by omega) K M hK
  let CR := (CAng+2)*CC
  let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let CA := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
  let B := firstErrorHigherCommonBudget F0 ha0 Q0 CG CKN CKH BS CQ CI CW K (M 0) CC CR
  let CS := 3*C^3*CA^2+6*B^2
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hC : 0 ≤ C := by
    have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    dsimp only [C]
    positivity
  have hCS : 0 ≤ CS := by dsimp only [CS];positivity
  refine ⟨min ηS (min ηG ηK),CS,lt_min hηS (lt_min hηG hηK),
    (min_le_left _ _).trans hηS1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s G
  have hSmallS := hSmall.trans (min_le_left _ _)
  have hSmallG := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallK := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨A,HS⟩ := hScalar floor hf ε hε hSmallS d hd y hy CF CA CM s
  have HG := hHigher floor hf ε hε hSmallG d hd y hy CF CA CM s CG G
  obtain ⟨KN,KH,hKNJets,hP,hKern,hKH⟩ := hKernel floor hf ε hε hSmallK d hd y hy CF CA CM s CG G
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hKN : ‖KN p‖ ≤ CKN*(d.radius y)^2 := by
    simpa only [norm_iteratedFDeriv_zero] using hKNJets.bound 0 (by norm_num)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hε1 := hSmallS.trans hηS1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have hR (v : X) (Cv : (k : I) → RelativeCenterErrorCoefficientFamily d y v k CC CH) (i j k : I) :
      ‖RelativeCenterErrorCoefficientFamily.angularCoefficient Cv k i j p‖ ≤ CR*‖v‖*(d.radius y)^2 := by
    have hh := (hAngular d hd.1 y (hSub hy) v CC CH hCC Cv he k i j).bound 0 (by norm_num)
    simpa only [norm_iteratedFDeriv_zero,CR,mul_assoc] using hh
  intro a b Ca Cb Ha Hb hHa hHb
  exact A.actual_first_error_higher_adjoint_commutator G ha0 HS HG (zero_le_one.trans hBS)
    hd hK hf hε hε1 hy (hrε.trans hε1) hCQ hΩ hF0 Q0 hQ0 hCC Ca Cb CR hCR
    (hR a Ca) (hR b Cb) (KN p) CKN hCKN hKN KH CKH hCKH hKH hP hKern Ha Hb hHa hHb

end ShrinkingSpheres
