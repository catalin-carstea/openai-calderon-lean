import Proof.NativeScalarMixedAdjointData
import Proof.UniformNativeFirstErrorHigherAdjointCommutator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Uniform mixed-adjoint point data for arbitrary genuine scalar-plus-
bounded packets on one selected native generator family. -/
def NativeScalarPacketMixedAdjointData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
    {K CG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}
    (G : NativeTaylorGeneratorBounds s h hK CG) (CQB CZB CAug CS : ℝ) : Prop :=
  ∀ scaleA scaleB : ℝ,0 ≤ scaleA → 0 ≤ scaleB →
  ∀ La Lb : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
  ∀ Ha0 Hb0 : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
  ∀ A : NativeScalarBoundedEndpointData G La Ha0 CQB CZB scaleA,
  ∀ B : NativeScalarBoundedEndpointData G Lb Hb0 CQB CZB scaleB,
  NativeScalarBoundedHigherData A CAug → NativeScalarBoundedHigherData B CAug →
  ∀ Ha : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
  (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp Ha=
    La.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) →
  Nonempty (GradedBalancedCommutatorBound
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) La.adjoint Lb Ha Hb0 (CS*scaleA*scaleB))

/-- Closed uniform low/high mixed-adjoint production preserving arbitrary
separate packet scales. The actual angular and bounded-higher packets
remain genuine inputs; no regularity follows from their underlying types. -/
theorem uniform_native_scalar_mixed_adjoint_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (CG CQB CZB CAug : ℝ) (hCQB : 0 ≤ CQB) (hCAug : 0 ≤ CAug) :
    ∃ η CS : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CS ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ G : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      NativeScalarPacketMixedAdjointData G CQB CZB CAug CS := by
  have hS := uniform_native_scalar_generator_rotation_data
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0 ha0
  obtain ⟨ηS,CK,CJ,BS,hηS,hηS1,_hCK,_hCJ,hBS,hScalar⟩ := hS
  have hG := uniform_native_higher_generator_commutator
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hSub hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0
  obtain ⟨ηG,BG,hηG,_hηG1,_hBG,hHigher⟩ := hG
  have hKernData := uniform_native_antisymmetric_higher_kernel_data
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0 ha0
  obtain ⟨ηK,CKN,CKH,hηK,_hηK1,hCKN,hCKH,hKernel⟩ := hKernData
  let CS := nativeScalarMixedAdjointBudget F0 ha0 CG CKN CKH BS BG CQ CI CW CQB CZB CAug
  have hCS : 0 ≤ CS := nativeScalarMixedAdjointBudget_nonneg F0 ha0 CG CKN CKH BS BG CQ CI CW CQB CZB CAug
  refine ⟨min ηS (min ηG ηK),CS,lt_min hηS (lt_min hηG hηK),(min_le_left _ _).trans hηS1,hCS,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s G
  have hSmallS := hSmall.trans (min_le_left _ _)
  have hSmallG := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallK := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N,HS⟩ := hScalar floor hf ε hε hSmallS d hd y hy CF CA CM s
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
  intro scaleA scaleB hScaleA hScaleB La Lb Ha0 Hb0 A B DA DB Ha hHa
  exact DA.mixed_adjoint_data DB N ha0 HS HG hΩ hF0 he hCQ hCI hCW hr.le (hrε.trans hε1)
    hCQB hCAug hScaleA hScaleB (zero_le_one.trans hBS) (KN p) CKN hCKN hKN KH CKH hCKH hKH hP hKern Ha hHa
end ShrinkingSpheres
