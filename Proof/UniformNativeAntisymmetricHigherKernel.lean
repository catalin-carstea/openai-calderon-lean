import Proof.ActualNormalHigherKernel
import Proof.UniformNativeAntisymmetricTaylorData
import Proof.NativeAntisymmetricTaylorNeighborhood
import Proof.HalfTaylorAdjointDefect
import Proof.NearIdentityInverse
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

def NativeAntisymmetricHigherKernelData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM) (CK CH : ℝ) : Prop :=
      ∃ KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∃ KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ),
      let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
      SmoothFiniteJetBound KN p 3 (CK*(d.radius y)^2) ∧
      (s.response.adjointHalfTaylor p).adjoint=s.response.adjointHalfTaylor p-
        (KN p).comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) ∧
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
        (-(KN p).adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
          (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖KH‖ ≤ CH*(d.radius y)^2

/-- The SAME genuine antisymmetric kernel has a quadratic-gain higher
    realization, for any previously selected native generator/scalar data. -/
theorem uniform_native_antisymmetric_higher_kernel {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (BS : ℝ) (hBS : 0 ≤ BS) :
    ∃ η CK CH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧ 0 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ CG : ℝ,∀ _G : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      ∀ CKA CJA : ℝ,∀ A : NativeAdjointHalfScalarNeighborhoodData s hd.1.1 (zero_lt_one.trans_le hK) CKA CJA,
      NativeScalarGeneratorRotationData A ha0 BS →
      NativeAntisymmetricHigherKernelData s CK CH := by
  have hAntiAll := uniform_native_antisymmetric_taylor_data (Y:=Y) (Ω:=Ω) (m:=m)
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q hQ
  obtain ⟨ηA,CR,CK,hηA,hηA1,hCR,hCK,hAnti⟩ := hAntiAll
  obtain ⟨ηW,hηW,hNeighborhood⟩ := uniform_native_antisymmetric_taylor_neighborhood (Y:=Y) (Ω:=Ω) (m:=m)
    hY hΩ (show 2 ≤ m by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨CAng,hCAng,hAngular⟩ := RelativeNormalScalarRemainderFamily.uniform_angular_two_jets
    (Ω:=Ω) hΩ (show 2 ≤ m by omega) K M hK
  have hCR0 : 0 ≤ CR := zero_le_one.trans hCR
  have hCAng0 : 0 ≤ CAng := zero_le_one.trans hCAng
  let BM := ‖closedThreeJetHigherScalarMultiplierL‖*(‖linearScalarClosedCoefficientL Q‖*CQ+CR)
  have hBM : 0 ≤ BM := by dsimp only [BM];positivity
  let ηN := 1/(2*(1+BM))
  have hηN : 0 < ηN := by dsimp only [ηN];positivity
  let CH := nativeNormalAntisymmetricHigherBudget Q CQ CR CAng BS
  have hCH : 0 ≤ CH := nativeNormalAntisymmetricHigherBudget_nonneg Q CQ CR CAng BS hCQ hCR0 hCAng0 hBS
  refine ⟨min ηA (min ηW ηN),CK,CH,lt_min hηA (lt_min hηW hηN),
    (min_le_left _ _).trans hηA1,hCK,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s CG G CKA CJA A H
  have hSmallA := hSmall.trans (min_le_left _ _)
  have hSmallW := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallN := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAntiCurrent := hAnti floor hf ε hε hSmallA d hd y hy CF CA CM s
  obtain ⟨R,haR,V,hKNJets,hGraph⟩ := hAntiCurrent
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let KN := fun x => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q x)
    (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ x)) x
  let KH := A.actualNormalAntisymmetricHigher ha0 Q R p
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := (hrε.trans hSmallA).trans hηA1
  have hEll : ‖normalFrameRelativeFirstCovector d.γ d.g₁ p‖ ≤ CQ := by
    simpa only [norm_iteratedFDeriv_zero] using s.coefficients.firstCovectorJets (by norm_num) 0 (by norm_num)
  have he (i j : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hRAngular (ij : I × I) : ‖normalFrameRelativeAngularDerivative d.γ R.closed ij.1 ij.2 p‖ ≤ CAng*(CR*(d.radius y)^2) := by
    have hh := hAngular d hd.1 y (hd.2.1.center_mem hy) CR R he ij.1 ij.2
    simpa only [norm_iteratedFDeriv_zero] using hh.bound 0 (by norm_num)
  have hNear : BM*d.radius y ≤ (1/2:ℝ) := by
    have hP : 0 < 1+BM := by linarith
    have hMul := mul_le_mul_of_nonneg_left (hrε.trans hSmallN) hP.le
    have hEq : (1+BM)*ηN=(1/2:ℝ) := by dsimp only [ηN];field_simp
    rw [hEq] at hMul
    nlinarith only [hMul,hr]
  have hAt : ‖closedThreeJetHigherScalarMultiplierL (R.normalCoefficient Q p)-
      ContinuousLinearMap.id ℝ (SphereSobolev (3/2:ℝ))‖ ≤ (1/2:ℝ) :=
    (R.normalCoefficient_higher_deviation_norm_le Q hQ CQ hCR0 hr hr1 hEll).trans hNear
  letI : CompleteSpace (SphereSobolev (3/2:ℝ)) := lp.completeSpace
  obtain ⟨hM,hInv⟩ := near_identity_inverse_data _ hAt
  obtain ⟨W,hW,hpW,hWV,hKNW⟩ := hNeighborhood floor hf ε hε hSmallW d hd y hy
    F0 CQ CI CW CF CA CM CR s R Q hQ ha0 hF0 V
  have hPos : p ∈ normalFrameRelativePositiveDomain Ω := s.coefficients.positive s.coefficients.pointMem
  refine ⟨KN,KH,hKNJets,?_,?_,?_⟩
  · exact s.response.adjointHalfTaylor_transpose_defect V (by norm_num) F0 hF0 p V.pointMem (KN p) hGraph
  · exact A.actualNormalAntisymmetricHigher_half_compatible G ha0 H hF0 Q hQ R hPos he hM
      (hKNW p hpW).1 (hKNW p hpW).2.2
  · exact A.actualNormalAntisymmetricHigher_norm_le ha0 H hF0 Q hQ R CAng hCQ hCR0 hCAng0 hBS
      hr hr1 hEll hRAngular hPos he hM hInv

/-- Closed common producer: the required scalar angular data are supplied
    by the existing uniform producer, for any selected native generator. -/
theorem uniform_native_antisymmetric_higher_kernel_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) :
    ∃ η CK CH : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧ 0 ≤ CH ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∀ CG : ℝ,∀ _G : NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG,
      NativeAntisymmetricHigherKernelData s CK CH := by
  obtain ⟨ηS,CKA,CJA,BS,hηS,hηS1,_hCKA,_hCJA,hBS,hScalar⟩ := uniform_native_scalar_generator_rotation_data
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q hQ ha0
  obtain ⟨ηK,CK,CH,hηK,_hηK1,hCK,hCH,hKernel⟩ := uniform_native_antisymmetric_higher_kernel
    (Y:=Y) (Ω:=Ω) (m:=m) hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q hQ ha0 BS
      (zero_le_one.trans hBS)
  refine ⟨min ηS ηK,CK,CH,lt_min hηS hηK,(min_le_left _ _).trans hηS1,hCK,hCH,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s CG G
  obtain ⟨A,H⟩ := hScalar floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CF CA CM s
  exact hKernel floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF CA CM s CG G CKA CJA A H

end ShrinkingSpheres
