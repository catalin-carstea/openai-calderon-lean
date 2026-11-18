import Proof.NativeHigherScalarCombinationData
import Proof.ActualFirstErrorAngularCoefficients
import Proof.TaylorGeneratorAdjointDecomposition
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS BG : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def firstErrorHigherGeneratorCommutator (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q0 : SmoothCoefficientJets 2)
    {a b : X} {CC CH : ℝ}
    (Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH)
    (p : NormalFrameRelativeParameter) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  A.scalarCombinationHigherFamily G ha0
    (fun k _ => signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca) k)
    (fun k _ => actualFirstErrorGeneratorCoefficients Q0 Cb k)
    (fun k ij _ => signedTaylorScalarCoefficients (actualFirstErrorAngularCoefficients Q0 Ca ij.1 ij.2) k)
    (fun k ij _ => actualFirstErrorAngularCoefficients Q0 Cb ij.1 ij.2 k) p

/-- Genuine higher realization of the mixed signed/unsigned actual
    first-error generator commutator. The coefficient extension is constant
    in this pointwise construction; no physical parameter-jet claim is made. -/
lemma firstErrorHigherGeneratorCommutator_graph
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (hΩ : IsOpen Ω) (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z=1)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    {a b : X} {CC CH : ℝ}
    (Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let Gl := taylorGeneratorLow (s.response.adjointHalfTaylor p)
    let Gh := taylorGeneratorHigh (G.domain.adjointHigherTaylor h hK (by norm_num) p)
    let Qa := signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca)
    let Qb := actualFirstErrorGeneratorCoefficients Q0 Cb
    (∑ k,(Gl k).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Qa k))).comp
      (∑ l,(Gh l).comp (closedThreeJetHigherScalarMultiplierL (Qb l)))-
    (∑ l,(Gl l).comp (closedThreeJetHalfBoundaryScalarMultiplierL (Qb l))).comp
      (∑ k,(Gh k).comp (closedThreeJetHigherScalarMultiplierL (Qa k)))=
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (A.firstErrorHigherGeneratorCommutator G ha0 Q0 Ca Cb p) := by
  apply A.scalarCombinationHigherFamily_graph G ha0 H hΩ hF0 he hFlat hInv0
    (fun k _ => signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca) k)
    (fun k _ => actualFirstErrorGeneratorCoefficients Q0 Cb k)
    (fun k ij _ => signedTaylorScalarCoefficients (actualFirstErrorAngularCoefficients Q0 Ca ij.1 ij.2) k)
    (fun k ij _ => actualFirstErrorAngularCoefficients Q0 Cb ij.1 ij.2 k)
  · intro k i j
    simpa only [signedTaylorScalarCoefficients,map_smul] using
      congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => k.adjointSign • T)
        (actualFirstErrorAngularCoefficients_half Q0 hQ0 Ca he i j k)
  · intro k i j
    exact actualFirstErrorAngularCoefficients_half Q0 hQ0 Cb he i j k

lemma firstErrorHigherGeneratorCommutator_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (HS : NativeScalarGeneratorRotationData A ha0 BS) (HG : NativeHigherGeneratorCommutatorData G BG)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (Q0 : SmoothCoefficientJets 2) {a b : X} {CC CH : ℝ} (hCC : 0 ≤ CC)
    (Ca : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Cb : (k : I) → RelativeCenterErrorCoefficientFamily d y b k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hRa : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient Ca k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2)
    (hRb : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient Cb k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖b‖*(d.radius y)^2) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
    let CQ := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
    ‖A.firstErrorHigherGeneratorCommutator G ha0 Q0 Ca Cb p‖ ≤
      (3*C^3*CQ^2)*‖a‖*‖b‖*(d.radius y)^2 := by
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let C := taylorGeneratorFixedBudget F0 ha0 CG+2+|BG|+|BS|+‖closedThreeJetHigherScalarMultiplierL‖
  let CQ := firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR
  let qa := ∑ k,taylorGeneratorWeight (d.radius y) k*(‖actualFirstErrorGeneratorCoefficients Q0 Ca k‖+
    ∑ ij : I × I,‖actualFirstErrorAngularCoefficients Q0 Ca ij.1 ij.2 k‖)
  let qb := ∑ k,taylorGeneratorWeight (d.radius y) k*(‖actualFirstErrorGeneratorCoefficients Q0 Cb k‖+
    ∑ ij : I × I,‖actualFirstErrorAngularCoefficients Q0 Cb ij.1 ij.2 k‖)
  have hqa : qa ≤ CQ*‖a‖*(d.radius y) := hd.first_error_augmented_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a Ca CR hCR hRa
  have hqb : qb ≤ CQ*‖b‖*(d.radius y) := hd.first_error_augmented_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC b Cb CR hCR hRb
  have hC : 0 ≤ C := by
    have hCB := (taylorGeneratorFixedBudget_bounds F0 ha0 CG).1
    dsimp only [C]
    positivity
  have hCQ : 0 ≤ CQ := by
    have hJ : 0 ≤ firstErrorScalarFixedBudget Q0 := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
    have hK0 := zero_le_one.trans hK1
    dsimp only [CQ,firstErrorScalarAngularCommonBudget]
    positivity
  have hqb0 : 0 ≤ qb := by
    apply Finset.sum_nonneg
    intro k _
    have hw : 0 ≤ taylorGeneratorWeight (d.radius y) k := by cases k <;> simp only [taylorGeneratorWeight] <;> positivity
    exact mul_nonneg hw (add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
  have hPair := mul_le_mul hqa hqb hqb0 (by
    exact mul_nonneg (mul_nonneg hCQ (norm_nonneg a)) (hd.2.2.2.2.1.2 y hy).1.le)
  have hh := A.scalarCombinationHigherFamily_norm_le G ha0 HS HG
    (fun k _ => signedTaylorScalarCoefficients (actualFirstErrorGeneratorCoefficients Q0 Ca) k)
    (fun k _ => actualFirstErrorGeneratorCoefficients Q0 Cb k)
    (fun k ij _ => signedTaylorScalarCoefficients (actualFirstErrorAngularCoefficients Q0 Ca ij.1 ij.2) k)
    (fun k ij _ => actualFirstErrorAngularCoefficients Q0 Cb ij.1 ij.2 k)
  simp only [norm_signedTaylorScalarCoefficients] at hh
  calc
    _ ≤ 3*C^3*qa*qb := hh
    _ = 3*C^3*(qa*qb) := by ring
    _ ≤ 3*C^3*((CQ*‖a‖*(d.radius y))*(CQ*‖b‖*(d.radius y))) :=
      mul_le_mul_of_nonneg_left hPair (by positivity)
    _ = _ := by ring
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
