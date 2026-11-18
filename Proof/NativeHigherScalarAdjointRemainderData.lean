import Proof.HigherScalarAdjointRemainderBounds
import Proof.NativeHigherScalarPointNorm
import Proof.ActualFirstErrorAngularCoefficients
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeAdjointHalfScalarNeighborhoodData
variable {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM : ℝ}
  {s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM}
  {K CK CJ CG BS : ℝ} {h : Elliptic Ω K d.γ} {hK : 0 < K}

def scalarAdjointRemainderHigher
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (R : TaylorGeneratorIndex → I × I → ClosedCoefficientJets 3) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ) :=
  taylorScalarAdjointRemainderHigherL KH
    (fun a => A.higherScalarGeneratorFromRotationData ha0 a (fun _ => Q a) (fun ij _ => R a ij)
      ((y,frameVectorLinear d.frame y),0)) Q

lemma scalarAdjointRemainderHigher_compatible
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (G : NativeTaylorGeneratorBounds s h hK CG)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (R : TaylorGeneratorIndex → I × I → ClosedCoefficientJets 3)
    (hR : ∀ a i j,closedThreeJetHalfBoundaryScalarMultiplierL (R a (i,j))=closedCoefficientAngularHalfL i j (Q a))
    (hKern : (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp KH=
      (-KN.adjoint : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).comp
      (A.scalarAdjointRemainderHigher ha0 KH Q R)=
      (taylorScalarAdjointRemainderHalfL KN (fun a => taylorGeneratorScalarCommutator G.scalar F0 ha0 a (Q a)) Q).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  taylorScalarAdjointRemainder_higher_half_compatible KH KN _ _ Q hKern
    (fun a => (H.2 CG G (fun _ => Q a) (fun ij _ => R a ij) (hR a) a).1)

lemma scalarAdjointRemainderHigher_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) (BK : ℝ) (hBK : 0 ≤ BK)
    (hKH : ‖KH‖ ≤ BK*(d.radius y)^2)
    (Q : TaylorGeneratorIndex → ClosedCoefficientJets 3)
    (R : TaylorGeneratorIndex → I × I → ClosedCoefficientJets 3) :
    ‖A.scalarAdjointRemainderHigher ha0 KH Q R‖ ≤
      (‖closedThreeJetHigherScalarMultiplierL‖*BK+BS)*
        (∑ a,taylorGeneratorWeight (d.radius y) a*(‖Q a‖+∑ ij : I × I,‖R a ij‖)) := by
  exact norm_taylorScalarAdjointRemainderHigherL_weighted KH _ Q
    (fun a => ‖Q a‖+∑ ij : I × I,‖R a ij‖) BK BS (d.radius y) hBK hKH
    (fun a => le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    (fun a => A.higherScalarGeneratorFromRotationData_norm_le ha0 H (fun _ => Q a) (fun ij _ => R a ij) a)

lemma actualFirstErrorScalarAdjointRemainderHigher_norm_le
    (A : NativeAdjointHalfScalarNeighborhoodData s h hK CK CJ)
    (ha0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (H : NativeScalarGeneratorRotationData A ha0 BS) (hBS : 0 ≤ BS)
    {m : ℕ} {ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK1 : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (KH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (3/2:ℝ)) (BK : ℝ) (hBK : 0 ≤ BK)
    (hKH : ‖KH‖ ≤ BK*(d.radius y)^2)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hR : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2) :
    ‖A.scalarAdjointRemainderHigher ha0 KH (actualFirstErrorGeneratorCoefficients Q0 C)
      (fun b ij => actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b)‖ ≤
      ((‖closedThreeJetHigherScalarMultiplierL‖*BK+BS)*
        firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR)*‖a‖*(d.radius y) := by
  have hh := A.scalarAdjointRemainderHigher_norm_le ha0 H KH BK hBK hKH
    (actualFirstErrorGeneratorCoefficients Q0 C) (fun b ij => actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b)
  have hQ := hd.first_error_augmented_coefficient_bound hK1 hf hε hε1 hy hr1 Q0 hCC a C CR hCR hR
  have hBudget : 0 ≤ ‖closedThreeJetHigherScalarMultiplierL‖*BK+BS := by positivity
  exact hh.trans ((mul_le_mul_of_nonneg_left hQ hBudget).trans_eq (by ring))
end NativeAdjointHalfScalarNeighborhoodData
end ShrinkingSpheres
