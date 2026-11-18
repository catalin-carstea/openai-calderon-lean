import Proof.FirstErrorScalarAngularBounds
import Proof.ActualCoframeDirectionBound
import Proof.ActualFirstErrorGeneratorCommutator
import Proof.RelativeCenterAngularCoefficient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

def actualFirstErrorAngularCoefficients {d : Data} {y a : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2) (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (i j : I) : TaylorGeneratorIndex → ClosedCoefficientJets 3 :=
  firstErrorScalarAngularCoefficients Q0 (d.radius y)⁻¹
    (fun k => normalFrameRelativeCoframeValue d.γ a k ((y,frameVectorLinear d.frame y),0))
    (fun k => (C k).closed ((y,frameVectorLinear d.frame y),0))
    (fun k => RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j ((y,frameVectorLinear d.frame y),0)) i j

lemma actualFirstErrorAngularCoefficients_half {d : Data} {y a : X} {CC CH : ℝ}
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (he : ∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
      ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0)
    (i j : I) (b : TaylorGeneratorIndex) :
    closedThreeJetHalfBoundaryScalarMultiplierL (actualFirstErrorAngularCoefficients Q0 C i j b)=
      closedCoefficientAngularHalfL i j (actualFirstErrorGeneratorCoefficients Q0 C b) :=
  firstErrorScalarAngularCoefficients_half Q0 hQ0 _ _ _ _ _ i j
    (fun k => RelativeCenterErrorCoefficientFamily.angularCoefficient_half C _
      (fun l => (C l).point) he k i j) b

lemma Admissible.first_error_angular_coefficient_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    {y : X} (hy : y ∈ Y) (hr1 : d.radius y ≤ 1) (Q0 : SmoothCoefficientJets 2)
    {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR) (i j : I)
    (hR : ∀ k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2) :
    (∑ b,taylorGeneratorWeight (d.radius y) b*‖actualFirstErrorAngularCoefficients Q0 C i j b‖) ≤
      (firstErrorScalarFixedBudget Q0*(54*|M 0| *K+15*(CR+2*CC)))*‖a‖*(d.radius y) := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hQ (k : I) : ‖(C k).closed ((y,frameVectorLinear d.frame y),0)‖ ≤ CC*‖a‖*(d.radius y)^2 := by
    simpa only [RelativeCenterErrorCoefficientFamily.closed,norm_iteratedFDeriv_zero] using (C k).joint 0 (by norm_num)
  have hh := firstErrorScalarAngularCoefficients_weighted_bound Q0 (d.radius y) ‖a‖
    (9*|M 0| *K) CC CR hr hr1 (norm_nonneg _) (by positivity) hCC hCR _ _ _ i j
    (fun k => hd.relative_coframe_direction_bound hK (hd.2.1.center_mem hy) a k) hQ hR
  exact hh.trans_eq (by ring)

def firstErrorScalarAngularCommonBudget (Q0 : SmoothCoefficientJets 2) (K M0 CC CR : ℝ) : ℝ :=
  firstErrorScalarFixedBudget Q0*(27*|M0| *K+3*K+15*CC)+
    9*(firstErrorScalarFixedBudget Q0*(54*|M0| *K+15*(CR+2*CC)))

lemma Admissible.first_error_augmented_coefficient_bound {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (hr1 : d.radius y ≤ 1)
    (Q0 : SmoothCoefficientJets 2) {CC CH : ℝ} (hCC : 0 ≤ CC) (a : X)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (CR : ℝ) (hCR : 0 ≤ CR)
    (hR : ∀ i j k,‖RelativeCenterErrorCoefficientFamily.angularCoefficient C k i j
      ((y,frameVectorLinear d.frame y),0)‖ ≤ CR*‖a‖*(d.radius y)^2) :
    (∑ b,taylorGeneratorWeight (d.radius y) b*(‖actualFirstErrorGeneratorCoefficients Q0 C b‖+
      ∑ ij : I × I,‖actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b‖)) ≤
    firstErrorScalarAngularCommonBudget Q0 K (M 0) CC CR*‖a‖*(d.radius y) := by
  have hQ := hd.first_error_scalar_coefficient_bound hK hf hε hε1 hy hr1 Q0 hCC a C
  have hA (ij : I × I) := hd.first_error_angular_coefficient_bound hK hy hr1 Q0 hCC a C CR hCR ij.1 ij.2 (hR ij.1 ij.2)
  calc
    _ = (∑ b,taylorGeneratorWeight (d.radius y) b*‖actualFirstErrorGeneratorCoefficients Q0 C b‖)+
        ∑ ij : I × I,∑ b,taylorGeneratorWeight (d.radius y) b*‖actualFirstErrorAngularCoefficients Q0 C ij.1 ij.2 b‖ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      exact Finset.sum_comm
    _ ≤ (firstErrorScalarFixedBudget Q0*(27*|M 0| *K+3*K+15*CC))*‖a‖*(d.radius y)+
        ∑ _ij : I × I,(firstErrorScalarFixedBudget Q0*(54*|M 0| *K+15*(CR+2*CC)))*‖a‖*(d.radius y) :=
      add_le_add hQ (Finset.sum_le_sum (fun ij _ => hA ij))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
      dsimp only [firstErrorScalarAngularCommonBudget]
      ring
end ShrinkingSpheres
