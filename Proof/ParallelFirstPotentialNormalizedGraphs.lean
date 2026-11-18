import Proof.ParallelNormAssemblyReservedFirstBoundedAdjoint
import Proof.ParallelNormAssemblyReservedNormalizedWordLifts
import Proof.FrameAdjointEndpointCombination
import Proof.ParallelFirstSelfLeadingExchange

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

private lemma forward_sum_endpoint_unique {E H ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I0 : E →L[ℝ] E) (J : H →L[ℝ] E) (hI : Function.Injective I0)
    (B : E →L[ℝ] E) (BH RH : H →L[ℝ] E) (R : E →L[ℝ] E)
    (L : ι → E →L[ℝ] E) (G : ι → H →L[ℝ] E) (w : ι → ℝ)
    (hB : I0.comp BH=B.comp J) (hG : ∀ a,I0.comp (G a)=(L a).comp J)
    (hR : I0.comp RH=R.comp J) (hSplit : B=(∑ a,w a • L a)+R) :
    BH=(∑ a,w a • G a)+RH := by
  apply ContinuousLinearMap.ext
  intro u
  apply hI
  have hBV := DFunLike.congr_fun hB u
  have hGV (a : ι) := DFunLike.congr_fun (hG a) u
  have hRV := DFunLike.congr_fun hR u
  simp only [ContinuousLinearMap.comp_apply] at hBV hGV hRV
  rw [hBV,hSplit]
  simp only [_root_.add_apply,_root_.sum_apply,_root_.smul_apply,map_add,map_sum,map_smul,hGV,hRV]

private lemma adjoint_add_endpoint {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (I0 B R : E →L[ℝ] E) (J BH RH : H →L[ℝ] E)
    (hB : I0.comp BH=B.adjoint.comp J) (hR : I0.comp RH=R.adjoint.comp J) :
    I0.comp (BH+RH)=(B+R).adjoint.comp J := by
  rw [map_add,ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp,hB,hR]

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstPotentialNormalizedAdjointHigh {P : PhysicalPrincipalData Y d CF CT} {y : X}
    (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ c : PhysicalPotentialGeneratorIndex,normalizedCoordinateGeneratorCoefficients d y a c • W.adjointHigh c

lemma firstPotentialNormalizedAdjointHigh_graph (P : PhysicalPrincipalData Y d CF CT)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (a : PhysicalPotentialGeneratorIndex) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (firstPotentialNormalizedAdjointHigh W a)=
      (normalizedPotentialGeneratorLow P y a).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have h := finite_real_adjoint_balanced_combination
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (P.potentialGeneratorLow y) W.adjointHigh W.adjoint_compatible (normalizedCoordinateGeneratorCoefficients d y a)
  rw [←normalized_generator_low_old_words] at h
  exact h

def firstPotentialBoundedForwardHigherL (d : Data) (b : I) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (effectiveFirstBoundedRemainderAtL (1/2:ℝ) d b y).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma firstPotentialBoundedForwardHigherL_graph (d : Data) (b : I) (y : X)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (firstPotentialBoundedForwardHigherL d b y)=
      (effectiveFirstBoundedRemainderHalfL d b y).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact DFunLike.congr_fun (effective_first_bounded_half_actual d b y he)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)

/-- Genuine full forward higher split; no Sobolev gain is inferred from
carrier equality. The original complete scalar drift is retained. -/
theorem firstPotential_forward_higher_word_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) (b : I)
    (hRaw : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    P.firstCovariantCoordinateHigherL b y=
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a • normalizedPotentialGeneratorHigh P y a)+
        firstPotentialBoundedForwardHigherL d b y :=
  forward_sum_endpoint_unique _ _ (sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    _ _ _ _ _ _ _ (P.firstCovariantCoordinateHigherL_balanced b y hRaw)
    (fun a => normalized_generator_balanced P hy a)
    (firstPotentialBoundedForwardHigherL_graph d b y (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)))
    (effective_first_normalized_word_split P hY hd hy b)

/-- The SAME selected WF and SAME selected W determine the exact full
true-adjoint higher split, including the bounded geometric/scalar part. -/
theorem firstPotential_adjoint_higher_word_split
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {y : X} (hy : y ∈ Y) (W : PhysicalPotentialQuarticData P y CG CK) (b : I) :
    WF.covariantCoordinateAdjointHigher b y=
      (∑ a : PhysicalPotentialGeneratorIndex,effectiveFirstWordCoefficient d b y a • firstPotentialNormalizedAdjointHigh W a)+
        effectiveFirstBoundedAdjointHigherL d b y := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hS := finite_real_adjoint_balanced_combination
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (normalizedPotentialGeneratorLow P y) (firstPotentialNormalizedAdjointHigh W)
    (firstPotentialNormalizedAdjointHigh_graph P hy W) (effectiveFirstWordCoefficient d b y)
  have hC := adjoint_add_endpoint _ _ _ _ _ _ hS (effective_first_bounded_adjoint_higher_graph d b y hFrame)
  rw [←effective_first_normalized_word_split P hY hd hy b] at hC
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  exact (DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hy) u).trans
    (DFunLike.congr_fun hC u).symm

end ShrinkingSpheres.ParallelEnergy
