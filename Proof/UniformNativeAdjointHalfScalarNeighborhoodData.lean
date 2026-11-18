import Proof.NativeAdjointHalfScalarCommutator
import Proof.DenseSkewAdjoint
import Proof.NativeAntisymmetricTaylorNeighborhood
import Proof.NativeAntisymmetricKernelRegularity
import Proof.ZeroOrderInterpolationJets
import Proof.UniformNativeAntisymmetricTaylorData
import Proof.SmoothFiniteAdjointJets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
local instance nativeAdjointHalfScalarNeighborhoodNegativeComplete : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := lp.completeSpace

/-- SAME physical scalar commutator family, its actual neighborhood, and
joint gained jets. The selected native witnesses are explicit fields. -/
structure NativeAdjointHalfScalarNeighborhoodData
    {Y Ω : Set X} {d : Data} {y : X} {F0 : SmoothCoefficientMatrix 2}
    {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (CK CJ : ℝ) where
  domain : s.response.SymmetricAdjointDomain
  kernel : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  kernel_jets : SmoothFiniteJetBound kernel ((y,frameVectorLinear d.frame y),0) 3 (CK*(d.radius y)^2)
  scalar_jets : ∀ T : NormalFrameRelativeParameter → ClosedCoefficientJets 3,∀ BT : ℝ,
    SmoothFiniteJetBound T ((y,frameVectorLinear d.frame y),0) 3 BT →
    SmoothFiniteJetBound (fun p => s.response.adjointHalfScalarCommutator F0 kernel (T p) p)
      ((y,frameVectorLinear d.frame y),0) 3 ((CJ*BT)*(d.radius y)^2)
  neighborhood : Set NormalFrameRelativeParameter
  neighborhoodOpen : IsOpen neighborhood
  pointMem : ((y,frameVectorLinear d.frame y),0) ∈ neighborhood
  sub : neighborhood ⊆ domain.domain
  low_graph : ∀ p ∈ neighborhood,∀ T : ClosedCoefficientJets 3,
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      ((s.response.adjointHalfScalarCommutator F0 kernel T p).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))=
      (s.response.adjointTaylor p).comp (closedOneBoundaryScalarMultiplierL T)-
        (closedThreeJetCoarseScalarMultiplierL T).comp (s.response.adjointTaylor p)
  high_graph : ∀ p ∈ neighborhood,∀ T : ClosedCoefficientJets 3,
    (domain.adjointHigherTaylor h hK (by norm_num) p).comp (closedThreeJetHigherScalarMultiplierL T)-
      (closedThreeJetHalfBoundaryScalarMultiplierL T).comp (domain.adjointHigherTaylor h hK (by norm_num) p)=
    (s.response.adjointHalfScalarCommutator F0 kernel T p).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

theorem uniform_native_adjoint_half_scalar_neighborhood_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    ∃ η CK CJ : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧ 0 ≤ CJ ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      Nonempty (NativeAdjointHalfScalarNeighborhoodData s hd.1.1 (zero_lt_one.trans_le hK) CK CJ) := by
  obtain ⟨ηA,CR,CK,hηA,hηA1,hCR,hCK,hSkew⟩ := uniform_native_antisymmetric_taylor_data
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q hQ
  obtain ⟨ηW,hηW,hNeighborhood⟩ := uniform_native_antisymmetric_taylor_neighborhood (Y:=Y) (Ω:=Ω) (m:=m)
    hY hΩ (show 2 ≤ m by omega) K ρ c₀ M Cj hK hρ
  let CJ := 2^3*(2^3*|nativeMultiplierKernelLinearJetBudget 3 F0 CI CI CW 5 CQ CQ CQ|)+
    2*(2^3)*CK*‖closedThreeJetHalfBoundaryScalarMultiplierL‖
  have hCJ : 0 ≤ CJ := by dsimp only [CJ];positivity
  refine ⟨min ηA ηW,CK,CJ,lt_min hηA hηW,(min_le_left _ _).trans hηA1,hCK,hCJ,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  have hSmallA : ε ≤ ηA := hSmall.trans (min_le_left _ _)
  have hSmallW : ε ≤ ηW := hSmall.trans (min_le_right _ _)
  obtain ⟨R,ha0,V,hKNJ,_hPoint⟩ := hSkew floor hf ε hε hSmallA d hd y hy CF CA CM s
  let KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    fun p => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q p)
      (linearScalarClosedCoefficientL Q (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := (hrε.trans hSmallA).trans hηA1
  obtain ⟨W,hW,hpW,hWV,hKNW⟩ := hNeighborhood floor hf ε hε hSmallW d hd y hy
    F0 CQ CI CW CF CA CM CR s R Q hQ ha0 hF0 V
  refine ⟨{
    domain := V
    kernel := KN
    kernel_jets := hKNJ
    scalar_jets := ?_
    neighborhood := W
    neighborhoodOpen := hW
    pointMem := hpW
    sub := hWV
    low_graph := ?_
    high_graph := ?_ }⟩
  · intro T BT hT
    exact s.adjointHalfScalarCommutator_three_jets hF0 hCQ hCI hCW hr.le hr1 KN CK hKNJ T BT hT
  · intro p hp T
    exact s.response.adjointTaylor_half_scalar_commutator_graph V (by norm_num) F0 hF0 KN T
      p (hWV hp) (hKNW p hp).2.1
  · intro p hp T
    exact s.response.adjointHigherTaylor_scalar_commutator_graph V hd.1.1 (zero_lt_one.trans_le hK)
      (by norm_num) F0 hF0 KN T p (hWV hp) (hKNW p hp).2.1
end ShrinkingSpheres
