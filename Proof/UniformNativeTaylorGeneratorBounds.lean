import Proof.NativeTaylorSelectedHigherJets
import Proof.NativeTaylorGeneratorEndpoints
import Proof.UniformNativeAdjointHalfScalarPointData
import Proof.UniformNativeRelativeDegreeHigherData
import Proof.RelativeAngularNormalizationJets
import Proof.SmoothFiniteAdjointJets
import Proof.NativeHalfTaylorHigherRegularity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

structure NativeTaylorGeneratorBounds {Y Ω : Set X} {d : Data} {y : X}
    {F0 : SmoothCoefficientMatrix 2} {CQ CI CW CF CA CM : ℝ}
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    {K : ℝ} (h : Elliptic Ω K d.γ) (hK : 0 < K) (C : ℝ) where
  domain : s.response.SymmetricAdjointDomain
  low_bound : ‖s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ C*(d.radius y)^2
  high_bound : ‖domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)‖ ≤ C*(d.radius y)^2
  degree_bound : ‖domain.degreeFamily h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)‖ ≤ C*(d.radius y)^2
  angular_bound : ∀ i j : I,
    ‖fderiv ℝ s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)
      (normalFrameRelativeAngularTangent d.γ ((y,frameVectorLinear d.frame y),0) i j)‖ ≤ C*(d.radius y)^2
  scalar : ClosedCoefficientJets 3 → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  scalar_bound : ∀ Q,‖scalar Q‖ ≤ C*‖Q‖*(d.radius y)^2
  scalar_graph : ∀ Q,
    (domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0)).comp
      (closedThreeJetHigherScalarMultiplierL Q)-
    (closedThreeJetHalfBoundaryScalarMultiplierL Q).comp
      (domain.adjointHigherTaylor h hK (by norm_num) ((y,frameVectorLinear d.frame y),0))=
      (scalar Q).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

/-- Uniform pointwise bounds for the SAME common Taylor generator, with its
chosen higher endpoint, degree/rotation commutators and every scalar commutator.
All constants precede admitted profiles and frames. -/
theorem uniform_native_taylor_generator_bounds {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    ∃ η CG : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ CG ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      Nonempty (NativeTaylorGeneratorBounds s hd.1.1 (zero_lt_one.trans_le hK) CG) := by
  obtain ⟨ηD,CFD,CAD,CD,hηD,hηD1,hCFD,hCAD,hCD,hDegree⟩ := uniform_native_relative_degree_higher_data
    hY hΩ 3 (by omega) K ρ c₀ M Cj hK hρ CI CW hCI hCW F0 hF0
  obtain ⟨ηS,CK,CJ,hηS,hηS1,hCK,hCJ,hScalar⟩ := uniform_native_adjoint_half_scalar_point_data
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  obtain ⟨D,hD,hNormalize⟩ := uniform_relative_angular_normalization_jets hΩ 3 (by omega) K M hK
  let BL := |lowRadialTaylorJetBudget 3 2 CW 5 CQ CQ CQ|
  let CH := BL+CD
  let CR := 2*D*BL
  let CG := 1+BL+CH+CD+CR+CJ
  have hBL : 0 ≤ BL := abs_nonneg _
  have hCD0 := zero_le_one.trans hCD
  have hCH : 0 ≤ CH := add_nonneg hBL hCD0
  have hD0 := zero_le_one.trans hD
  have hCR : 0 ≤ CR := by dsimp only [CR];positivity
  have hCG : 1 ≤ CG := by dsimp only [CG];linarith only [hBL,hCH,hCD0,hCR,hCJ]
  have hBLG : BL ≤ CG := by dsimp only [CG];linarith only [hBL,hCH,hCD0,hCR,hCJ]
  have hCHG : CH ≤ CG := by dsimp only [CG];linarith only [hBL,hCH,hCD0,hCR,hCJ]
  have hCDG : CD ≤ CG := by dsimp only [CG];linarith only [hBL,hCH,hCD0,hCR,hCJ]
  have hCRG : CR ≤ CG := by dsimp only [CG];linarith only [hBL,hCH,hCD0,hCR,hCJ]
  have hCJG : CJ ≤ CG := by dsimp only [CG];linarith only [hBL,hCH,hCD0,hCR,hCJ]
  refine ⟨min ηD ηS,CG,lt_min hηD hηS,(min_le_left _ _).trans hηD1,hCG,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨V,hF,hA,hDj⟩ := hDegree floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy CQ CF CA CM s
  obtain ⟨Vs,KN,hKNJ,hQJets,hQGraphs⟩ := hScalar floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy CF CA CM s
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hrε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := (hrε.trans hSmall).trans ((min_le_left _ _).trans hηD1)
  have hLow : SmoothFiniteJetBound s.coefficients.halfTaylor p 3 (BL*(d.radius y)^2) :=
    s.half_taylor_three_jets V hCQ hCW hr.le hr1 hF0
  have hPa : SmoothFiniteJetBound s.response.adjointHalfTaylor p 3 (BL*(d.radius y)^2) := hLow.adjoint
  have hDegreeJets : SmoothFiniteJetBound (V.degreeFamily hd.1.1 (zero_lt_one.trans_le hK) (by norm_num))
      p 3 (CD*(d.radius y)^2) :=
    ⟨by positivity,(V.contDiffOn_degreeFamily hΩ hd.1.1 (zero_lt_one.trans_le hK) (by norm_num)).contDiffAt
      (V.domainOpen.mem_nhds V.pointMem),hDj⟩
  have hHigh := s.adjoint_higher_taylor_three_jets V hd.1.1 (zero_lt_one.trans_le hK)
    hCQ hCW hr.le hr1 hF0 CD hDegreeJets
  let S := fun T => s.response.adjointHalfScalarCommutator F0 KN T p
  refine ⟨{
    domain := V
    low_bound := ?_
    high_bound := ?_
    degree_bound := ?_
    angular_bound := ?_
    scalar := S
    scalar_bound := ?_
    scalar_graph := ?_ }⟩
  · have hh := hPa.bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hBLG (sq_nonneg _))
  · have hh := hHigh.bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans (by simpa only [CH,add_mul] using mul_le_mul_of_nonneg_right hCHG (sq_nonneg (d.radius y)))
  · have hh := hDegreeJets.bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hCDG (sq_nonneg _))
  · intro i j
    have he (a b : I) : metricPair d.γ y ((frameVectorLinear d.frame y) (axis a))
        ((frameVectorLinear d.frame y) (axis b))=if a=b then 1 else 0 := by
      simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) a b
    obtain ⟨hNS,hNJ,hT⟩ := hNormalize d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) _ he
    have hTN := (hT i j).2 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hTN
    have hDF := hPa.bound 1 (by omega)
    rw [norm_iteratedFDeriv_one] at hDF
    have hh := (fderiv ℝ s.response.adjointHalfTaylor p).le_opNorm (normalFrameRelativeAngularTangent d.γ p i j)
    have hh' := hh.trans (mul_le_mul hDF hTN (norm_nonneg _) (by positivity))
    exact hh'.trans ((show (BL*(d.radius y)^2)*(2*D)=CR*(d.radius y)^2 by dsimp only [CR];ring).le.trans
      (mul_le_mul_of_nonneg_right hCRG (sq_nonneg _)))
  · intro T
    have hh := (hQJets (fun _ => T) ‖T‖ (SmoothFiniteJetBound.constant T p 3)).bound 0 (by omega)
    rw [norm_iteratedFDeriv_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCJG (norm_nonneg T)) (sq_nonneg _))
  · intro T
    exact balanced_higher_scalar_commutator (s.response.adjointTaylor p)
      (V.adjointHigherTaylor hd.1.1 (zero_lt_one.trans_le hK) (by norm_num) p) (S T) T
      (V.adjointHigherTaylor_coarse_compatible hd.1.1 (zero_lt_one.trans_le hK) (by norm_num) F0 hF0 p V.pointMem)
      (hQGraphs T).1
end ShrinkingSpheres
