import Proof.NormalFrameRelativeCoefficientPair
import Proof.UniformRelativeCoefficientPrincipalJets
import Proof.UniformRelativeFirstModelJets
import Proof.UniformRelativeRemainderJointJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- A single common-support geometric coefficient pair, its genuine germs
    on a whole parameter neighborhood, and its uniform finite joint jets. -/
structure NormalFrameRelativeCoefficientJetFamily (Y Ω : Set X) (g g₁ : MetricField)
    (E : X × X → X) (y : X) (L : X →L[ℝ] X) (r : ℝ) (N : ℕ) (Z C : ℝ) where
  a : NormalFrameRelativeParameter × X → Mat
  a1 : NormalFrameRelativeParameter × X → Mat
  smooth : ContDiff ℝ ∞ a
  firstSmooth : ContDiff ℝ ∞ a1
  support : Set X
  compact : IsCompact support
  supported : ∀ p z,z ∉ support → a (p,z) = 0
  firstSupported : ∀ p z,z ∉ support → a1 (p,z) = 0
  domain : Set NormalFrameRelativeParameter
  domainOpen : IsOpen domain
  pointMem : ((y,L),0) ∈ domain
  positive : domain ⊆ normalFrameRelativePositiveDomain Ω
  centers : ∀ p ∈ domain,p.1.1 ∈ Y
  covectorSmooth : ContDiffOn ℝ ∞ (normalFrameRelativeFirstCovector g g₁) domain
  coefficientGerm : ∀ p ∈ domain,∀ z ∈ Metric.closedBall (0:X) Z,
    a =ᶠ[𝓝 (p,z)] normalFrameRelativeCoefficient g g₁ E r
  firstGerm : ∀ p ∈ domain,∀ z ∈ Metric.closedBall (0:X) Z,
    a1 =ᶠ[𝓝 (p,z)] normalFrameRelativeFirstModel g g₁
  firstScalar : ∀ p ∈ domain,∀ z ∈ Metric.closedBall (0:X) Z,
    a1 (p,z) = normalFrameRelativeFirstCovector g g₁ p z • (1:Mat)
  coefficientJets : ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n a (((y,L),0),z)‖ ≤ C
  firstJets : ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n a1 (((y,L),0),z)‖ ≤ C
  remainderJets : ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n (fun q => a q-(1:Mat)-r • a1 q) (((y,L),0),z)‖ ≤ C*r^2

theorem uniform_normalFrameRelativeCoefficient_jet_family {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ r : ℝ,|r| ≤ d.radius y →
      Nonempty (NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y L r N Z C) := by
  obtain ⟨ηF,hηF,hηF1,hFamily⟩ := uniform_normalFrameRelative_coefficient_pair_family
    hY hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hA⟩ := uniform_normalFrameRelativeCoefficient_joint_jets
    hY hΩ N (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨η1,C1,hη1,hη11,hC1,hA1⟩ := uniform_normalFrameRelativeFirstModel_joint_jets
    hY hΩ N (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hR⟩ := uniform_normalFrameRelativeRemainder_joint_jets
    hY hΩ N hNm K ρ c₀ M Cj hK hρ Z hZ
  let C : ℝ := max CA (max C1 CR)
  refine ⟨min ηF (min ηA (min η1 ηR)),C,lt_min hηF (lt_min hηA (lt_min hη1 hηR)),
    (min_le_left _ _).trans hηF1,hCA.trans (le_max_left _ _),?_⟩
  intro floor hf ε hε hSmall d hd y hy L he r hr
  have hSmallF := hSmall.trans (min_le_left _ _)
  have hSmallA := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmall1 := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hSmallR := hSmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨a,a1,ha,ha1,S,hS,hzA,hzA1,V,hV,hpV,hVP,hVY,hCov,hRep,hRep1,hScalar,hRes⟩ :=
    hFamily floor hf ε hε hSmallF d hd y hy L he r hr
  refine ⟨{
    a := a, a1 := a1, smooth := ha, firstSmooth := ha1,
    support := S, compact := hS, supported := hzA, firstSupported := hzA1,
    domain := V, domainOpen := hV, pointMem := hpV, positive := hVP, centers := hVY,
    covectorSmooth := hCov, coefficientGerm := hRep, firstGerm := hRep1, firstScalar := hScalar,
    coefficientJets := ?_, firstJets := ?_, remainderJets := ?_ }⟩
  · intro z hz n hn
    have hzB : z ∈ Metric.closedBall (0:X) Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [((hRep _ hpV z hzB).iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hA floor hf ε hε hSmallA d hd y hy L he z hz r hr n hn).trans (le_max_left _ _)
  · intro z hz n hn
    have hzB : z ∈ Metric.closedBall (0:X) Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [((hRep1 _ hpV z hzB).iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hA1 floor hf ε hε hSmall1 d hd y hy L he z hz n hn).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro z hz n hn
    have hGerm : (fun q => a q-(1:Mat)-r • a1 q) =ᶠ[𝓝 ((((y,L),0),z))]
        (fun q => normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r q-(1:Mat)-r • normalFrameRelativeFirstModel d.γ d.g₁ q) := by
      have hzB : z ∈ Metric.closedBall (0:X) Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
      filter_upwards [hRep _ hpV z hzB,hRep1 _ hpV z hzB] with q hq hq1
      rw [hq,hq1]
    rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hR floor hf ε hε hSmallR d hd y hy L he z hz r hr n hn).trans
      (mul_le_mul_of_nonneg_right ((le_max_right C1 CR).trans (le_max_right CA _)) (sq_nonneg r))

end ShrinkingSpheres
