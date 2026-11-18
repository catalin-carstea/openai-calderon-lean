import Proof.NormalFrameRelativeCoefficientJetFamily
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

structure NormalFrameRelativeCoefficientHigherBudget {Y Ω : Set X} {d : Data} {y : X}
    {N0 : ℕ} {Z C0 : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N0 Z C0) (N : ℕ) (C : ℝ) : Prop where
  coefficient : ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n q.a (((y,frameVectorLinear d.frame y),0),z)‖ ≤ C
  first : ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n q.a1 (((y,frameVectorLinear d.frame y),0),z)‖ ≤ C
  remainder : ∀ z : X,‖z‖ ≤ Z → ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n (fun p => q.a p-(1:Mat)-d.radius y • q.a1 p)
      (((y,frameVectorLinear d.frame y),0),z)‖ ≤ C*(d.radius y)^2

def NormalFrameRelativeCoefficientJetFamily.withHigherJetBudget {Y Ω : Set X} {d : Data} {y : X}
    {N0 : ℕ} {Z C0 : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N0 Z C0) (N : ℕ) (C : ℝ)
    (h : NormalFrameRelativeCoefficientHigherBudget q N C) :
    NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C where
  a := q.a
  a1 := q.a1
  smooth := q.smooth
  firstSmooth := q.firstSmooth
  support := q.support
  compact := q.compact
  supported := q.supported
  firstSupported := q.firstSupported
  domain := q.domain
  domainOpen := q.domainOpen
  pointMem := q.pointMem
  positive := q.positive
  centers := q.centers
  covectorSmooth := q.covectorSmooth
  coefficientGerm := q.coefficientGerm
  firstGerm := q.firstGerm
  firstScalar := q.firstScalar
  coefficientJets := h.coefficient
  firstJets := h.first
  remainderJets := h.remainder

/-- Every previously selected smooth geometric representative has the same
    uniform higher joint budgets. Only its budget proofs are upgraded; its
    actual coefficients, support and parameter domain stay identical. -/
theorem uniform_chosen_relative_coefficient_higher_budget {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ N0 : ℕ,∀ C0 : ℝ,
      ∀ q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
        (frameVectorLinear d.frame y) (d.radius y) N0 Z C0,
      NormalFrameRelativeCoefficientHigherBudget q N C := by
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hA⟩ := uniform_normalFrameRelativeCoefficient_joint_jets
    hY hΩ N (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨η1,C1,hη1,hη11,hC1,hA1⟩ := uniform_normalFrameRelativeFirstModel_joint_jets
    hY hΩ N (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηR,CR,hηR,hηR1,hCR,hRem⟩ := uniform_normalFrameRelativeRemainder_joint_jets
    hY hΩ N hNm K ρ c₀ M Cj hK hρ Z hZ
  let C := max CA (max C1 CR)
  refine ⟨min ηA (min η1 ηR),C,lt_min hηA (lt_min hη1 hηR),
    (min_le_left _ _).trans hηA1,hCA.trans (le_max_left _ _),?_⟩
  intro floor hf ε hε hSmall d hd y hy N0 C0 q
  let L := frameVectorLinear d.frame y
  let p0 : NormalFrameRelativeParameter := ((y,L),0)
  have he (i j : I) : metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0 := by
    simpa only [L,frameVectorLinear_apply,frameVector_axis] using
      hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  have hrAbs : |d.radius y| ≤ d.radius y := by rw [abs_of_pos (hd.2.2.2.2.1.2 y hy).1]
  have hSmallA := hSmall.trans (min_le_left _ _)
  have hSmall1 := hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSmallR := hSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_,?_,?_⟩
  · intro z hz n hn
    have hzB : z ∈ Metric.closedBall (0:X) Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [((q.coefficientGerm _ q.pointMem z hzB).iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hA floor hf ε hε hSmallA d hd y hy L he z hz (d.radius y) hrAbs n hn).trans (le_max_left _ _)
  · intro z hz n hn
    have hzB : z ∈ Metric.closedBall (0:X) Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    rw [((q.firstGerm _ q.pointMem z hzB).iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hA1 floor hf ε hε hSmall1 d hd y hy L he z hz n hn).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · intro z hz n hn
    have hzB : z ∈ Metric.closedBall (0:X) Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
    have hGerm : (fun p => q.a p-(1:Mat)-d.radius y • q.a1 p) =ᶠ[𝓝 (p0,z)]
        (fun p => normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) p-
          (1:Mat)-d.radius y • normalFrameRelativeFirstModel d.γ d.g₁ p) := by
      filter_upwards [q.coefficientGerm _ q.pointMem z hzB,q.firstGerm _ q.pointMem z hzB] with p hp hp1
      rw [hp,hp1]
    rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (hRem floor hf ε hε hSmallR d hd y hy L he z hz (d.radius y) hrAbs n hn).trans
      (mul_le_mul_of_nonneg_right ((le_max_right C1 CR).trans (le_max_right CA _)) (sq_nonneg _))

end ShrinkingSpheres
