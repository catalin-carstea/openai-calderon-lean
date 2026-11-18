import Proof.ParallelModelFirstZeroRemainder
import Proof.ParallelFirstSelfLeadingBudgets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

structure ModelFirstZeroGreenBudget (Y Ω : Set X) {m : ℕ}
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (CB : ℝ) where
  eta : ℝ
  CJ : ℝ
  C : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1
  CJ_nonneg : 0 ≤ CJ
  C_nonneg : 0 ≤ C
  actual : ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ eta → ∀ d,
    Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS : ℝ,
    ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
    ∃ hJ : FirstSelfCompleteAdjointJetBound WF CJ,
    ∀ U : X → SphereSobolev (5/2:ℝ),∀ y ∈ Y,
      |modelFirstZeroPairedRemainder WF hJ U y| ≤ C*ε*metricDensity d.γ y*
        ∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i)

/-- Small uniform packet retains ONE complete true-adjoint first HIGH
jet before all test sections, and the original paired zero-model energy. -/
theorem model_first_zero_green_budget_exists {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CB : ℝ) (hCB : 0 ≤ CB) : Nonempty (ModelFirstZeroGreenBudget Y Ω K ρ c₀ M Cj CB) := by
  let JB := Classical.choice (first_self_leading_high_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ)
  let RB := Classical.choice (scalar_model_raising_budget_exists hY hΩ (by omega) K ρ c₀ M Cj hK)
  obtain ⟨CW,hCW,hW⟩ := uniform_scalar_principal_connection_two_jets hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨Q0,Q1,hQ0,hQ1,hQ⟩ := uniform_model_first_zero_weight_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let CA := 3*K*CB+CW
  let CQ := 3*RB.bound
  let C := 27*(Q0*(JB.boundConstant*CQ+CA*CQ)+Q1*CA*CQ)
  have hCA : 0 ≤ CA := by dsimp only [CA];positivity
  have hCQ : 0 ≤ CQ := mul_nonneg (by norm_num) RB.nonneg
  have hC : 0 ≤ C := by dsimp only [C];have := JB.nonneg;positivity
  refine ⟨⟨JB.eta,JB.boundConstant,C,JB.eta_pos,JB.eta_le_one,JB.nonneg,hC,?_⟩⟩
  intro floor hf ε hε hSmall d hd CF CT CS P WF
  let hJ := JB.packet floor hf ε hε hSmall d hd CF CT P CB CS WF
  refine ⟨hJ,?_⟩
  intro U y hy
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβp := zero_lt_one.trans_le hβ
  have hH (b : I) : ‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε/beta d.γ d.radius y := by
    have hw := ((hW floor hf ε hε (hSmall.trans JB.eta_le_one) d hd b).2 y hy b b).1
    have hw' := hw.trans (div_le_div_of_nonneg_left (mul_nonneg hCW hε) hβp (by nlinarith only [hβ] : beta d.γ d.radius y ≤ (beta d.γ d.radius y)^2))
    have hCoord := WF.norm_coordinateAdjointHigher_le hd hK b hy
    exact ((norm_sub_le _ _).trans (add_le_add hCoord ((norm_scalar_higher_inclusion_le _).trans hw'))).trans_eq (by dsimp only [CA];ring)
  have hNorm (c b : I) : ‖modelFirstZeroAdjointWeakL d c y‖ ≤ CQ ∧ ‖modelFirstZeroAdjointWeakJet d c b y‖ ≤ CQ :=
    model_first_zero_adjoint_norm_bounds d c b y RB.bound RB.nonneg
      (RB.actual floor ε d hd y hy b c).1 (RB.actual floor ε d hd y hy b c).2
  exact model_first_zero_paired_remainder_point_bound P WF hJ U hy Q0 Q1 CA CQ CQ (beta d.γ d.radius y)
    hQ0 hQ1 hCA JB.nonneg hCQ hCQ hε hβ
    (fun k c => ⟨((hQ floor hf ε d hd k c).2 y hy 0).1,fun i => ((hQ floor hf ε d hd k c).2 y hy i).2⟩)
    hH (fun c => (hNorm c 0).1) (fun c b => (hNorm c b).2)

end ShrinkingSpheres.ParallelEnergy
