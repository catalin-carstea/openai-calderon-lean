import Proof.ParallelModelFirstHodgeBound
import Proof.ParallelModelFirstJetPoint
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

/-- All genuine commutator/Hodge/first-jet remainders for the paired
model/first leading density, with constants before arbitrary profiles and
ANY fixed compatible WF/W. No second adjoint HIGH jet is required. -/
theorem uniform_model_first_leading_remainder_component_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CB : ℝ) (hCB : 0 ≤ CB) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ U : X → SphereSobolev (5/2:ℝ),ContDiff ℝ ∞ U → ∀ y ∈ Y,
      |modelFirstAngularCommutatorDensity P WF U y+modelFirstHodgeRemainder WF U y+modelFirstJetDensity P WF W U y| ≤
        C*ε*metricDensity d.γ y*∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i) := by
  let LB := Classical.choice (first_self_leading_low_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ)
  let JB := Classical.choice (first_self_leading_high_budget hY hΩ hSub hm K ρ c₀ M Cj hK hρ)
  let SB := Classical.choice (first_self_leading_scalar_budget hY hΩ (by omega) K ρ c₀ M Cj hK)
  let RB := Classical.choice (scalar_model_raising_budget_exists hY hΩ (by omega) K ρ c₀ M Cj hK)
  obtain ⟨ηX,QX,hηX,hηX1,hQX,hX⟩ := uniform_model_first_coordinate_raising_commutator hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨QW,hQW,hWeight⟩ := uniform_model_first_leading_weight_jets hY hΩ hSub (by omega) K ρ c₀ M Cj hK
  let CA := 3*K*CB+SB.boundConstant
  let RA := 3*K*modelFirstFlatAdjointBudget
  let RJ := 3*(9*K*|M ⟨1,by omega⟩|)*RA
  let CQ := 3*Real.sqrt 2*curvatureBudget K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
  let CC := 54*K*QX
  let CJ := 27*K*(4*RB.bound*JB.boundConstant+4*LB.boundConstant*RJ+2*RJ*JB.boundConstant)
  let CH := 27*RA*(K*CQ*(CA+LB.boundConstant)+2*QW*(2*(CA+LB.boundConstant)+JB.boundConstant))
  let C := CC+CH+CJ
  let η := min (min LB.eta JB.eta) ηX
  have hCA : 0 ≤ CA := by dsimp only [CA];have := SB.nonneg;positivity
  have hRA : 0 ≤ RA := by dsimp only [RA];exact mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK)) modelFirstFlatAdjointBudget_nonneg
  have hRJ : 0 ≤ RJ := by dsimp only [RJ];positivity
  have hCQ : 0 ≤ CQ := by
    have hCurv := curvatureBudget_nonneg K |M 0| |M ⟨1,by omega⟩| |M ⟨2,by omega⟩|
      (zero_le_one.trans hK) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    dsimp only [CQ];positivity
  have hCC : 0 ≤ CC := by dsimp only [CC];positivity
  have hCJ : 0 ≤ CJ := by dsimp only [CJ];have := RB.nonneg;have := JB.nonneg;have := LB.nonneg;positivity
  have hCH : 0 ≤ CH := by dsimp only [CH];have := LB.nonneg;have := JB.nonneg;positivity
  refine ⟨η,C,lt_min (lt_min LB.eta_pos JB.eta_pos) hηX,
    (min_le_left _ _).trans ((min_le_left _ _).trans LB.eta_le_one),by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS CG CK P WF W U hU y hy
  have hεL := hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεJ := hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεX := hSmall.trans (min_le_right _ _)
  have hε1 := hεL.trans LB.eta_le_one
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hA (b : I) : ‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε := by
    have hCoord := (WF.norm_coordinateAdjointHigher_le hd hK b hy).trans
      (div_le_self (by positivity : 0 ≤ (3*K*CB)*ε) hβ)
    have hw := SB.bound floor hf ε hε hε1 d hd b y hy
    exact ((norm_sub_le _ _).trans (add_le_add hCoord
      ((norm_scalar_higher_inclusion_le _).trans hw))).trans_eq (by dsimp only [CA];ring)
  have hLow (b : I) := LB.bound floor hf ε hε hεL d hd CF CT P b y hy
  have hLowWeak (b : I) : ‖P.firstCovariantCoordinateHalfL b y‖ ≤ LB.boundConstant*ε :=
    (hLow b).trans (div_le_self (mul_nonneg LB.nonneg hε) hβ)
  have hPoint := first_self_adjoint_source_point_bounds hY hΩ hd (zero_lt_one.trans_le hK) P WF W U hU.contDiffOn
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub (zero_lt_one.trans_le hK)) hy JB.nonneg hε hA hLowWeak
    (JB.packet floor hf ε hε hεJ d hd CF CT P CB CS WF)
  have hAdj (c : I) : ‖scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y‖ ≤ RA :=
    (model_first_raising_adjoint_norm_and_jet (by omega) hd hK hy c 0).1
  have hAdjJet (c i : I) : ‖modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c i y‖ ≤ RJ :=
    (model_first_raising_adjoint_norm_and_jet (by omega) hd hK hy c i).2
  have hCurv (k b : I) : ‖frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y (axis k) (axis b)‖ ≤ CQ := by
    simpa only [norm_axis,mul_one] using hd.1.norm_frameCurvatureSobolevL_le (1/2:ℝ) hΩ hK (by omega) (hSub hy) (axis k) (axis b)
  have hC := model_first_actual_commutator_point_bound hd hK hf hQX hε P WF U hy
    (hU.differentiable (by simp) y) (fun c b => hX floor hf ε hε hεX d hd CF CT P y hy b c)
  have hH := model_first_actual_hodge_remainder_point_bound hd hK hf hRA hCA LB.nonneg JB.nonneg hQW hCQ hε P WF W U hy hAdj hPoint
    (fun k c => ⟨(hWeight floor ε d hd k c).2 y hy 0 |>.1,fun i => ((hWeight floor ε d hd k c).2 y hy i).2⟩) hCurv
  have hJ := model_first_actual_jet_point_bound hY hΩ hd hK hf RB.nonneg hRJ LB.nonneg JB.nonneg hε P WF W U hU.contDiffOn hy
    (fun c => (RB.actual floor ε d hd y hy 0 c).1) hAdjJet hLow hPoint
  have hTriangle := (abs_add_le (modelFirstAngularCommutatorDensity P WF U y+modelFirstHodgeRemainder WF U y)
    (modelFirstJetDensity P WF W U y)).trans (add_le_add (abs_add_le _ _) le_rfl)
  exact hTriangle.trans ((add_le_add (add_le_add hC hH) hJ).trans_eq (by dsimp only [C,CC,CH,CJ,RA,RJ,CA,CQ];ring))

end ShrinkingSpheres.ParallelEnergy
