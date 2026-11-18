import Proof.ParallelFirstSelfDefectHigherPoint
import Proof.UniformActualHalfCovariantFirstForm

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

/-- The actual fibre-L2 adjoint defect has a genuine positive-half
representative of size epsilon times the H3/2 source. Constants precede
all profiles, frames, fixed compatible packets and source sections. -/
theorem uniform_first_adjoint_defect_higher_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (CB : ℝ) (hCB : 0 ≤ CB) :
    ∃ η CR : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CR ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ U : X → SphereSobolev (5/2:ℝ),ContDiffOn ℝ ∞ U Y → ∀ y ∈ Y,
      ∃ R : SphereSobolev (1/2:ℝ),
        firstAdjointDefectCoreSection P WF W U y=
          sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) R ∧
        ‖R‖ ≤ CR*ε*‖sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)‖ := by
  obtain ⟨η,CJ,hη,hη1,hCJ,hJet⟩ := uniform_complete_first_adjoint_covariant_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  let CA := 3*K*CB+CW
  let CQ := 27*K*|M ⟨1,by omega⟩|
  let CR := 3*(CJ+CQ*CA)
  have hCA : 0 ≤ CA := by dsimp only [CA];positivity
  have hCQ : 0 ≤ CQ := by dsimp only [CQ];positivity
  refine ⟨η,CR,hη,hη1,by dsimp only [CR];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS CG CK P WF W U hU y hy
  have hε1 := hSmall.trans hη1
  have hβ : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβ2 : 1 ≤ (beta d.γ d.radius y)^2 := by nlinarith only [hβ]
  have hA (b : I) : ‖WF.covariantCoordinateAdjointHigher b y‖ ≤ CA*ε := by
    have hw := ((hWeight floor hf ε hε hε1 d hd b).2 y hy b b).1
    have hw' := hw.trans (div_le_self (mul_nonneg hCW hε) hβ2)
    have hCoord := (WF.norm_coordinateAdjointHigher_le hd hK b hy).trans
      (div_le_self (by positivity : 0 ≤ (3*K*CB)*ε) hβ)
    exact ((norm_sub_le _ _).trans (add_le_add hCoord
      ((norm_scalar_higher_inclusion_le _).trans hw'))).trans_eq (by dsimp only [CA];ring)
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hμ : 0 < metricDensity d.γ y := metricDensity_pos hg (zero_lt_one.trans_le hK) hy
  have hq (b : I) : |(metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)| ≤ CQ := by
    have hRaw := hd.relative_density_axis_bound hΩ (by omega) (zero_lt_one.trans_le hK) hy b
    change |fderiv ℝ (metricDensity d.γ) y (axis b)| ≤ CQ*metricDensity d.γ y at hRaw
    rw [abs_mul,abs_inv,abs_of_pos hμ]
    calc
      _ ≤ (metricDensity d.γ y)⁻¹*(CQ*metricDensity d.γ y) :=
        mul_le_mul_of_nonneg_left hRaw (inv_nonneg.mpr hμ.le)
      _ = CQ := by field_simp
  have hJ := hJet floor hf ε hε hSmall d hd CF CT P CB CS WF
  choose H hH hHN using (fun b : I => hJ.jet b b y hy)
  refine ⟨firstAdjointDefectHigherPoint WF H U y,
    firstAdjointDefectHigherPoint_graph hY hΩ hSub hd (zero_lt_one.trans_le hK) P WF W U hU hy H hH,?_⟩
  exact norm_firstAdjointDefectHigherPoint_le WF H U y hCA hCQ hε hA hHN hq

end ShrinkingSpheres.ParallelEnergy
