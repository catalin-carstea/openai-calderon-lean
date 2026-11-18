import Proof.ParallelModelFirstSourceProduct
import Proof.ConstantBoundaryCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

/-- The fixed graded lowering map is the true model raising adjoint HIGH.
It is chosen independently of profiles, packets and tests. -/
def modelFirstFlatAdjointHigher (i : I) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  flatLoweringSobolevL (3/2:ℝ) i

lemma modelFirstFlatAdjointHigher_graph (i : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelFirstFlatAdjointHigher i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  obtain ⟨Q,hQ⟩ := exists_unit_boundary_coefficient
  exact model_first_flat_lower_half_graph Q hQ i

def modelFirstFlatAdjointBudget : ℝ := ∑ i : I,‖modelFirstFlatAdjointHigher i‖

lemma modelFirstFlatAdjointBudget_nonneg : 0 ≤ modelFirstFlatAdjointBudget :=
  Finset.sum_nonneg (fun i _ => norm_nonneg _)

lemma norm_modelFirstFlatAdjointHigher_le (i : I) : ‖modelFirstFlatAdjointHigher i‖ ≤ modelFirstFlatAdjointBudget :=
  Finset.single_le_sum (fun j _ => norm_nonneg (modelFirstFlatAdjointHigher j)) (Finset.mem_univ i)

lemma model_first_raising_adjoint_norm_and_jet
    {Y Ω : Set X} {m : ℕ} (hm : 1 ≤ m) {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    {y : X} (hy : y ∈ Y) (c i : I) :
    ‖scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y‖ ≤ 3*K*modelFirstFlatAdjointBudget ∧
      ‖modelFirstRaisingAdjointJet modelFirstFlatAdjointHigher d c i y‖ ≤
        3*(9*K*|M ⟨1,by omega⟩|)*(3*K*modelFirstFlatAdjointBudget) := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hN (a : I) : ‖scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d a y‖ ≤
      3*K*modelFirstFlatAdjointBudget := by
    apply norm_weighted_sum_three_le _ _ K modelFirstFlatAdjointBudget (zero_le_one.trans hK)
    · intro j
      rw [frameCoordinateLinear_apply]
      exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hd.2.1.center_mem hy) hFrame a j
    · exact norm_modelFirstFlatAdjointHigher_le
  refine ⟨hN c,?_⟩
  apply norm_weighted_sum_three_le _ _ (9*K*|M ⟨1,by omega⟩|) _ (by positivity)
  · intro a
    exact hd.1.1.christoffel_entry_bound (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy)
      |M ⟨1,by omega⟩| (abs_nonneg _) (fun p q =>
        (hd.1.reference_fderiv_bound hm (hd.2.1.center_mem hy) p q).trans (le_abs_self _)) a i c
  · exact hN

/-- Uniform angular commutator for the COMPLETE coordinate coefficient,
with the canonical true model adjoint kept fixed before all tests. -/
theorem uniform_model_first_coordinate_raising_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ Q ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ y ∈ Y,∀ b c : I,
      ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        (framedRaisingHalfL d y (axis c)).adjoint.comp (P.firstCovariantCoordinateHigherL b y)-
          (P.firstCovariantCoordinateHalfL b y).comp
            (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y)=
          S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖S‖ ≤ Q*ε/beta d.γ d.radius y := by
  obtain ⟨η,CS,hη,hη1,hCS,hCross⟩ := uniform_full_first_derivative_raising_adjoint_cross
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,9*K^2*CS,hη,hη1,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P y hy b c
  exact model_first_coordinate_raising_commutator_point hd hK hf hCS hε P
    modelFirstFlatAdjointHigher modelFirstFlatAdjointHigher_graph hy
    (hCross floor hf ε hε hSmall d hd CF CT P y hy) b c

end ShrinkingSpheres.ParallelEnergy
