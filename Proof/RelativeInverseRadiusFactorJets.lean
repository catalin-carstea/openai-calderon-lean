import Proof.NormalFrameRelativeJetInput
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def normalFrameRelativeInverseRadiusFactor (p : NormalFrameRelativeParameter) : ℝ := (1+p.2)⁻¹

/-- The dimensionless reciprocal radius factor has a universal finite jet
    budget at relative radius zero, independent of center and frame. -/
theorem exists_relative_inverse_radius_factor_jet_bound (N : ℕ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ y : X,∀ L : X →L[ℝ] X,
      ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor ((y,L),0) ∧
      ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n normalFrameRelativeInverseRadiusFactor ((y,L),0)‖ ≤ C := by
  let f : ℝ → ℝ := fun t => (1+t)⁻¹
  have hf : ContDiffAt ℝ ∞ f 0 := (contDiffAt_const.add contDiffAt_id).inv (by norm_num)
  obtain ⟨B,hB,hBound⟩ := exists_finite_jet_bound_on_compact f {0} isCompact_singleton
    (fun x hx => by have hx0 : x=0 := mem_singleton_iff.mp hx;subst x;exact hf) N
  let C := 1+(N.factorial:ℝ)*B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro y L
  let T := ContinuousLinearMap.snd ℝ (X × (X →L[ℝ] X)) ℝ
  have hSmooth : ContDiffAt ℝ ∞ normalFrameRelativeInverseRadiusFactor ((y,L),0) :=
    hf.comp (f:=T) ((y,L),0) T.contDiff.contDiffAt
  refine ⟨hSmooth,?_⟩
  intro n hn
  have hh := iteratedFDeriv_comp_common_bound T f ((y,L),0) T.contDiff.contDiffAt hf N B 1 hB0 le_rfl
    (fun j hj => hBound j hj 0 (mem_singleton 0))
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one T (ContinuousLinearMap.norm_snd_le ℝ _ _) _ j hj) n hn
  simp only [one_pow,mul_one] at hh
  exact hh.trans (by change (N.factorial:ℝ)*B ≤ C;dsimp only [C];linarith)

end ShrinkingSpheres
