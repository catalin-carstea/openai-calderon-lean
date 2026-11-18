import Proof.NormalFrameHorizontalRescaling
import Proof.NormalFrameScaledFiniteJetBound
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma normalFrame_scaled_parameter_three_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : ℝ) (hβ : 1 ≤ β) (y : X) (L : X →L[ℝ] X)
    {F : NormalFrameRelativeParameter → E} {B : ℝ}
    (hF : SmoothFiniteJetBound F ((y,L),0) 3 B) :
    SmoothFiniteJetBound (F ∘ normalFrameRelativeScaledParameter β y) ((0,L),0) 3 (6*B) := by
  let p0 : NormalFrameRelativeParameter := ((0,L),0)
  let Φ := normalFrameRelativeScaledParameter β y
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  let e := normalFrameParameterScaleEquiv β hβpos.ne'
  let b : NormalFrameRelativeParameter := ((y,0),0)
  have hPhi : Φ = fun p => b+e p := normalFrameRelativeScaledParameter_affine β hβpos.ne' y
  have hPoint : Φ p0 = ((y,L),0) := normalFrameRelativeScaledParameter_point β y L
  have hPhiSmooth : ContDiffAt ℝ ∞ Φ p0 := by
    rw [hPhi]
    exact contDiffAt_const.add e.toContinuousLinearMap.contDiff.contDiffAt
  have hFPoint : ContDiffAt ℝ ∞ F (Φ p0) := by rw [hPoint];exact hF.smooth
  have hB := hF.nonneg
  refine ⟨by positivity,hFPoint.comp p0 hPhiSmooth,?_⟩
  intro n hn
  have hh := iteratedFDeriv_comp_common_bound Φ F p0 hPhiSmooth hFPoint 3 B 1 hB le_rfl
    (fun k hk => by rw [hPoint];exact hF.bound k hk)
    (fun k hk hkn => by
      rw [hPhi]
      change ‖iteratedFDeriv ℝ k (fun p => b+e.toContinuousLinearMap p) p0‖ ≤ 1
      rw [norm_iteratedFDeriv_affine_clm_positive e.toContinuousLinearMap b p0 k hk]
      split_ifs
      · exact norm_normalFrameParameterScaleEquiv_le_one hβ
      · norm_num) n hn
  norm_num only [Nat.factorial,one_pow,mul_one] at hh
  exact hh

/-- A bound obtained AFTER beta rescaling gives the actual horizontal
    three-jets. This also applies to products containing the log-radius covector. -/
lemma ordered_normalFrame_horizontal_bound_of_scaled_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y : X) (a : ℕ → X) (D B : ℝ) (hD : 1 ≤ D)
    (hβ : 1 ≤ beta d.γ d.radius y) (F : NormalFrameRelativeParameter → E)
    (hFs : SmoothFiniteJetBound (F ∘ normalFrameRelativeScaledParameter (beta d.γ d.radius y) y)
      ((0,frameVectorLinear d.frame y),0) 3 B)
    (hV : ∀ j,ContDiffAt ℝ ∞
      (normalFrameRelativeScaledHorizontalField d.γ d.radius (beta d.γ d.radius y) y (a j))
      ((0,frameVectorLinear d.frame y),0))
    (hVJets : ∀ j : ℕ,j < 3 → ∀ k : ℕ,k+1 ≤ 3 →
      ‖iteratedFDeriv ℝ k (normalFrameRelativeScaledHorizontalField d.γ d.radius (beta d.γ d.radius y) y (a j))
        ((0,frameVectorLinear d.frame y),0)‖ ≤ D)
    (n : ℕ) (hn : n ≤ 3) :
    ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n
      ((y,frameVectorLinear d.frame y),0)‖ ≤ (8*D)^3*B*(beta d.γ d.radius y)^n := by
  simpa only [show (2:ℝ)^3=8 by norm_num] using
    ordered_normalFrame_horizontal_bound_of_scaled_finite_jets 3 d y a D B hD hβ F hFs hV hVJets n hn
end ShrinkingSpheres
