import Proof.CoarseDegreeFamilyJets
import Proof.SmoothFiniteJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.CoarseDegreeCompatibility
open OAI.AnisotropicCalderon.SphereHarmonic
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The canonical closed-graph half extraction preserves rescaled jets of
    the SAME data family. Its domain choices are identified as genuine germs. -/
lemma halfFamily_composition_jet_bound
    (f : E → CoarseDegreeData) (V : Set E) (hV : IsOpen V)
    (hConstraint : ∀ x ∈ V,∀ z,constraintL z (f x) = 0) (hf : ContDiffOn ℝ ∞ f V)
    (Φ : P → E) (hΦ : ContDiff ℝ ∞ Φ) {p : P} (hp : Φ p ∈ V) {N : ℕ} {B : ℝ}
    (hData : SmoothFiniteJetBound (f ∘ Φ) p N B) :
    SmoothFiniteJetBound (halfFamily f V hConstraint ∘ Φ) p N ((12*Real.sqrt 2)*B) := by
  let W := Φ ⁻¹' V
  have hW : IsOpen W := hV.preimage hΦ.continuous
  have hpW : p ∈ W := hp
  have hC : ∀ x ∈ W,∀ z,constraintL z ((f ∘ Φ) x) = 0 := fun x hx => hConstraint (Φ x) hx
  have hSmooth : ContDiffOn ℝ ∞ (f ∘ Φ) W := hf.comp hΦ.contDiffOn (fun x hx => hx)
  have hGerm : (halfFamily f V hConstraint ∘ Φ) =ᶠ[𝓝 p]
      halfFamily (f ∘ Φ) W hC := by
    filter_upwards [hW.mem_nhds hpW] with x hx
    change halfExtractorL (restriction f V hConstraint (Φ x)) =
      halfExtractorL (restriction (f ∘ Φ) W hC x)
    rfl
  have hB := hData.nonneg
  have hHalfS : ContDiffAt ℝ ∞ (halfFamily f V hConstraint ∘ Φ) p :=
    ((contDiffOn_halfFamily f V hV hConstraint hf).contDiffAt (hV.mem_nhds hp)).comp p hΦ.contDiffAt
  refine ⟨by positivity,hHalfS,?_⟩
  intro n hn
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  exact norm_iteratedFDeriv_halfFamily_le (f ∘ Φ) W hW hC hSmooth p hpW B hB n (hData.bound n hn)
end ShrinkingSpheres.CoarseDegreeCompatibility
