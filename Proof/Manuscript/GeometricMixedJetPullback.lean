module

public import Proof.Manuscript.SeparatedAngularJets

import Proof.CalderonN.PhysicalTraceScalarJets
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {X P B E V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pull back a free geometry jet along one admitted profile, with a factor
of beta for each base derivative and no loss in the covector order. -/
theorem geometricMixedJet_pullback_le
    {a : P × B → E → V} {O : Set ((P × B) × E)} (hO : IsOpen O)
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) O)
    {p : X → P} {y : X} (hp : ContDiffAt ℝ ∞ p y) (x : B) (ξ : E)
    (hm : ((p y,x),ξ) ∈ O)
    {β D C : ℝ} (hβ : 1 ≤ β) (hD : 1 ≤ D)
    (j k l : ℕ)
    (hP : ∀ n ≤ j, ‖iteratedFDeriv ℝ n p y‖ ≤ D*β^n)
    (hA : ∀ n ≤ j+k, ‖angularMixedJet n l a (p y,x) ξ‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun b => iteratedFDeriv ℝ k
      (fun x' => iteratedFDeriv ℝ l (a (p b,x')) ξ) x) y‖ ≤
      ((j.factorial:ℝ)*C*D^j) * β^j := by
  let G (u : P) (z : B) := iteratedFDeriv ℝ l (a (u,z)) ξ
  let A (u : P) := iteratedFDeriv ℝ k (G u) x
  let p₀ (z : X) := p (y+β⁻¹ • z)
  have hβp := zero_lt_one.trans_le hβ
  have hG : ContDiffAt ℝ ∞ (Function.uncurry G) (p y,x) := by
    have h₁ := contDiffAt_iteratedFDeriv_snd (ha.contDiffAt (hO.mem_nhds hm)) l
    exact h₁.comp (p y,x) (contDiffAt_id.prodMk contDiffAt_const)
  have hAS : ContDiffAt ℝ ∞ A (p y) :=
    (contDiffAt_iteratedFDeriv_snd hG k).comp (p y) (contDiffAt_id.prodMk contDiffAt_const)
  have hNear : ∀ᶠ z : P × B in 𝓝 (p y,x),
      ContDiffAt ℝ ∞ (Function.uncurry a) (z,ξ) := by
    have hC : Continuous (fun z : P × B => (z,ξ)) := continuous_id.prodMk continuous_const
    filter_upwards [hC.continuousAt.eventually (hO.mem_nhds hm)] with z hz
    exact ha.contDiffAt (hO.mem_nhds hz)
  have hAb : ∀ n ≤ j, ‖iteratedFDeriv ℝ n A (p y)‖ ≤ C := by
    intro n hn
    exact (separatedAngularJets_le_joint hNear n k l).trans (hA (n+k) (Nat.add_le_add_right hn k))
  have hAB : LocalSmoothJetBudget A (p₀ 0) j C := by
    simp only [p₀,smul_zero,add_zero]
    exact ⟨hAS,hAb⟩
  have hPb : LocalSmoothJetBudget p₀ 0 j D :=
    localSmoothJetBudget_scaled_chart hβ hp hP
  have hJ := hPb.comp hAB hD
  exact localSmoothJetBudget_scaled_chart_bound hβ hJ j le_rfl

end CalderonPaper
