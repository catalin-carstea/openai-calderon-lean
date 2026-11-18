import Proof.BackgroundMetricSprayInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Uniform finite spray jets for every admitted background metric.
    Only one additional metric derivative is needed. -/
theorem uniform_background_spray_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    (K : ℝ) (hK : 0 < K) {m : ℕ} (M : Fin (m+1) → ℝ)
    (N : ℕ) (hNm : N+1 ≤ m) :
    ∃ S : ℝ, 1 ≤ S ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),
      Background Ω K M g g₁ g₂ e → ∀ x ∈ Ω, ∀ v : X, ‖v‖ ≤ K →
      ∀ n : ℕ, 1 ≤ n → n ≤ N → ‖iteratedFDeriv ℝ n (coordinateGeodesicSpray g) (x,v)‖ ≤ S := by
  let B := backgroundAllMetricJetBudget M
  let D := (N.factorial:ℝ)*B+1
  have hB1 : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hD1 : 1 ≤ D := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [D]
    linarith only [hh]
  have hDensity : 0 < metricDensityBudget K := by unfold metricDensityBudget;positivity
  obtain ⟨C,hC,hUniversal⟩ := exists_universalMetricSpray_jet_bound K B K
    (((metricDensityBudget K)⁻¹)^2) (by positivity) N
  let S := 1+(N.factorial:ℝ)*C*D^N
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hS : 1 ≤ S := by
    have hh : 0 ≤ (N.factorial:ℝ)*C*D^N := by positivity
    dsimp only [S]
    linarith only [hh]
  refine ⟨S,hS,?_⟩
  intro g g₁ g₂ e h x hx v hv n hn hnN
  have hg (z : X) (hz : z ∈ Ω) : ContDiffAt ℝ ∞ g z :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hz)))
  have hInput := contDiffAt_metricSprayInput g (x,v) (hg x hx)
  have hDet : (g x).det ≠ 0 := (h.1.posDef hK hx).det_pos.ne'
  have hOuter := contDiffAt_universalMetricSpray (metricSprayInput g (x,v)) hDet
  have hMem := h.metricSprayInput_mem_uniform_set hΩ hK (by omega) hx hv
  have he : universalMetricSpray ∘ metricSprayInput g =ᶠ[𝓝 (x,v)] coordinateGeodesicSpray g := by
    have hNear : ∀ᶠ p : X × X in 𝓝 (x,v), p.1 ∈ Ω :=
      continuousAt_fst.eventually (hΩ.mem_nhds hx)
    filter_upwards [hNear] with p hp
    exact universalMetricSpray_actual g p.1 p.2 (hg p.1 hp)
  rw [← (he.iteratedFDeriv ℝ n).eq_of_nhds]
  have hh := norm_iteratedFDeriv_comp_at_bound (metricSprayInput g) universalMetricSpray (x,v)
    hInput hOuter n C D
    (fun j hj => hUniversal j (hj.trans hnN) _ hMem)
    (fun j hj hjn => h.metricSprayInput_jet_bound hΩ N hNm hx j hj (hjn.trans hnN))
  have hFac : (n.factorial:ℝ) ≤ (N.factorial:ℝ) := by exact_mod_cast Nat.factorial_le hnN
  have hPow : D^n ≤ D^N := pow_le_pow_right₀ hD1 hnN
  have hCompare : (n.factorial:ℝ)*C*D^n ≤ (N.factorial:ℝ)*C*D^N := by
    gcongr
  exact hh.trans (hCompare.trans (by dsimp only [S];linarith))

end ShrinkingSpheres
