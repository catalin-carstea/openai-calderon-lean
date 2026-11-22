module

public import Proof.CalderonN.UniformBackgroundSprayJets
public import Proof.CalderonN.NormalJointHigherJetBounds

/-! Higher normal-coordinate jets, adapted from the checked Proposition
5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Every positive finite joint normal-map jet is controlled uniformly by
    ellipticity and the admitted background metric jets. The same constant
    bounds the complete phase along the geodesic and the endpoint map.
    No quantitative derivative of an arbitrary frame or radius is used. -/
theorem uniform_normalMap_higher_jet_bounds {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    (K : ℝ) (hK : 0 < K) {m : ℕ} (M : Fin (m+1) → ℝ)
    (N : ℕ) (hNm : N+1 ≤ m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g g₁ g₂ : (MetricField dim)) (e : (Frame dim)),
      Background Ω K M g g₁ g₂ e → ∀ (Y : Set (X dim)), IsOpen Y →
      ∀ (E : (X dim) × (X dim) → (X dim)) (R : (X dim) → ℝ), NormalCoordinates Y Ω g E R →
      ∀ y ∈ Y, ContinuousAt R y → ∀ v : (X dim),
      metricPair g y v v < (R y)^2 → ‖v‖ ≤ 1 →
      ∀ n : ℕ, 1 ≤ n → n ≤ N →
        (∀ t ∈ Icc (0:ℝ) 1,
          ‖iteratedFDeriv ℝ n (fun p => normalJointPhase E (p,t)) (y,v)‖ ≤ C) ∧
        ‖iteratedFDeriv ℝ n E (y,v)‖ ≤ C := by
  obtain ⟨S,hS,hSpray⟩ := uniform_background_spray_jet_bounds hΩ K hK M N hNm
  have hS0 : 0 ≤ S := zero_le_one.trans hS
  refine ⟨higherFlowJetBudget S N,one_le_higherFlowJetBudget S hS0 N,?_⟩
  intro g g₁ g₂ e h Y hY E R hN y hy hR v hv hv1 n hn hnN
  exact ⟨fun t ht => hN.joint_higher_jet_bound_of_spray_jets hY hΩ h.1 hK N S hS0
      (hSpray g g₁ g₂ e h) hy hR v hv hv1 n hn hnN ht,
    hN.expMap_higher_jet_bound_of_spray_jets hY hΩ h.1 hK N S hS0
      (hSpray g g₁ g₂ e h) hy hR v hv hv1 n hn hnN⟩

end CalderonN
