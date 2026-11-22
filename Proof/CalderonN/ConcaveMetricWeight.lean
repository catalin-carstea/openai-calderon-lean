module

public import Proof.CalderonN.StrictMetricWeight
public import Proof.CalderonN.ExponentialBalancing

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

open Elliptic

/-- The same estimate for the concave phase (s-kappa s^2), uniformly
including (kappa=0) and nearby coefficient parameters. -/
theorem exists_concave_metricCarleman {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {g : P → (MetricField dim)} {θ : P → (X dim) → ℝ}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : P × (X dim) => g q.1 q.2 i j))
    (hp : ∀ a x, (g a x).PosDef) (hθ : ContDiff ℝ ∞ (fun q : P × (X dim) => θ q.1 q.2))
    (a₀ : P) (x₀ : (X dim)) (hs : StrictMetricWeightAt (g a₀) (θ a₀) x₀) :
    ∃ r C τ₀ : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ₀ ∧
      ∀ a ∈ closedBall a₀ r, ∀ κ : ℝ, |κ| ≤ r →
      ∀ τ : ℝ, τ₀ ≤ τ → ∀ w : (X dim) → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ closedBall x₀ r →
        τ * (∫ x, ∑ i, coordDeriv i (fun y => Real.exp (τ * strictHeight κ (θ a y)) * w y) x ^ 2) +
        τ^3 * (∫ x, (Real.exp (τ * strictHeight κ (θ a x)) * w x)^2) ≤
          C * ∫ x, Real.exp (2*(τ * strictHeight κ (θ a x))) *
            (chartVolume (g a) x * laplace (g a) w x)^2 := by
  let π (q : (P × ℝ) × (X dim)) : P × (X dim) := (q.1.1,q.2)
  have hπ : ContDiff ℝ ∞ π := (contDiff_fst.fst).prodMk contDiff_snd
  have hθ' : ContDiff ℝ ∞ (fun q : (P × ℝ) × (X dim) => θ q.1.1 q.2) := hθ.comp hπ
  let φ (a : P × ℝ) (x : (X dim)) := strictHeight a.2 (θ a.1 x)
  have hφ : ContDiff ℝ ∞ (fun q : (P × ℝ) × (X dim) => φ q.1 q.2) := by
    exact hθ'.sub ((contDiff_fst.snd).mul (hθ'.pow 2))
  have hφ0 : φ (a₀,0) = θ a₀ := by
    funext x
    simp [φ, strictHeight]
  have hs' : StrictMetricWeightAt (g (a₀, (0 : ℝ)).1) (φ (a₀,0)) x₀ := by
    rw [hφ0]
    exact hs
  obtain ⟨r,C,τ₀,hr,hC,hτ,hCar⟩ :=
    exists_local_metricCarleman (g := fun a : P × ℝ => g a.1)
      (fun i j => (hg i j).comp hπ) (fun a x => hp a.1 x) hφ (a₀,0) x₀ hs'
  refine ⟨r,C,τ₀,hr,hC,hτ, fun a ha κ hκ τ ht w hw hwc hwr => ?_⟩
  have hpair : (a,κ) ∈ closedBall (a₀,(0 : ℝ)) r := by
    rw [mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, sub_zero]
    exact ⟨mem_closedBall.mp ha,hκ⟩
  exact hCar (a,κ) hpair τ ht w hw hwc hwr

end CalderonN
