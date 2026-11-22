module

public import Proof.CalderonN.BallRegularity.Spaces

import Proof.CalderonN.WholeSpaceVariableH2
import Mathlib.Tactic

/-! Fixed-ball specialization of the entrywise weak energy estimate
from `WeakEnergyEntryNorm` in the Proposition 5.3 release. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

noncomputable local instance : SeminormedAddCommGroup (FixedBallH1 dim) := inferInstance

noncomputable local instance : NormedSpace ℝ (FixedBallH1 dim) := inferInstance

/-- The local coefficient entries on the unit ball control the full
weak energy, including tests with nonzero Dirichlet trace. -/
theorem norm_fixedBall_weakEnergy_entrywise_le {a : X dim → Mat dim}
    (ha : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)))
    (q : ℝ) (hq : 0 ≤ q) (hEntry : ∀ x ∈ (fixedBallOpens dim : Set (X dim)), ∀ i j, |a x i j| ≤ q) :
    ‖(TauCeti.PDE.energyFormH1L ha : FixedBallH1 dim →L[ℝ] FixedBallH1 dim →L[ℝ] ℝ)‖ ≤
      (dim : ℝ)^2*q := by
  have hDot (x : X dim) (hx : x ∈ (fixedBallOpens dim : Set (X dim))) (eta xi : X dim) :
      |eta ⬝ᵥ (a x *ᵥ xi)| ≤ ((dim : ℝ)^2*q)*‖eta‖*‖xi‖ := by
    simpa only [Fintype.card_fin] using
      OAI.AnisotropicCalderon.Regularity.abs_dotProduct_mulVec_le_of_entry (a x) (hEntry x hx) eta xi
  have h := TauCeti.PDE.norm_energyFormH1L_le_of_bounds (a := a)
    (b := fun _ => (0 : X dim)) (c := fun _ => (0 : ℝ)) (Lam := (dim : ℝ)^2*q) (beta := 0) (gamma := 0)
    ha (by positivity) hDot le_rfl le_rfl (fun _ _ => by simp) (fun _ _ => by simp)
  simpa only [add_zero] using h

end CalderonN
