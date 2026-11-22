module

public import Proof.CalderonN.MovingTrace
public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.NormalGreenFlux

@[expose] public section

open Set Filter MeasureTheory CalderonN
open scoped ContDiff Topology

noncomputable section

namespace CalderonPaper

variable {n : ℕ}

/-- Pair the density on the reference unit sphere with the trace on the
actual normal sphere, using the probability measure. -/
def densityValue (E : (X n) × (X n) → X n) (e : Frame n) (r : X n → ℝ)
    (ψ : (X n) × (X n) → ℝ) (u : X n → ℝ) (y : X n) : ℝ :=
  ∫ w : ↥(standardSphere n), ψ (y, frameVector e y w) *
    u (endpoint E r (y, frameVector e y w)) ∂(sphereProbability n)

/-- The angular derivatives and one base derivative in a smooth
orthonormal trivialization of the sphere bundle. The ambient
representative agrees on the sphere bundle near the given point.
Its radial extension may be chosen to control the ambient norms. -/
def angularBaseJetBound (e : Frame n) (ψ : (X n) × (X n) → ℝ)
    (y : X n) (w : ↥(standardSphere n)) (C : ℕ → ℝ) : Prop :=
  ∃ H : (X n) × (X n) → ℝ, ContDiff ℝ ∞ H ∧
    H =ᶠ[𝓝[Set.univ ×ˢ standardSphere n] (y, (w : X n))]
      (fun q : (X n) × (X n) => ψ (q.1, frameVector e q.1 q.2)) ∧
    ∀ k : ℕ, ‖iteratedFDeriv ℝ k (fun v => H (y, v)) (w : X n)‖ ≤ C k ∧
      ‖iteratedFDeriv ℝ k (fun v => fderiv ℝ (fun z => H (z, v)) y) (w : X n)‖ ≤ C k

end CalderonPaper
