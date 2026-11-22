module

public import Proof.Manuscript.MovingTrace.ActualRadialVelocityModel
public import Proof.Manuscript.MovingTrace.VelocityPrincipalRadius
public import Proof.Manuscript.PhysicalCollarPrincipalZero
public import Proof.Manuscript.PhysicalVelocityFirstRadius
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "d" => n+1
local notation "Z" => X (n+1)
local notation "P" => MovingSymbolGeometry (n+1)

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

/-- The radius derivative of the actual normalized response's principal
symbol vanishes after holding the physical velocity slope fixed. -/
theorem velocityPrincipalSymbol_physical_first_zero
    {Y Ω : Set Z} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g q : ℝ → MetricField d} {K : ℝ} {m : ℕ} {B : Fin (m+1) → ℝ}
    {e : ℝ → Frame d} {E : ℝ → Z × Z → Z}
    (lam : ℝ) (hB : Background Ω K B (γ lam) (g lam) (q lam) (e lam)) (hK : 0 < K)
    (hE : ContDiff ℝ ∞ (E lam)) {R : Z → ℝ}
    (hN : NormalCoordinates Y Ω (γ lam) (E lam) R)
    {G : BallPoissonTube P d} (C : SignedPoissonCollar G) (A : SmoothRadialVelocity G)
    (hG : G.g = radializedNormalFamily (fun p => symmetrizedNormalMetric g E e (p.1.1,p.2)))
    (i : I d) {y : Z} (hy : y ∈ Y) (b : ℝ) (hp₀ : ((lam,y,0),b) ∈ A.U)
    (hV : ∀ r z, A.velocity (((lam,y,r),b),z) =
      scaledNormalTraceVelocity (γ lam) (E lam) (e lam) y r b z (axis i))
    (χ ζ : X n → ℂ) (x ξ : X n) (hξ : ξ ≠ 0) :
    HasDerivAt (fun r : ℝ => C.velocityPrincipalSymbol A χ ζ (((lam,y,r),b),x) ξ) 0 0 := by
  have hν : ‖ξ‖⁻¹ • ξ ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hξ)) hξ
  have hκ := signedPoissonCollar_kappa_first_radius_zero hΩ lam hB hK hE hN hy C hG b
    (A.subset hp₀) x (‖ξ‖⁻¹ • ξ) hν
  have hFrame (z : Z) (hz : z ∈ Y) (j k : I d) :
      metricPair (γ lam) z (e lam z j) (e lam z k) = if j=k then 1 else 0 :=
    hB.2.2.2.2.2.2.2 z (hN.center_mem hz) j k
  have hVel := scaledNormalTraceVelocity_first_radius_zero hY hΩ hB.1 hE hN hFrame hy b
    (angularPoint C.pole x) (axis i)
  exact C.velocityPrincipalSymbol_first_zero A χ ζ (fun r => ((lam,y,r),b)) x ξ hκ
    (hVel.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hV r _))

end SignedPoissonCollar
end CalderonPaper
