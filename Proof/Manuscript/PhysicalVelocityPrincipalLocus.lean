module

public import Proof.Manuscript.MovingTrace.MovingAdjointOperatorAssembly
public import Proof.Manuscript.MovingTrace.PhysicalPrincipalRadiusJet
public import Proof.Manuscript.MovingTrace.SignedGeometryDirections
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric
open scoped ContDiff

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "d" => n+1
local notation "Z" => X (n+1)
local notation "P" => MovingSymbolGeometry (n+1)

/-- The principal coefficient of the first radius variation vanishes at
all geometry values at which an admitted physical radius is evaluated. -/
theorem velocityPrincipalSymbol_zero_on_physicalLocus
    {Y Ω : Set Z} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ g₁ g₂ : ℝ → MetricField d} {e : ℝ → Frame d} {E : ℝ → Z × Z → Z}
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (Z × Z) => E q.1 q.2))
    {K : ℝ} (hK : 0 < K) {m : ℕ} {M : Fin (m+1) → ℝ}
    (hbg : ∀ lam ∈ Icc (0:ℝ) 1, Background Ω K M (γ lam) (g₁ lam) (g₂ lam) (e lam))
    {ρ B δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hN : ∀ lam ∈ Icc (0:ℝ) 1, NormalCoordinates (closure Y) Ω (γ lam) (E lam) (fun _ => ρ))
    {G : BallPoissonTube P d} (A : SmoothRadialVelocity G)
    (hJA : signedGeometryCompact Y ρ B δ ⊆ A.U)
    (hG : G.g = radializedNormalFamily (fun p => symmetrizedNormalMetric g₁ E e (p.1.1,p.2)))
    (i : I d)
    (hV : ∀ q : P × Z, q.1.1.1 ∈ Icc 0 1 → q.1.1.2.1 ∈ closure Y →
      A.velocity q = physicalSignedVelocity γ E e i q) :
    ∀ C : SignedPoissonCollar G, ∀ χ ζ : X n → ℂ,
      ∀ p ∈ movingSymbolPhysicalLocus Y ρ B, ∀ x ξ : X n, ξ ≠ 0 →
        HasDerivAt (fun r => C.velocityPrincipalSymbol A χ ζ
          (movingSymbolSignedRadiusEquiv d (((movingSymbolSignedRadiusEquiv d).symm p).1,r),x) ξ) 0 0 := by
  intro C χ ζ p hp x ξ hξ
  rcases p with ⟨⟨lam,y,s⟩,b⟩
  have hlam : lam ∈ Icc (0:ℝ) 1 := hp.1.1.1
  have hy : y ∈ Y := hp.2
  have hp₀ : ((lam,y,0),b) ∈ A.U := hJA
    (signedGeometryCompact_radius_line_mem hp.1 ⟨neg_nonpos.mpr hδ,hρ.le⟩)
  exact C.velocityPrincipalSymbol_physical_first_zero hY hΩ lam (hbg lam hlam) hK
    (hE.comp ((contDiff_const (c := lam)).prodMk contDiff_id))
    ((hN lam hlam).mono_centers subset_closure) A hG i hy b hp₀
    (fun r z => hV (((lam,y,r),b),z) hlam (subset_closure hy)) χ ζ x ξ hξ

end CalderonPaper
