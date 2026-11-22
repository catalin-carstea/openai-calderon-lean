module

public import Proof.Manuscript.ScalarConductivityDefs

import Proof.Manuscript.AnisotropicUniqueness
import Proof.Manuscript.BoundaryPatchDensity
import Proof.Manuscript.Lemma81
import Proof.Manuscript.LocalExtensions
import Proof.Manuscript.ConformalPolynomial
import Proof.Manuscript.ScalarConformalEnergy
import Proof.Manuscript.ScalarCoordinates
import Proof.Manuscript.ScalarGauge
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

public section

noncomputable section
open Set MeasureTheory CalderonPatch
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace CalderonPaper

/-- Corollary 1.3. Smooth scalar uniqueness from one patch. -/
theorem corollary13 {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    [ChartedSpace (EuclideanHalfSpace n) ↥(closure Ω)]
    [IsManifold (𝓡∂ n) ∞ ↥(closure Ω)] (D : EuclideanClosure Ω)
    {Γ : Set ↥(frontier Ω)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty)
    {γ₁ γ₂ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hγ₁ : SmoothThrough (closure Ω) γ₁) (hγ₂ : SmoothThrough (closure Ω) γ₂)
    (hpos₁ : ∀ x ∈ closure Ω, 0 < γ₁ x) (hpos₂ : ∀ x ∈ closure Ω, 0 < γ₂ x)
    (hDN : ScalarPatchEnergyEqual D hΩ γ₁ γ₂ Γ) :
    EqOn γ₁ γ₂ (closure Ω) := by

  let : CompactSpace ↥(closure Ω) := isCompact_iff_compactSpace.mp hbounded.isCompact_closure
  let : ConnectedSpace ↥(closure Ω) := isConnected_iff_connectedSpace.mp hconn.closure
  let B := ↥((𝓡∂ n).boundary ↥(closure Ω))
  let native : Set B := D.boundaryCoordinate hΩ ⁻¹' Γ
  have ho : IsOpen native := hΓ.preimage (D.continuous_boundaryCoordinate hΩ)
  have hne : native.Nonempty := by
    obtain ⟨q, hq⟩ := hΓne
    obtain ⟨p, hp⟩ := D.surjective_boundaryCoordinate hΩ q
    exact ⟨p, show D.boundaryCoordinate hΩ p ∈ Γ by rwa [hp]⟩
  obtain ⟨Γ₀, h₀open, h₀ne, h₀proper, h₀sub⟩ :
      ∃ P : Set B, IsOpen P ∧ P.Nonempty ∧ P ≠ univ ∧ P ⊆ native := by
    by_cases he : native = univ
    · obtain ⟨q, _⟩ := hne
      let : Nonempty B := ⟨q⟩
      have hd : Dense ({q}ᶜ : Set B) := boundary_compl_singleton_dense (n := n) (by omega) q
      refine ⟨{q}ᶜ, isClosed_singleton.isOpen_compl, hd.nonempty, ?_, he ▸ subset_univ _⟩
      intro hh
      have hq : q ∈ ({q}ᶜ : Set B) := hh ▸ mem_univ q
      exact hq rfl
    · exact ⟨native, ho, hne, he, Subset.rfl⟩
  let ψ₁ := conductivityExponent n γ₁
  let ψ₂ := conductivityExponent n γ₂
  have hψ₁ : SmoothThrough (closure Ω) ψ₁ := smoothThrough_conductivityExponent hγ₁ hpos₁
  have hψ₂ : SmoothThrough (closure Ω) ψ₂ := smoothThrough_conductivityExponent hγ₂ hpos₂
  let σ₁ := ψ₁ ∘ (Subtype.val : ↥(closure Ω) → EuclideanSpace ℝ (Fin n))
  let σ₂ := ψ₂ ∘ (Subtype.val : ↥(closure Ω) → EuclideanSpace ℝ (Fin n))
  have hs₁ := D.contMDiff_restrict hψ₁
  have hs₂ := D.contMDiff_restrict hψ₂
  let g₁ := expScaledMetric D.metric σ₁ hs₁
  let g₂ := expScaledMetric D.metric σ₂ hs₂
  let μ₁ := expScaledVolume (n := n) D.volume σ₁
  let μ₂ := expScaledVolume (n := n) D.volume σ₂
  have hμ₁ : IsMetricVolume g₁ μ₁ := isMetricVolume_expScaled D.metric D.volume D.volume_isMetricVolume σ₁ hs₁
  have hμ₂ : IsMetricVolume g₂ μ₂ := isMetricVolume_expScaled D.metric D.volume D.volume_isMetricVolume σ₂ hs₂
  have hdenom : ((n : ℝ) - 2) ≠ 0 := by
    have : (2 : ℝ) < n := by exact_mod_cast (by omega : 2 < n)
    exact sub_ne_zero.mpr this.ne'
  have hExp (γ : EuclideanSpace ℝ (Fin n) → ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : 0 < γ x) :
      Real.exp (((n : ℝ) - 2) * conductivityExponent n γ x) = γ x := by
    rw [conductivityExponent, ← mul_div_assoc, mul_div_cancel_left₀ _ hdenom, Real.exp_log hx]
  have hγ₁exp : (fun x : ↥(closure Ω) => Real.exp (((n : ℝ) - 2) * σ₁ x)) = γ₁ ∘ Subtype.val :=
    funext fun x => hExp γ₁ (hpos₁ x x.property)
  have hγ₂exp : (fun x : ↥(closure Ω) => Real.exp (((n : ℝ) - 2) * σ₂ x)) = γ₂ ∘ Subtype.val :=
    funext fun x => hExp γ₂ (hpos₂ x x.property)
  have hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ₀ := by
    intro f hf hSupp
    change dirichletQuadraticEnergy (expScaledMetric D.metric σ₁ hs₁)
        (expScaledVolume (n := n) D.volume σ₁) f =
      dirichletQuadraticEnergy (expScaledMetric D.metric σ₂ hs₂)
        (expScaledVolume (n := n) D.volume σ₂) f
    rw [expScaledEnergy_eq_conductivity, expScaledEnergy_eq_conductivity, hγ₁exp, hγ₂exp]
    exact hDN f hf (hSupp.trans h₀sub)
  obtain ⟨Φ, hΦfix, hΦmetric⟩ :=
    smoothAnisotropicUniqueness (M := ↥(closure Ω)) hn h₀open h₀ne h₀proper hμ₁ hμ₂ hEnergy
  let F := closureSelfMap Φ
  let H := closureSelfMap Φ.symm
  let b (x : EuclideanSpace ℝ (Fin n)) := ψ₂ x - ψ₁ (F x)
  let d (x : EuclideanSpace ℝ (Fin n)) := ψ₁ x - ψ₂ (H x)
  have hFi : MapsTo F Ω Ω := D.closureSelfMap_mapsTo_interior Φ
  have hHi : MapsTo H Ω Ω := D.closureSelfMap_mapsTo_interior Φ.symm
  have hFc : ContinuousOn F (closure Ω) := closureSelfMap_continuousOn Φ Φ.continuous
  have hHc : ContinuousOn H (closure Ω) := closureSelfMap_continuousOn Φ.symm Φ.symm.continuous
  have hFs : ContDiffOn ℝ ∞ F Ω := D.closureSelfMap_smooth_on_interior Φ Φ.contMDiff
  have hHs : ContDiffOn ℝ ∞ H Ω := D.closureSelfMap_smooth_on_interior Φ.symm Φ.symm.contMDiff
  have hbc : ContinuousOn b (closure Ω) :=
    hψ₂.continuousOn.sub (hψ₁.continuousOn.comp hFc (closureSelfMap_mapsTo Φ))
  have hdc : ContinuousOn d (closure Ω) :=
    hψ₁.continuousOn.sub (hψ₂.continuousOn.comp hHc (closureSelfMap_mapsTo Φ.symm))
  have hbs : ContDiffOn ℝ ∞ b Ω :=
    (hψ₂.contDiffOn_interior hΩ).sub ((hψ₁.contDiffOn_interior hΩ).comp hFs hFi)
  have hds : ContDiffOn ℝ ∞ d Ω :=
    (hψ₁.contDiffOn_interior hΩ).sub ((hψ₂.contDiffOn_interior hΩ).comp hHs hHi)
  have hFconf : EuclideanConformalOn Ω F b :=
    closureSelfMap_conformal_of_pullback D hΩ Φ hψ₁ hψ₂ hΦmetric
  have hHconf : EuclideanConformalOn Ω H d :=
    closureSelfMap_conformal_of_pullback D hΩ Φ.symm hψ₂ hψ₁ (pullbackMetric_inverse Φ hΦmetric)
  obtain ⟨hFext, hbext⟩ := smoothThrough_of_conformal_on_connected_domain hn hΩ hconn hFs hbs hFc hbc hFconf
  obtain ⟨hHext, _⟩ := smoothThrough_of_conformal_on_connected_domain hn hΩ hconn hHs hds hHc hdc hHconf
  have hFclosure : IsClosureDiffeomorphism Ω F := by
    refine ⟨closureSelfMap_mapsTo Φ, hFi, hFext,
      H, closureSelfMap_mapsTo Φ.symm, hHi, hHext, ?_, ?_⟩
    · intro x hx
      let p : ↥(closure Ω) := ⟨x, hx⟩
      change closureSelfMap Φ.symm (closureSelfMap Φ (p : EuclideanSpace ℝ (Fin n))) = (p : EuclideanSpace ℝ (Fin n))
      rw [closureSelfMap_on_closure, closureSelfMap_on_closure, Φ.symm_apply_apply]
    · intro x hx
      let p : ↥(closure Ω) := ⟨x, hx⟩
      change closureSelfMap Φ (closureSelfMap Φ.symm (p : EuclideanSpace ℝ (Fin n))) = (p : EuclideanSpace ℝ (Fin n))
      rw [closureSelfMap_on_closure, closureSelfMap_on_closure, Φ.apply_symm_apply]
  let P := (D.frontierCoordinate hΩ) ⁻¹' Γ₀
  have hP : IsOpen P := h₀open.preimage (D.continuous_frontierCoordinate hΩ)
  have hPne : P.Nonempty := by
    obtain ⟨p, hp⟩ := h₀ne
    exact ⟨D.boundaryCoordinate hΩ p, by
      change D.frontierCoordinate hΩ (D.boundaryCoordinate hΩ p) ∈ Γ₀
      rw [D.frontierCoordinate_boundaryCoordinate]
      exact hp⟩
  have hpfix (q : ↥(frontier Ω)) (hq : q ∈ P) : F q = (q : EuclideanSpace ℝ (Fin n)) := by
    let p := D.frontierCoordinate hΩ q
    change p ∈ Γ₀ at hq
    change closureSelfMap Φ (p.val : EuclideanSpace ℝ (Fin n)) = (p.val : EuclideanSpace ℝ (Fin n))
    rw [closureSelfMap_on_closure, hΦfix p hq]
  obtain ⟨hFid, hbid⟩ := lemma81 hn hΩ hconn D.regular_boundary hFclosure hbext hFconf hP hPne hpfix
  intro x hx
  have hb : ψ₂ x - ψ₁ x = 0 := by
    have h := hbid hx
    change ψ₂ x - ψ₁ (F x) = 0 at h
    rw [show F x = x from hFid hx] at h
    exact h
  calc
    γ₁ x = Real.exp (((n : ℝ) - 2) * ψ₁ x) := (hExp γ₁ (hpos₁ x hx)).symm
    _ = Real.exp (((n : ℝ) - 2) * ψ₂ x) := by rw [sub_eq_zero.mp hb]
    _ = γ₂ x := hExp γ₂ (hpos₂ x hx)

end CalderonPaper
