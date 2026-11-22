module

public import Proof.CalderonPatch.HalfSpaceLocalizedForcing
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Regularity.SmoothCutoff

import Proof.CalderonN.EllipticCalculus
import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal ContDiff Distributions Gradient Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN TauCeti TauCeti.PDE OAI.AnisotropicCalderon.Regularity

variable {n : ℕ}
local notation "E" => X n
local notation "μ" => (volume : Measure E)

set_option maxHeartbeats 2500000 in
/-- Successive cutoff reads of the same local weak equation on a
common larger open set. The zero-trace condition is supplied for
cutoffs supported in one fixed signed chart region. -/
theorem exists_localized_sobolev_order
    {Ω H : Opens E} {W : Set E} (hW : IsOpen W)
    (hΩH : Ω ≤ H) (hΩb : Bornology.IsBounded (Ω : Set E))
    (hWH : W ∩ H ⊆ (Ω : Set E))
    {a : E → Mat n} (ha : ContDiff ℝ ∞ a)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ ((μ).restrict H))
    (hHigher : ∀ k (F : Wkp μ H 2 k) (u : W1p0 μ H 2),
      IsWeakSolutionDirichlet a 0 0 (Wkp.value k F) u →
      ∃ U : Wkp μ H 2 (k + 2), Wkp.firstOrder (k + 1) U = (u : W1p μ H 2))
    {f : Lp ℝ 2 ((μ).restrict Ω)} {q : E → ℝ} (hq : ContDiff ℝ ∞ q)
    (hf : (f : E → ℝ) =ᵐ[(μ).restrict Ω] q)
    (u : W1p μ Ω 2)
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ μ Ω 2 φ) =
      ∫ x in Ω, f x * φ x)
    (hZero : ∀ (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ), HasCompactSupport ψ →
      tsupport ψ ⊆ W → ∀ (B : ℝ) (hB : 0 ≤ B)
      (hBv : ∀ x ∈ Ω, |ψ x| ≤ B) (hBg : ∀ x ∈ Ω, ‖∇ ψ x‖ ≤ B),
      W1p.contDiffSMul ψ hψ hB hBv hBg u ∈ w1p0Submodule μ Ω 2)
    (k : ℕ) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ W) :
    ∃ U : Wkp μ H 2 (k + 1),
      Wkp.firstOrder k U ∈ w1p0Submodule μ H 2 ∧
      (∀ᵐ x ∂(μ).restrict H, W1p.value (Wkp.firstOrder k U) x =
        (Ω : Set E).indicator (fun y => ψ y * W1p.value u y) x) ∧
      ∀ᵐ x ∂(μ).restrict H, W1p.gradient (Wkp.firstOrder k U) x =
        (Ω : Set E).indicator (fun y =>
          ψ y • W1p.gradient u y + W1p.value u y • ∇ ψ y) x := by
  have hlocal (ζ : E → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
      (hζs : tsupport ζ ⊆ W) :
      ∃ w : W1p0 μ H 2, ∃ g : Lp ℝ 2 ((μ).restrict H),
        IsWeakSolutionDirichlet a 0 0 g w ∧
        (∀ᵐ x ∂(μ).restrict H, g x = (Ω : Set E).indicator (locForcing a ζ f u) x) ∧
        (∀ᵐ x ∂(μ).restrict H, W1p.value (w : W1p μ H 2) x =
          (Ω : Set E).indicator (fun y => ζ y * W1p.value u y) x) ∧
        ∀ᵐ x ∂(μ).restrict H, W1p.gradient (w : W1p μ H 2) x =
          (Ω : Set E).indicator (fun y =>
            ζ y • W1p.gradient u y + W1p.value u y • ∇ ζ y) x := by
    let S := tsupport ζ
    have hζg : Continuous (∇ ζ) := (hζ.gradient_right (m := ∞) (by simp)).continuous
    obtain ⟨Bv,hBv⟩ := hζc.exists_bound_of_continuousOn hζ.continuous.continuousOn
    obtain ⟨Bg,hBg⟩ := hζc.exists_bound_of_continuousOn hζg.continuousOn
    let B := max 0 (max Bv Bg)
    have hB : 0 ≤ B := le_max_left _ _
    have hB₁ : Bv ≤ B := (le_max_left _ _).trans (le_max_right _ _)
    have hB₂ : Bg ≤ B := (le_max_right _ _).trans (le_max_right _ _)
    have hBV (x : E) (_ : x ∈ Ω) : |ζ x| ≤ B := by
      by_cases hx : x ∈ S
      · exact (hBv x hx).trans hB₁
      · rw [image_eq_zero_of_notMem_tsupport hx,abs_zero]
        exact hB
    have hBG (x : E) (_ : x ∈ Ω) : ‖∇ ζ x‖ ≤ B := by
      by_cases hx : x ∈ S
      · exact (hBg x hx).trans hB₂
      · rw [gradient_of_notMem_tsupport hx,norm_zero]
        exact hB
    exact exists_isWeakSolutionDirichlet_smoothCutoff ha hcoeff hΩH hΩb hu hζ
      (fun x hx => hWH ⟨hζs hx.1,hx.2⟩) hB hBV hBG
      (hZero ζ hζ hζc hζs B hB hBV hBG)
  induction k generalizing ψ with
  | zero =>
    obtain ⟨w,g,_,_,hv,hg⟩ := hlocal ψ hψ hψc hψs
    let v : Wkp μ H 2 1 := (w : W1p μ H 2)
    have hFirst : Wkp.firstOrder 0 v = (w : W1p μ H 2) := Wkp.firstOrder_zero v
    refine ⟨v, ?_⟩
    rw [hFirst]
    exact ⟨w.property,hv,hg⟩
  | succ k ih =>
    obtain ⟨w,g,hw,hg,hwv,hwg⟩ := hlocal ψ hψ hψc hψs
    obtain ⟨η,hη,hηc,hηs,hη1⟩ := Elliptic.exists_plateau_cutoff hW hψc hψs
    obtain ⟨T,_,hTv,hTg⟩ := ih hη hηc hηs
    obtain ⟨G,hG⟩ := exists_sobolev_localized_forcing_on ha hq f hf u hψ hψc
      (fun x hx => hWH ⟨hψs hx.1,hx.2⟩) hη1 k T hTv hTg
    have hfg : Wkp.value k G = g := Lp.ext (hG.trans (EventuallyEq.symm hg))
    have hw' : IsWeakSolutionDirichlet a 0 0 (Wkp.value k G) w := by rwa [hfg]
    obtain ⟨U,hU⟩ := hHigher k G w hw'
    exact ⟨U,by rw [hU]; exact w.property,by rwa [hU],by rwa [hU]⟩

end CalderonPatch
