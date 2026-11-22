module

public import Proof.CalderonPatch.DirichletWeakGreen

import Proof.CalderonPatch.GaugeFromCauchy
import Proof.CalderonPatch.SmoothNativeLaplace
import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- Smooth solvability of the homogeneous boundary problem with
smooth forcing gives a smooth harmonic solution for every smooth trace. -/
theorem exists_dirichletHarmonic_from_smoothForcing (D : DirichletData m M)
    (hSolve : ∀ (f : Lp ℝ 2 D.volume) (q : M → ℝ), ContMDiff J R ∞ q →
      (f : M → ℝ) =ᵐ[D.volume] q →
      ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ EqOn u 0 ((J).boundary M) ∧
        EqOn (-nativeLaplace D.metric u) q ((J).interior M))
    {f : M → ℝ} (hf : ContMDiff J R ∞ f) :
    ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ EqOn u f ((J).boundary M) ∧
      EqOn (nativeLaplace D.metric u) 0 ((J).interior M) := by
  obtain ⟨Q,hQ,hEq⟩ := exists_smooth_nativeLaplace D.metric hf
  have hAE : (D.positiveLaplaceLp f hf : M → ℝ) =ᵐ[D.volume] -Q := by
    have hI : ∀ᵐ x ∂D.volume, x ∈ (J).interior M := by
      rw [ae_iff]
      change D.volume (((J).interior M)ᶜ) = 0
      rw [(J).compl_interior]
      exact metricVolume_boundary_eq_zero D.metric D.volume D.metric_volume
    filter_upwards [D.positiveLaplaceLp_ae_eq f hf,hI] with x hx hxi
    exact hx.trans (congrArg Neg.neg (hEq hxi)).symm
  obtain ⟨v,hv,hv0,hvQ⟩ := hSolve (D.positiveLaplaceLp f hf) (-Q) hQ.neg hAE
  refine ⟨f-v,hf.sub hv,?_,?_⟩
  · intro x hx
    change f x - v x = f x
    rw [hv0 hx,Pi.zero_apply,sub_zero]
  · intro x hx
    have he : nativeLaplace D.metric v x = nativeLaplace D.metric f x := by
      have h := hvQ hx
      change -nativeLaplace D.metric v x = -Q x at h
      exact (neg_injective h).trans (hEq hx)
    change nativeLaplace D.metric (fun y => f y - v y) x = 0
    rw [nativeLaplace_sub D.metric hf hv hx,he,sub_self]

end CalderonPatch
