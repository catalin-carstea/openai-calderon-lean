module

public import Proof.CalderonPatch.Energy
import Proof.Manuscript.AnisotropicUniqueness
import Proof.Manuscript.BoundaryPatchDensity
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Filter Set MeasureTheory
open scoped ContDiff Manifold Topology

namespace CalderonPaper

open CalderonN (X axis)
open CalderonPatch

theorem corollary12 {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hBoundary : ((𝓡∂ n).boundary M).Nonempty)
    {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (hμ₁ : IsMetricVolume g₁ μ₁) (hμ₂ : IsMetricVolume g₂ μ₂)
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ univ) :
    ∃ F : M ≃ₘ⟮𝓡∂ n, 𝓡∂ n⟯ M, FixesPatch (n := n) univ F ∧ PullbackMetric g₂ g₁ F := by
  let J := 𝓡∂ n
  obtain ⟨p, hp⟩ := hBoundary
  let q : ↥(J.boundary M) := ⟨p, hp⟩
  let Γ : Set ↥(J.boundary M) := {q}ᶜ
  have hDense : Dense Γ := boundary_compl_singleton_dense (n := n) (by omega) q
  have hProper : Γ ≠ univ := fun h => by
    have : q ∈ Γ := h ▸ mem_univ q
    exact this rfl
  have hΓ : IsOpen Γ := isClosed_singleton.isOpen_compl
  let : Nonempty ↥(J.boundary M) := ⟨q⟩
  have hΓne : Γ.Nonempty := hDense.nonempty
  have hPatch : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ :=
    fun f hf _ => hEnergy f hf (subset_univ _)
  obtain ⟨Φ, hfix, hPull⟩ :=
    smoothAnisotropicUniqueness hn hΓ hΓne hProper hμ₁ hμ₂ hPatch
  have hEq : ∀ z : ↥(J.boundary M), Φ z = (z : M) := by
    let s : Set ↥(J.boundary M) := {z | Φ z = (z : M)}
    have hs : IsClosed s :=
      isClosed_eq (Φ.continuous.comp continuous_subtype_val) continuous_subtype_val
    intro z
    exact closure_minimal (fun y hy => hfix y hy) hs (hDense z)
  refine ⟨Φ.symm, ?_, ?_⟩
  · intro z _
    exact Φ.injective ((Φ.apply_symm_apply z).trans (hEq z).symm)
  · intro x v w
    have hComp : (fun y : M => Φ (Φ.symm y)) = id := funext Φ.apply_symm_apply
    have hD : (mfderiv J J Φ (Φ.symm x)).comp (mfderiv J J Φ.symm x) =
        ContinuousLinearMap.id ℝ (X n) := by
      rw [← mfderiv_comp x (Φ.contMDiff.mdifferentiable (by simp) _) (Φ.symm.contMDiff.mdifferentiable (by simp) _)]
      change mfderiv J J (fun y : M => Φ (Φ.symm y)) x = _
      rw [hComp, mfderiv_id]
      rfl
    have h := hPull (Φ.symm x) (mfderiv J J Φ.symm x v) (mfderiv J J Φ.symm x w)
    change g₂.inner (Φ.symm x) (mfderiv J J Φ.symm x v) (mfderiv J J Φ.symm x w) =
      g₁.inner (Φ (Φ.symm x))
        (((mfderiv J J Φ (Φ.symm x)).comp (mfderiv J J Φ.symm x)) v)
        (((mfderiv J J Φ (Φ.symm x)).comp (mfderiv J J Φ.symm x)) w) at h
    rw [hD, Φ.apply_symm_apply] at h
    exact h.symm

end CalderonPaper
