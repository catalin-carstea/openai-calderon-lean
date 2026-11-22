module

public import Proof.CalderonPatch.ChartSobolev
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Multiplication

import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.VanishingBoundary

public section

noncomputable section
open Filter MeasureTheory Set TopologicalSpace TauCeti
open scoped ContDiff ENNReal Gradient Manifold Topology

namespace CalderonPatch

open CalderonN (X)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "N" => (m + 1)

/-- A cutoff supported inside the signed chart preserves the zero
Dirichlet condition on the flat face for every element of the native
energy completion. It introduces zero data on the artificial boundary. -/
theorem chartSobolev_cutoff_mem_w1p0 (D : DirichletData m M)
    {U : Opens (X N)} {W : Set (X N)} (hU : (U : Set (X N)) = W ∩ positiveHalfSpace N)
    (hB : Bornology.IsBounded (U : Set (X N)))
    (F : DirichletHilbert D →L[ℝ] W1p (volume : Measure (X N)) U 2)
    (hF : ∀ u : DirichletTest D, ∃ v : X N → ℝ,
      Continuous v ∧ (∀ z ∈ closure (U : Set (X N)), z 0 = 0 → v z = 0) ∧
      (W1p.value (F (u : DirichletHilbert D)) : X N → ℝ) =ᵐ[volume.restrict U] v)
    {χ : X N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ W) {B : ℝ}
    (hB₀ : 0 ≤ B) (hBχ : ∀ z ∈ U, |χ z| ≤ B) (hBg : ∀ z ∈ U, ‖gradient χ z‖ ≤ B)
    (u : DirichletHilbert D) :
    W1p.contDiffSMul χ hχ hB₀ hBχ hBg (F u) ∈ w1p0Submodule volume U 2 := by
  let L := (W1p.contDiffSMulL χ hχ hB₀ hBχ hBg).comp F
  have hClosed : IsClosed {u : DirichletHilbert D | L u ∈ w1p0Submodule volume U 2} :=
    (w1p0Submodule volume U 2).isClosed.preimage L.continuous
  change L u ∈ w1p0Submodule volume U 2
  change u ∈ {w : DirichletHilbert D | L w ∈ w1p0Submodule volume U 2}
  refine UniformSpace.Completion.induction_on u hClosed ?_
  intro w
  obtain ⟨v,hv,hv0,hValue⟩ := hF w
  let f : X N → ℝ := fun z => χ z * v z
  have hf0 (z : X N) (hz : z ∈ frontier (U : Set (X N))) : f z = 0 := by
    have hzH : z ∈ inwardHalfSpace N := by
      have hClosedH : IsClosed (inwardHalfSpace N) :=
        isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
      have hUH : (U : Set (X N)) ⊆ inwardHalfSpace N := by
        rw [hU]
        exact inter_subset_right.trans positiveHalfSpace_subset_inwardHalfSpace
      exact closure_minimal hUH hClosedH hz.1
    by_cases hheight : z 0 = 0
    · exact mul_eq_zero_of_right _ (hv0 z hz.1 hheight)
    · have hzP : z ∈ positiveHalfSpace N :=
        mem_positiveHalfSpace.mpr (lt_of_le_of_ne (mem_inwardHalfSpace.mp hzH) (Ne.symm hheight))
      have hzW : z ∉ W := by
        intro h
        apply hz.2
        rw [U.isOpen.interior_eq,hU]
        exact ⟨h,hzP⟩
      exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport fun h => hzW (hχs h)) _
  have hval : (W1p.value (L (w : DirichletHilbert D)) : X N → ℝ) =ᵐ[volume.restrict U] f := by
    dsimp only [L,ContinuousLinearMap.comp_apply]
    rw [W1p.contDiffSMulL_apply]
    filter_upwards [W1p.value_contDiffSMul_ae hχ hB₀ hBχ hBg (F (w : DirichletHilbert D)),
      hValue] with z h₁ h₂
    simp only [f,h₁,h₂,smul_eq_mul]
  exact W1p.mem_w1p0Submodule_of_continuousOn_closure ENNReal.ofNat_ne_top hB
    (hχ.continuous.mul hv).continuousOn hf0 hval

end CalderonPatch
