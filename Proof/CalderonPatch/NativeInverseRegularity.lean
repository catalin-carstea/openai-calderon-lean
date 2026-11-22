module

public import Proof.CalderonPatch.DirichletWeakGreen
public import Proof.CalderonPatch.GreenInverseJetContinuity

public section

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Manifold Matrix.Norms.Elementwise

namespace CalderonPatch

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)

/-- Analytic properties of the actual canonical weak inverse used by
the Green construction. Both regularity statements describe smooth
representatives of the exact almost-everywhere class of the inverse. -/
structure NativeInverseRegularity (D : DirichletData m M) : Prop where
  smooth_solution :
    ∀ (f : Lp ℝ 2 D.volume) (q : M → ℝ), ContMDiff J R ∞ q →
      (f : M → ℝ) =ᵐ[D.volume] q →
      ∃ u : M → ℝ, ContMDiff J R ∞ u ∧ EqOn u 0 ((J).boundary M) ∧
        EqOn (-nativeLaplace D.metric u) q ((J).interior M) ∧
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume] u
  local_zero_forcing :
    ∀ (U : Set M), IsOpen U → ∀ f : Lp ℝ 2 D.volume,
      (f : M → ℝ) =ᵐ[D.volume.restrict U] 0 →
      ∃ u : M → ℝ, ContMDiffOn J R ∞ u U ∧ EqOn u 0 (U ∩ (J).boundary M) ∧
        EqOn (nativeLaplace D.metric u) 0 (U ∩ (J).interior M) ∧
        (D.l2Value (D.weakDirichletInverse f) : M → ℝ) =ᵐ[D.volume.restrict U] u

end CalderonPatch
