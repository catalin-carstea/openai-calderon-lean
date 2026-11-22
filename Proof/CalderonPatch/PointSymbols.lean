module

public import Proof.CalderonPatch.PointSupport
public import Proof.CalderonPatch.PointDistributionSymbol

import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LSum
import Proof.CalderonN.ChartSchwarzWords

@[expose] public section

noncomputable section
open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

open CalderonN (I X axis axis_sum_chart chartPartial iteratedFDeriv_chart_axes_eq_chartPartial)

variable {n : ℕ} {K : Compacts (X n)}

/-- Apply a polynomial in ordinary partial derivatives to a function at the
origin. The signs from derivatives of delta distributions are absorbed in
the coefficients of the polynomial. -/
def pointSymbolApply (f : X n → ℝ) : MvPolynomial (I n) ℝ →ₗ[ℝ] ℝ :=
  (Finsupp.lsum ℝ fun a : I n →₀ ℕ =>
    (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (chartPartial a f 0)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap

@[simp]
theorem pointSymbolApply_monomial (f : X n → ℝ) (a : I n →₀ ℕ) (c : ℝ) :
    pointSymbolApply f (MvPolynomial.monomial a c) = c * chartPartial a f 0 := by
  change Finsupp.lsum ℝ _ (Finsupp.single a c) = _
  rw [Finsupp.lsum_single]
  rfl

theorem pointSymbolApply_sum_coeff (f : X n → ℝ) (P : MvPolynomial (I n) ℝ) :
    pointSymbolApply f P = ∑ a ∈ P.support, P.coeff a * chartPartial a f 0 := by
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [pointSymbolApply_monomial]

private def chartWordDual {j : ℕ} (idx : Fin j → I n) : X n [×j]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap
    (fun k => EuclideanSpace.proj (idx k))

private theorem chartWordDual_apply {j : ℕ} (idx : Fin j → I n) (v : Fin j → X n) :
    chartWordDual idx v = ∏ k, v k (idx k) := by
  simp [chartWordDual, ContinuousMultilinearMap.compContinuousLinearMap_apply]

private theorem chartMultilinear_expansion [NeZero n] {j : ℕ} (L : X n [×j]→L[ℝ] ℝ) :
    L = ∑ idx : Fin j → I n, L (fun k => axis (idx k)) • chartWordDual idx := by
  ext v
  have hv : v = fun k => ∑ i : I n, v k i • axis i := funext fun k => (axis_sum_chart (v k)).symm
  conv_lhs => rw [hv]
  rw [L.map_sum]
  simp only [ContinuousMultilinearMap.map_smul_univ, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply,
    chartWordDual_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private def chartWordMultidegree {j : ℕ} (idx : Fin j → I n) : I n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (List.ofFn idx).count i

private theorem chartWordMultidegree_coe {j : ℕ} (idx : Fin j → I n) :
    (⇑(chartWordMultidegree idx)) = fun i => (List.ofFn idx).count i := rfl

/-- The coordinate derivatives of delta span the point-supported continuous
linear functionals on tests in a compact neighborhood. -/
theorem exists_pointSymbol_of_point_support [NeZero n] (T : 𝓓_{K}(X n, ℝ) →L[ℝ] ℝ)
    (hK : (K : Set (X n)) ∈ 𝓝 0)
    (hT : ∀ f : 𝓓_{K}(X n, ℝ), (f : X n → ℝ) =ᶠ[𝓝 0] 0 → T f = 0) :
    ∃ P : MvPolynomial (I n) ℝ, ∀ f : 𝓓_{K}(X n, ℝ), T f = pointSymbolApply f P := by
  classical
  obtain ⟨m, A, hA⟩ := exists_compactTest_jet_representation T hK hT
  let w (j : Fin (m + 1)) (idx : Fin (j : ℕ) → I n) :=
    A (Pi.single j (chartWordDual idx))
  let P := ∑ j : Fin (m + 1), ∑ idx : Fin (j : ℕ) → I n,
    MvPolynomial.monomial (chartWordMultidegree idx) (w j idx)
  refine ⟨P, fun f => ?_⟩
  have hexp (j : Fin (m + 1)) :
      (Pi.single j (iteratedFDeriv ℝ (j : ℕ) f 0) : ∀ k : Fin (m + 1), X n [×(k : ℕ)]→L[ℝ] ℝ) =
        ∑ idx : Fin (j : ℕ) → I n,
          chartPartial (chartWordMultidegree idx) f 0 • Pi.single j (chartWordDual idx) := by
    let L := iteratedFDeriv ℝ (j : ℕ) f 0
    have hL : L = ∑ idx : Fin (j : ℕ) → I n,
        chartPartial (chartWordMultidegree idx) f 0 • chartWordDual idx := by
      simpa only [L, iteratedFDeriv_chart_axes_eq_chartPartial f.contDiff,
        chartWordMultidegree_coe] using chartMultilinear_expansion L
    change LinearMap.single ℝ (fun k : Fin (m + 1) => X n [×(k : ℕ)]→L[ℝ] ℝ) j L = _
    rw [hL, map_sum]
    simp only [map_smul, LinearMap.single_apply]
  have hSum : compactTestJet K m f = ∑ j : Fin (m + 1), Pi.single j (iteratedFDeriv ℝ (j : ℕ) f 0) := by
    exact (Finset.univ_sum_single (compactTestJet K m f)).symm
  have h := DFunLike.congr_fun hA f
  change T f = A (compactTestJet K m f) at h
  rw [h, hSum, map_sum]
  simp only [P, hexp, map_sum, map_smul, smul_eq_mul, pointSymbolApply_monomial, w]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

end CalderonPatch
