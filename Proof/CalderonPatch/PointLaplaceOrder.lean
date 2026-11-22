module

public import Proof.CalderonPatch.CompactSecondJet
public import Proof.CalderonPatch.PointEllipticOrder
public import Proof.CalderonPatch.NativeLaplace

import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.LocalMixedParameterJetCalculus

@[expose] public section

noncomputable section
open Filter Matrix Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch

open CalderonN (I X Mat MetricField christoffel laplace chartDerivativeWord coordDeriv)

variable {n : ℕ} [NeZero n] {U : Set (X n)} {K : Compacts (X n)} {γ : MetricField n}

/-- The chart Laplacian preserves the space of tests supported in a
compact subset of the smooth chart. -/
def compactLaplace (hU : IsOpen U) (hK : (K : Set (X n)) ⊆ U) (hγ : CalderonN.SmoothMetric U γ)
    (f : 𝓓_{K}(X n, ℝ)) : 𝓓_{K}(X n, ℝ) := by
  have hs : tsupport (laplace γ f) ⊆ (K : Set (X n)) :=
    (CalderonN.tsupport_laplace_subset γ f).trans f.tsupport_subset
  have hzero : EqOn (laplace γ f) 0 (K : Set (X n))ᶜ :=
    fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  refine ⟨laplace γ f, contDiff_iff_contDiffAt.mpr (fun x => ?_), hzero⟩
  by_cases hx : x ∈ U
  · exact (contDiffOn_coordinateLaplace hU hγ f.contDiff.contDiffOn).contDiffAt (hU.mem_nhds hx)
  · have h := Filter.mem_of_superset (K.isCompact.isClosed.isOpen_compl.mem_nhds
      (show x ∉ (K : Set (X n)) from fun hk => hx (hK hk))) hzero
    exact contDiffAt_const.congr_of_eventuallyEq h

/-- The coefficient of each first derivative in the ordinary coordinate Laplacian. -/
def laplaceFirstCoeff (γ : MetricField n) (x : X n) (k : I n) : ℝ :=
  -(∑ i : I n, ∑ j : I n, (γ x)⁻¹ i j * christoffel γ x k i j)

omit [NeZero n] in
theorem coordinateElliptic_eq_laplace (γ : MetricField n) (f : X n → ℝ) :
    coordinateElliptic (fun x => (γ x)⁻¹) (laplaceFirstCoeff γ) f = laplace γ f := by
  funext x
  simp only [coordinateElliptic, Pi.add_apply, Finset.sum_apply, Pi.mul_apply, chartDerivativeWord,
    List.foldr_cons, List.foldr_nil, laplaceFirstCoeff, laplace, mul_sub, Finset.sum_sub_distrib,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

private theorem exists_smooth_coordinateElliptic_germ (hU : IsOpen U) (h0 : (0 : X n) ∈ U)
    (hγ : CalderonN.SmoothMetric U γ) :
    ∃ (A : X n → Mat n) (b : X n → I n → ℝ),
      (∀ i j, ContDiff ℝ ∞ (fun x => A x i j)) ∧ (∀ i, ContDiff ℝ ∞ (fun x => b x i)) ∧
      (A 0).PosDef ∧ ∀ f : X n → ℝ, laplace γ f =ᶠ[𝓝 0] coordinateElliptic A b f := by
  have hb (k : I n) : ContDiffOn ℝ ∞ (fun x => laplaceFirstCoeff γ x k) U := by
    exact (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (CalderonN.contDiffOn_metric_inv_entry hγ i j).mul
        (CalderonN.contDiffOn_christoffel hU hγ k i j)))).neg
  choose A hA hAEq using fun i j => CalderonN.exists_global_smooth_germ_of_open
    (fun x => (γ x)⁻¹ i j) hU (CalderonN.contDiffOn_metric_inv_entry hγ i j) h0
  choose b hbDiff hbEq using fun k => CalderonN.exists_global_smooth_germ_of_open
    (fun x => laplaceFirstCoeff γ x k) hU (hb k) h0
  refine ⟨fun x i j => A i j x, fun x k => b k x, hA, hbDiff, ?_, fun f => ?_⟩
  · have h : (fun i j => A i j (0 : X n)) = (γ 0)⁻¹ := Matrix.ext fun i j => (hAEq i j).eq_of_nhds
    change Matrix.PosDef (fun i j => A i j (0 : X n))
    rw [h]
    exact (hγ.2 0 h0).inv
  · have hA' : ∀ᶠ x in 𝓝 (0 : X n), ∀ i j, A i j x = (γ x)⁻¹ i j :=
      Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (hAEq i))
    have hb' : ∀ᶠ x in 𝓝 (0 : X n), ∀ i, b i x = laplaceFirstCoeff γ x i :=
      Filter.eventually_all.2 hbEq
    rw [← coordinateElliptic_eq_laplace]
    filter_upwards [hA', hb'] with x hx hy
    simp only [coordinateElliptic, Pi.add_apply, Finset.sum_apply, Pi.mul_apply, hx, hy]

/-- The order calculation identifies a point-supported inverse of a
second-jet functional as a multiple of delta, and hence identifies the
original functional as a multiple of the chart Laplacian on jets. -/
theorem annihilator_eq_laplace_of_pointSupported_inverse (hU : IsOpen U)
    (hK : (K : Set (X n)) ⊆ U) (hK0 : (K : Set (X n)) ∈ 𝓝 0) (hγ : CalderonN.SmoothMetric U γ)
    (D : ScalarSecondJet n →ₗ[ℝ] ℝ) (W : 𝓓_{K}(X n, ℝ) →L[ℝ] ℝ)
    (hW : ∀ f : 𝓓_{K}(X n, ℝ), (f : X n → ℝ) =ᶠ[𝓝 0] 0 → W f = 0)
    (hInverse : ∀ f, W (compactLaplace hU hK hγ f) = D (compactSecondJet f)) :
    ∃ c : ℝ, D = c • laplaceOnSecondJet γ 0 := by
  have h0 := hK (mem_of_mem_nhds hK0)
  obtain ⟨A, b, hA, hb, hPos, hOp⟩ := exists_smooth_coordinateElliptic_germ hU h0 hγ
  obtain ⟨c, hc⟩ := compactTest_point_support_elliptic_order hK0 W hW (compactLaplace hU hK hγ)
    hA hb hPos (fun f => hOp f) (fun f hf => by
      rw [hInverse, compactSecondJet_eq_zero_of_flat f hf, map_zero])
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro v
  obtain ⟨f, rfl⟩ := surjective_compactSecondJet hK0 v
  rw [← hInverse, hc]
  change c * laplace γ f 0 = c * laplaceOnSecondJet γ 0 (compactSecondJet f)
  rw [compactSecondJet, smoothSecondJet_laplace]

/-- The second jets of the linear cap-source family fill the harmonic
hyperplane once each transposed annihilator has point support. -/
theorem range_sourceSecondJet_of_pointSupported_inverses {F : Type*} [AddCommGroup F] [Module ℝ F]
    (hU : IsOpen U) (hK : (K : Set (X n)) ⊆ U) (hK0 : (K : Set (X n)) ∈ 𝓝 0)
    (hγ : CalderonN.SmoothMetric U γ) (J : F →ₗ[ℝ] ScalarSecondJet n)
    (hH : ∀ f, laplaceOnSecondJet γ 0 (J f) = 0)
    (hDual : ∀ D : ScalarSecondJet n →ₗ[ℝ] ℝ, (∀ f, D (J f) = 0) →
      ∃ W : 𝓓_{K}(X n, ℝ) →L[ℝ] ℝ,
        (∀ f : 𝓓_{K}(X n, ℝ), (f : X n → ℝ) =ᶠ[𝓝 0] 0 → W f = 0) ∧
        ∀ f, W (compactLaplace hU hK hγ f) = D (compactSecondJet f)) :
    J.range = (laplaceOnSecondJet γ 0).ker := by
  apply range_eq_ker_of_annihilating_functionals _ J hH
  intro D hD
  obtain ⟨W, hW, hInverse⟩ := hDual D hD
  exact annihilator_eq_laplace_of_pointSupported_inverse hU hK hK0 hγ D W hW hInverse

end CalderonPatch
