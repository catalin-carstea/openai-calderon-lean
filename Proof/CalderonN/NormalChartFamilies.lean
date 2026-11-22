module

public import Proof.CalderonN.NormalTraceVelocity

import Proof.CalderonN.ClassicalBallDirichlet
import Proof.CalderonN.ScaledGreenDatumJets
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

/-! Adapted from `NormalChartFamilies` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Metric
open scoped ContDiff Topology Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem contDiff_normalBallChartMap_family
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {e : ℝ → (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => e p.1 p.2 i)) :
    ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (ℝ × (X dim))) =>
      normalBallChartMap (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2) := by
  let B (q : ℝ × ((X dim) × (ℝ × (X dim)))) := (q.1,q.2.1)
  have hB : ContDiff ℝ ∞ B := contDiff_fst.prodMk contDiff_snd.fst
  have hW : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (ℝ × (X dim))) =>
      frameVector (e q.1) q.2.1 q.2.2.2) :=
    contDiff_family_frameVector (fun i => (he i).comp hB) contDiff_snd.snd.snd
  exact hE.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.fst.smul hW)))

theorem contDiff_family_christoffel
    {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hPos : ∀ a y, (γ a y).PosDef) (k i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => christoffel (γ q.1) q.2 k i j) := by
  have hd (a b c : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) =>
      coordDeriv a (fun y => γ q.1 y b c) q.2) := by
    have he (q : ℝ × (X dim)) := section_coordDeriv_eq_product_fderiv (hγ b c) q.1 q.2 a
    simp_rw [he]
    exact ((hγ b c).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hInv (a b : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => (γ q.1 q.2)⁻¹ a b) :=
    contDiffOn_univ.mp (contDiffOn_inv_entry_of_entries (g := fun q : ℝ × (X dim) => γ q.1 q.2)
      (fun i j => (hγ i j).contDiffOn) (fun q _ => (hPos q.1 q.2).det_pos.ne') a b)
  unfold christoffel
  exact (ContDiff.sum fun l _ => (hInv k l).mul (((hd i l j).add (hd j i l)).sub (hd l i j))).div_const 2

theorem contDiff_family_frameCoordinates
    {γ : ℝ → (MetricField dim)} (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    {e : ℝ → (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i)) :
    ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => frameCoordinates (γ q.1) q.2.1 (e q.1 q.2.1) q.2.2) := by
  let B (q : ℝ × ((X dim) × (X dim))) := (q.1,q.2.1)
  have hB : ContDiff ℝ ∞ B := contDiff_fst.prodMk contDiff_snd.fst
  apply (contDiff_piLp 2).mpr
  intro k
  change ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => metricPair (γ q.1) q.2.1 q.2.2 (e q.1 q.2.1 k))
  unfold metricPair
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (((hγ i j).comp hB).mul ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd.snd)).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp ((he k).comp hB))

abbrev NormalVelocityParameter (dim : ℕ) := ℝ × ((X dim) × (ℝ × (ℝ × (X dim))))

set_option maxHeartbeats 1800000 in
/-- Smoothness of the scaled velocity on the domain where the normalized
vertical chart derivative is invertible. The radius need not be positive. -/
theorem contDiffOn_scaledNormalTraceVelocity_family
    {γ : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hPos : ∀ a y, (γ a y).PosDef)
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {e : ℝ → (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => e p.1 p.2 i))
    (a : (X dim)) {U : Set (NormalVelocityParameter dim)}
    (hDet : ∀ q ∈ U, (coordinateMatrix (normalizedBallDerivative (E q.1) (e q.1)
      q.2.1 q.2.2.1 q.2.2.2.2)).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun q : (NormalVelocityParameter dim) => scaledNormalTraceVelocity (γ q.1) (E q.1)
      (e q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 a) U := by
  let T := (NormalVelocityParameter dim)
  let B (q : T) := (q.1,q.2.1)
  let R (q : T) := (q.1,(q.2.1,(q.2.2.1,q.2.2.2.2)))
  let W (q : T) := frameVector (e q.1) q.2.1 q.2.2.2.2
  let D (q : T) := coordinateMatrix (normalizedBallDerivative (E q.1) (e q.1)
    q.2.1 q.2.2.1 q.2.2.2.2)
  let H (q : T) := connection (γ q.1) q.2.1 a (W q)
  let Z (q : T) := (q.1,(q.2.1,q.2.2.1 • W q))
  let V (q : T) := fderiv ℝ (E q.1) (Z q).2
    (a,q.2.2.2.1 • W q - q.2.2.1 • H q)
  have hB : ContDiff ℝ ∞ B := contDiff_fst.prodMk contDiff_snd.fst
  have hR : ContDiff ℝ ∞ R := contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk (contDiff_snd.snd.fst.prodMk contDiff_snd.snd.snd.snd))
  have hW : ContDiff ℝ ∞ W :=
    contDiff_family_frameVector (fun i => (he i).comp hB) contDiff_snd.snd.snd.snd
  have hD (i j : (I dim)) : ContDiff ℝ ∞ (fun q : T => D q i j) :=
    (contDiff_normalizedBallDerivative_family_entry hE he i j).comp hR
  have hInv (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q : T => (D q)⁻¹ i j) U :=
    contDiffOn_inv_entry_of_entries (fun i j => (hD i j).contDiffOn) hDet i j
  have hH : ContDiff ℝ ∞ H := by
    apply (contDiff_piLp 2).mpr
    intro k
    change ContDiff ℝ ∞ (fun q : T => ∑ i : (I dim), ∑ j : (I dim),
      christoffel (γ q.1) q.2.1 k i j * a i * W q j)
    exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (((contDiff_family_christoffel hγ hPos k i j).comp hB).mul contDiff_const).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hW)
  have hZ : ContDiff ℝ ∞ Z := contDiff_fst.prodMk
    (contDiff_snd.fst.prodMk (contDiff_snd.snd.fst.smul hW))
  have hV : ContDiff ℝ ∞ V := by
    have hEq (q : T) : V q = fderiv ℝ (fun p : ℝ × ((X dim) × (X dim)) => E p.1 p.2) (Z q)
        (0,(a,q.2.2.2.1 • W q-q.2.2.1 • H q)) := by
      have hSlice : HasFDerivAt (Prod.mk q.1) (ContinuousLinearMap.inr ℝ ℝ ((X dim) × (X dim))) (Z q).2 :=
        hasFDerivAt_prodMk_right q.1 (Z q).2
      have hDer := ((hE.differentiable (by simp) (Z q)).hasFDerivAt.comp (Z q).2 hSlice).fderiv
      change fderiv ℝ ((fun p : ℝ × ((X dim) × (X dim)) => E p.1 p.2) ∘ Prod.mk q.1) (Z q).2
        (a,q.2.2.2.1 • W q - q.2.2.1 • H q) = _
      rw [hDer]
      simp
    change ContDiff ℝ ∞ (fun q : T => V q)
    simp_rw [hEq]
    exact ((hE.fderiv_right (m := ∞) (by simp)).comp hZ).clm_apply
      (contDiff_const.prodMk (contDiff_const.prodMk
        ((contDiff_snd.snd.snd.fst.smul hW).sub (contDiff_snd.snd.fst.smul hH))))
  apply (contDiffOn_piLp 2).mpr
  intro i
  change ContDiffOn ℝ ∞ (fun q : T => ∑ j : (I dim), (D q)⁻¹ i j * V q j) U
  exact ContDiffOn.sum fun j _ => (hInv i j).mul
    (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hV).contDiffOn)

theorem normalizedBallDerivative_det_ne_zero
    {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E) (e : (Frame dim)) (y : (X dim)) {r : ℝ}
    {z : (X dim)} (hBij : Function.Bijective (fderiv ℝ (normalBallChartMap E e y r) z)) :
    (coordinateMatrix (normalizedBallDerivative E e y r z)).det ≠ 0 := by
  have h := coordinateJacobian_det_ne_zero hBij
  have hMat : coordinateJacobian (normalBallChartMap E e y r) z =
      r • coordinateMatrix (normalizedBallDerivative E e y r z) := by
    unfold coordinateJacobian
    rw [fderiv_normalBallChartMap_eq_radius_smul hE]
    ext i j
    rfl
  rw [hMat,Matrix.det_smul] at h
  exact (mul_ne_zero_iff.mp h).2

end CalderonN
