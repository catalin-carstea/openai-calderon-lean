module

public import Proof.CalderonPatch.NormalJetLine
public import Proof.CalderonPatch.BoundaryNormalLaplacian

import Proof.CalderonN.MetricDivergence
import Mathlib.Tactic

public section
noncomputable section
open Filter Finset Matrix Set
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField axis chartVolume coordDeriv divergenceCoeff)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

/-- Normal derivatives of the inverse metric as one matrix. -/
@[expose] def inverseNormalJet (g : MetricField (n+1)) (k : ℕ) (y : Y) : Mat (n+1) :=
  iteratedDeriv k (fun t : ℝ => (g (signedLayerCoordinates (y,t)))⁻¹) 0

theorem inverseNormalJet_zero (g : MetricField (n+1)) (y : Y) :
    inverseNormalJet g 0 y = (g (normalFacePoint y))⁻¹ := by
  simp only [inverseNormalJet,iteratedDeriv_zero,signedLayerCoordinates_face]

theorem contDiffOn_metric_matrix {O : Set Z} {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) : ContDiffOn ℝ ∞ g O :=
  contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => hg.1 i j

theorem contDiffOn_invert_metric_matrix {O : Set Z} {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) : ContDiffOn ℝ ∞ (fun x => (g x)⁻¹) O :=
  contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => CalderonN.contDiffOn_metric_inv_entry hg i j

theorem inverseNormalJet_entry {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) {y : Y} (hy : normalFacePoint y ∈ O)
    (k : ℕ) (i j : I (n+1)) :
    inverseNormalJet g k y i j = normalJetAt (fun x => (g x)⁻¹ i j) k y := by
  symm
  exact iteratedDeriv_matrix_entry
    (contDiffAt_normalLine hO (contDiffOn_invert_metric_matrix hg) (by
      simpa only [signedLayerCoordinates_face] using hy)) k i j

theorem inverseNormalJet_isSymm {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) {y : Y} (hy : normalFacePoint y ∈ O) (k : ℕ) :
    (inverseNormalJet g k y).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply,inverseNormalJet_entry hO hg hy,inverseNormalJet_entry hO hg hy]
  have hc : Continuous (fun t : ℝ => signedLayerCoordinates (y,t)) :=
    signedLayerCoordinates.continuous.comp (continuous_const.prodMk continuous_id)
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, signedLayerCoordinates (y,t) ∈ O :=
    hc.continuousAt.eventually_mem (hO.mem_nhds (by simpa only [signedLayerCoordinates_face] using hy))
  have hEq : (fun t : ℝ => (g (signedLayerCoordinates (y,t)))⁻¹ j i) =ᶠ[𝓝 0]
      fun t : ℝ => (g (signedLayerCoordinates (y,t)))⁻¹ i j :=
    hNear.mono fun t ht => congrFun (congrFun (hg.2 _ ht).inv.isHermitian.isSymm.eq i) j
  exact hEq.iteratedDeriv_eq k

theorem inverseNormalJet_normal_row {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) (hN : HasNormalMetricBlock 0 g O) {y : Y}
    (hy : normalFacePoint y ∈ O) (k : ℕ) (j : I (n+1)) :
    inverseNormalJet g k y 0 j = iteratedDeriv k (fun _ : ℝ => if (0 : I (n+1)) = j then (1 : ℝ) else 0) 0 := by
  rw [inverseNormalJet_entry hO hg hy]
  have hc : Continuous (fun t : ℝ => signedLayerCoordinates (y,t)) :=
    signedLayerCoordinates.continuous.comp (continuous_const.prodMk continuous_id)
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, signedLayerCoordinates (y,t) ∈ O :=
    hc.continuousAt.eventually_mem (hO.mem_nhds (by simpa only [signedLayerCoordinates_face] using hy))
  have he : (fun t : ℝ => (g (signedLayerCoordinates (y,t)))⁻¹ 0 j) =ᶠ[𝓝 0]
      fun _ : ℝ => if (0 : I (n+1)) = j then (1 : ℝ) else 0 :=
    hNear.mono (fun _ ht => inverse_normalMetricBlock_row hN ht (hg.2 _ ht) j)
  exact he.iteratedDeriv_eq k

theorem inverseNormalJet_eq_of_tangential_eq {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) (hN₁ : HasNormalMetricBlock 0 g₁ O₁)
    (hN₂ : HasNormalMetricBlock 0 g₂ O₂) {y : Y} (hy₁ : normalFacePoint y ∈ O₁)
    (hy₂ : normalFacePoint y ∈ O₂) (k : ℕ)
    (h : ∀ i j : I n, inverseNormalJet g₁ k y i.succ j.succ = inverseNormalJet g₂ k y i.succ j.succ) :
    inverseNormalJet g₁ k y = inverseNormalJet g₂ k y := by
  have h₁ j := inverseNormalJet_normal_row hO₁ hg₁ hN₁ hy₁ k j
  have h₂ j := inverseNormalJet_normal_row hO₂ hg₂ hN₂ hy₂ k j
  have hS₁ := inverseNormalJet_isSymm hO₁ hg₁ hy₁ k
  have hS₂ := inverseNormalJet_isSymm hO₂ hg₂ hy₂ k
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · exact (h₁ j).trans (h₂ j).symm
  · refine Fin.cases ?_ (fun b => h a b) j
    have he₁ := congrArg (fun A : Mat (n+1) => A 0 a.succ) hS₁.eq
    have he₂ := congrArg (fun A : Mat (n+1) => A 0 a.succ) hS₂.eq
    exact he₁.trans ((h₁ a.succ).trans ((h₂ a.succ).symm.trans he₂.symm))

/-- Inverting the metric again preserves equality of finite normal jets. -/
theorem metricNormalJet_eq_of_inverseNormalJet_eq
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂)
    (k : ℕ) (hEq : ∀ l ≤ k, inverseNormalJet g₁ l y = inverseNormalJet g₂ l y) :
    iteratedDeriv k (fun t : ℝ => g₁ (signedLayerCoordinates (y,t))) 0 =
      iteratedDeriv k (fun t : ℝ => g₂ (signedLayerCoordinates (y,t))) 0 := by
  let A₁ (t : ℝ) := (g₁ (signedLayerCoordinates (y,t)))⁻¹
  let A₂ (t : ℝ) := (g₂ (signedLayerCoordinates (y,t)))⁻¹
  have hA₁ : ContDiffAt ℝ ∞ A₁ 0 := contDiffAt_normalLine hO₁ (contDiffOn_invert_metric_matrix hg₁)
    (by simpa only [signedLayerCoordinates_face] using hy₁)
  have hA₂ : ContDiffAt ℝ ∞ A₂ 0 := contDiffAt_normalLine hO₂ (contDiffOn_invert_metric_matrix hg₂)
    (by simpa only [signedLayerCoordinates_face] using hy₂)
  have hInv : ContDiffAt ℝ ∞ (fun A : Mat (n+1) => A⁻¹) (A₁ 0) :=
    contDiffAt_matrix_inv_of_det_ne_zero (by
      simpa only [A₁,signedLayerCoordinates_face] using (hg₁.2 _ hy₁).inv.det_pos.ne')
  have hS (g : MetricField (n+1)) {U : Set Z} (hU : IsOpen U) (hg : CalderonN.SmoothMetric U g)
      (hy : normalFacePoint y ∈ U) :
      (fun A : Mat (n+1) => A⁻¹) ∘ (fun t : ℝ => (g (signedLayerCoordinates (y,t)))⁻¹) =ᶠ[𝓝 0]
        fun t : ℝ => g (signedLayerCoordinates (y,t)) := by
    have hc : Continuous (fun t : ℝ => signedLayerCoordinates (y,t)) :=
      signedLayerCoordinates.continuous.comp (continuous_const.prodMk continuous_id)
    have hNear : ∀ᶠ t : ℝ in 𝓝 0, signedLayerCoordinates (y,t) ∈ U :=
      hc.continuousAt.eventually_mem (hU.mem_nhds (by simpa only [signedLayerCoordinates_face] using hy))
    exact hNear.mono fun t ht =>
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.2 _ ht).det_pos.ne')
  exact ((hS g₁ hO₁ hg₁ hy₁).iteratedDeriv_eq k).symm.trans
    ((iteratedDeriv_comp_congr_finite hA₁ hA₂ hInv k hEq).trans
      ((hS g₂ hO₂ hg₂ hy₂).iteratedDeriv_eq k))

theorem normalJetAt_metric_entry_eq_of_inverseNormalJet_eq
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂)
    (k : ℕ) (hEq : ∀ l ≤ k, inverseNormalJet g₁ l y = inverseNormalJet g₂ l y)
    (i j : I (n+1)) :
    normalJetAt (fun x => g₁ x i j) k y = normalJetAt (fun x => g₂ x i j) k y := by
  change iteratedDeriv k (fun t : ℝ => g₁ (signedLayerCoordinates (y,t)) i j) 0 =
    iteratedDeriv k (fun t : ℝ => g₂ (signedLayerCoordinates (y,t)) i j) 0
  rw [iteratedDeriv_matrix_entry
      (contDiffAt_normalLine hO₁ (contDiffOn_metric_matrix hg₁) (by
        simpa only [signedLayerCoordinates_face] using hy₁)),
    iteratedDeriv_matrix_entry
      (contDiffAt_normalLine hO₂ (contDiffOn_metric_matrix hg₂) (by
        simpa only [signedLayerCoordinates_face] using hy₂)),
    metricNormalJet_eq_of_inverseNormalJet_eq hO₁ hO₂ hg₁ hg₂ hy₁ hy₂ k hEq]

theorem normalJetAt_chartVolume_eq_of_inverseNormalJet_eq
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂)
    (k : ℕ) (hEq : ∀ l ≤ k, inverseNormalJet g₁ l y = inverseNormalJet g₂ l y) :
    normalJetAt (chartVolume g₁) k y = normalJetAt (chartVolume g₂) k y := by
  let G₁ (t : ℝ) := g₁ (signedLayerCoordinates (y,t))
  let G₂ (t : ℝ) := g₂ (signedLayerCoordinates (y,t))
  have hG₁ : ContDiffAt ℝ ∞ G₁ 0 := contDiffAt_normalLine hO₁ (contDiffOn_metric_matrix hg₁)
    (by simpa only [signedLayerCoordinates_face] using hy₁)
  have hG₂ : ContDiffAt ℝ ∞ G₂ 0 := contDiffAt_normalLine hO₂ (contDiffOn_metric_matrix hg₂)
    (by simpa only [signedLayerCoordinates_face] using hy₂)
  have hDet : ContDiff ℝ ∞ (Matrix.det : Mat (n+1) → ℝ) :=
    contDiffOn_univ.mp (CalderonN.contDiffOn_det_of_entries (g := id)
      fun i j => ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.contDiffOn)
  have hPos : (G₁ 0).det ≠ 0 := by
    simpa only [G₁,signedLayerCoordinates_face] using (hg₁.2 _ hy₁).det_pos.ne'
  exact iteratedDeriv_comp_congr_finite hG₁ hG₂ (hDet.contDiffAt.sqrt hPos) k
    (fun l hl => metricNormalJet_eq_of_inverseNormalJet_eq hO₁ hO₂ hg₁ hg₂ hy₁ hy₂ l
      (fun j hj => hEq j (hj.trans hl)))

end CalderonPatch.BoundaryLayer
