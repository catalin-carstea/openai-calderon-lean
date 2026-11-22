module

public import Proof.CalderonPatch.SignedNormalMetricJets

import Proof.CalderonN.MetricDivergence
import Mathlib.Tactic

public section
noncomputable section
open Filter Finset Set
open scoped ContDiff Topology

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I MetricField chartVolume coordDeriv divergenceCoeff)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

/-- In normal coordinates the first tangential terms depend only on
the tangential divergence of the density-weighted inverse block. -/
theorem laplaceFirstCoeff_tangent_eq_divergence {O : Set Z} (hO : IsOpen O)
    {g : MetricField (n+1)} (hg : CalderonN.SmoothMetric O g)
    (hN : HasNormalMetricBlock 0 g O) {z : Z} (hz : z ∈ O) (j : I n) :
    laplaceFirstCoeff g z j.succ =
      (∑ i : I n, coordDeriv i.succ (fun x => divergenceCoeff g x i.succ j.succ) z) *
        (chartVolume g z)⁻¹ := by
  have h := CalderonN.divergenceCoeff_connection hO hg hz j.succ
  rw [Fin.sum_univ_succ] at h
  have he : coordDeriv 0 (fun x => divergenceCoeff g x 0 j.succ) z = 0 := by
    have hz0 : (fun x => divergenceCoeff g x 0 j.succ) =ᶠ[𝓝 z] fun _ => 0 :=
      Filter.mem_of_superset (hO.mem_nhds hz) (fun x hx => by
        change chartVolume g x * (g x)⁻¹ 0 j.succ = 0
        rw [inverse_normalMetricBlock_row hN hx (hg.2 _ hx),
          ite_eq_right (Fin.succ_ne_zero j).symm,mul_zero])
    simp only [coordDeriv,hz0.fderiv_eq,fderiv_const_apply,_root_.zero_apply]
  rw [he,zero_add,neg_mul] at h
  have hp : chartVolume g z ≠ 0 := (Real.sqrt_pos.2 (hg.2 _ hz).det_pos).ne'
  rw [h,laplaceFirstCoeff]
  field_simp

private theorem volume_nonzero_on {O : Set Z} {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) {x : Z} (hx : x ∈ O) :
    chartVolume g x ≠ 0 := (Real.sqrt_pos.2 (hg.2 _ hx).det_pos).ne'

private theorem normalJetAt_inv_chartVolume_eq
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂)
    (k : ℕ) (hEq : ∀ l ≤ k, inverseNormalJet g₁ l y = inverseNormalJet g₂ l y) :
    normalJetAt (fun z => (chartVolume g₁ z)⁻¹) k y =
      normalJetAt (fun z => (chartVolume g₂ z)⁻¹) k y := by
  let F (g : MetricField (n+1)) (t : ℝ) := chartVolume g (signedLayerCoordinates (y,t))
  have hF₁ : ContDiffAt ℝ ∞ (F g₁) 0 :=
    contDiffAt_normalLine hO₁ (CalderonN.contDiffOn_metric_volume hg₁)
      (by simpa only [signedLayerCoordinates_face] using hy₁)
  have hF₂ : ContDiffAt ℝ ∞ (F g₂) 0 :=
    contDiffAt_normalLine hO₂ (CalderonN.contDiffOn_metric_volume hg₂)
      (by simpa only [signedLayerCoordinates_face] using hy₂)
  have he : ContDiffAt ℝ ∞ (fun x : ℝ => x⁻¹) (F g₁ 0) :=
    contDiffAt_id.inv (by simpa only [F,id_eq,signedLayerCoordinates_face] using volume_nonzero_on hg₁ hy₁)
  exact iteratedDeriv_comp_congr_finite hF₁ hF₂ he k
    (fun l hl => normalJetAt_chartVolume_eq_of_inverseNormalJet_eq hO₁ hO₂ hg₁ hg₂ hy₁ hy₂ l
      (fun q hq => hEq q (hq.trans hl)))

private theorem normalJetAt_divergenceCoeff_eq
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂)
    (k : ℕ) (hEq : ∀ l ≤ k, inverseNormalJet g₁ l y = inverseNormalJet g₂ l y)
    (i j : I (n+1)) :
    normalJetAt (fun z => divergenceCoeff g₁ z i j) k y =
      normalJetAt (fun z => divergenceCoeff g₂ z i j) k y := by
  let c (t : ℝ) := signedLayerCoordinates (y,t)
  have h₁ : c 0 ∈ O₁ := by simpa only [c,signedLayerCoordinates_face] using hy₁
  have h₂ : c 0 ∈ O₂ := by simpa only [c,signedLayerCoordinates_face] using hy₂
  change iteratedDeriv k (fun t => chartVolume g₁ (c t) * (g₁ (c t))⁻¹ i j) 0 =
    iteratedDeriv k (fun t => chartVolume g₂ (c t) * (g₂ (c t))⁻¹ i j) 0
  apply iteratedDeriv_mul_congr_finite
    (contDiffAt_normalLine hO₁ (CalderonN.contDiffOn_metric_volume hg₁) h₁)
    (contDiffAt_normalLine hO₂ (CalderonN.contDiffOn_metric_volume hg₂) h₂)
    (contDiffAt_normalLine hO₁ (CalderonN.contDiffOn_metric_inv_entry hg₁ i j) h₁)
    (contDiffAt_normalLine hO₂ (CalderonN.contDiffOn_metric_inv_entry hg₂ i j) h₂)
  · intro l hl
    exact normalJetAt_chartVolume_eq_of_inverseNormalJet_eq hO₁ hO₂ hg₁ hg₂ hy₁ hy₂ l
      (fun q hq => hEq q (hq.trans hl))
  · intro l hl
    exact (inverseNormalJet_entry hO₁ hg₁ hy₁ l i j).symm.trans
      ((congrArg (fun A => A i j) (hEq l hl)).trans (inverseNormalJet_entry hO₂ hg₂ hy₂ l i j))

/-- Matching normal inverse metric jets as functions of the face
implies the same-order tangential drift jets. -/
theorem eqOn_tangentDrift_normalJet_of_eqOn_inverseNormalJet
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) (hN₁ : HasNormalMetricBlock 0 g₁ O₁)
    (hN₂ : HasNormalMetricBlock 0 g₂ O₂) {U : Set Y} (hU : IsOpen U)
    (h₁ : MapsTo normalFacePoint U O₁) (h₂ : MapsTo normalFacePoint U O₂)
    (k : ℕ) (hEq : ∀ l ≤ k, EqOn (inverseNormalJet g₁ l) (inverseNormalJet g₂ l) U)
    (j : I n) :
    EqOn (normalJetAt (fun z => laplaceFirstCoeff g₁ z j.succ) k)
      (normalJetAt (fun z => laplaceFirstCoeff g₂ z j.succ) k) U := by
  let div (g : MetricField (n+1)) (z : Z) :=
    ∑ i : I n, coordDeriv i.succ (fun x => divergenceCoeff g x i.succ j.succ) z
  have hCont {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)}
      (hg : CalderonN.SmoothMetric O g) : ContDiffOn ℝ ∞ (div g) O :=
    ContDiffOn.sum fun i _ => CalderonN.contDiffOn_coordDeriv
      (CalderonN.contDiffOn_divergenceCoeff hg i.succ j.succ) hO i.succ
  intro y hy
  let c (t : ℝ) := signedLayerCoordinates (y,t)
  have hc : Continuous c := signedLayerCoordinates.continuous.comp (continuous_const.prodMk continuous_id)
  have hRead {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)}
      (hg : CalderonN.SmoothMetric O g) (hN : HasNormalMetricBlock 0 g O) (hy : normalFacePoint y ∈ O) :
      normalJetAt (fun z => laplaceFirstCoeff g z j.succ) k y =
        iteratedDeriv k (fun t => div g (c t) * (chartVolume g (c t))⁻¹) 0 := by
    have hNear : ∀ᶠ t : ℝ in 𝓝 0, c t ∈ O :=
      hc.continuousAt.eventually_mem (hO.mem_nhds (by simpa only [c,signedLayerCoordinates_face] using hy))
    have he : (fun t => laplaceFirstCoeff g (c t) j.succ) =ᶠ[𝓝 0]
        fun t => div g (c t) * (chartVolume g (c t))⁻¹ :=
      hNear.mono (fun _ ht => laplaceFirstCoeff_tangent_eq_divergence hO hg hN ht j)
    exact he.iteratedDeriv_eq k
  have h₁c : c 0 ∈ O₁ := by simpa only [c,signedLayerCoordinates_face] using h₁ hy
  have h₂c : c 0 ∈ O₂ := by simpa only [c,signedLayerCoordinates_face] using h₂ hy
  rw [hRead hO₁ hg₁ hN₁ (h₁ hy),hRead hO₂ hg₂ hN₂ (h₂ hy)]
  apply iteratedDeriv_mul_congr_finite
    (contDiffAt_normalLine hO₁ (hCont hO₁ hg₁) h₁c)
    (contDiffAt_normalLine hO₂ (hCont hO₂ hg₂) h₂c)
    (contDiffAt_normalLine hO₁ ((CalderonN.contDiffOn_metric_volume hg₁).inv (fun x hx => volume_nonzero_on hg₁ hx)) h₁c)
    (contDiffAt_normalLine hO₂ ((CalderonN.contDiffOn_metric_volume hg₂).inv (fun x hx => volume_nonzero_on hg₂ hx)) h₂c)
  · intro l hl
    dsimp only [div]
    rw [iteratedDeriv_fun_sum (fun i _ => (contDiffAt_normalLine hO₁
        (CalderonN.contDiffOn_coordDeriv (CalderonN.contDiffOn_divergenceCoeff hg₁ i.succ j.succ) hO₁ i.succ) h₁c).of_le (by simp)),
      iteratedDeriv_fun_sum (fun i _ => (contDiffAt_normalLine hO₂
        (CalderonN.contDiffOn_coordDeriv (CalderonN.contDiffOn_divergenceCoeff hg₂ i.succ j.succ) hO₂ i.succ) h₂c).of_le (by simp))]
    apply sum_congr rfl
    intro i _
    exact eqOn_normalJetAt_coordDeriv_tangent hO₁ hO₂
      (CalderonN.contDiffOn_divergenceCoeff hg₁ i.succ j.succ)
      (CalderonN.contDiffOn_divergenceCoeff hg₂ i.succ j.succ) hU h₁ h₂ l i
      (fun x hx => normalJetAt_divergenceCoeff_eq hO₁ hO₂ hg₁ hg₂ (h₁ hx) (h₂ hx) l
        (fun q hq => hEq q (hq.trans hl) hx) i.succ j.succ) hy
  · intro l hl
    exact normalJetAt_inv_chartVolume_eq hO₁ hO₂ hg₁ hg₂ (h₁ hy) (h₂ hy) l
      (fun q hq => hEq q (hq.trans hl) hy)

end CalderonPatch.BoundaryLayer
