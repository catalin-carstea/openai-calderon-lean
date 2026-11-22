module

public import Proof.CalderonPatch.SignedNormalMetricJets
public import Proof.CalderonN.MetricVolumeDifferential

import Mathlib.Tactic

public section
noncomputable section
open Filter Finset Matrix Set
open scoped ContDiff Topology

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField axis coordDeriv matrixFieldDerivative)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

section
open scoped Matrix.Norms.Operator

/-- In the normal block, the signed drift is the trace of the metric
against the normal derivative of its inverse. -/
theorem signed_normalDrift_eq_trace_invDerivative {O : Set Z} (hO : IsOpen O)
    {g : MetricField (n+1)} (hg : CalderonN.SmoothMetric O g) (hN : HasNormalMetricBlock 0 g O)
    {x : Z} (hx : x ∈ O) :
    (-2) * laplaceFirstCoeff g x 0 =
      ∑ i : I (n+1), ∑ j : I (n+1), g x i j * coordDeriv 0 (fun z => (g z)⁻¹ j i) x := by
  let A := g x
  let D := matrixFieldDerivative g x (axis (0 : I (n+1)))
  let V := matrixFieldDerivative (fun z => (g z)⁻¹) x (axis (0 : I (n+1)))
  have hDiff (i j : I (n+1)) : DifferentiableAt ℝ (fun z => g z i j) x :=
    ((hg.1 i j).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
  have hV : V = -(A⁻¹ * D * A⁻¹) := by
    have hA (i j : I (n+1)) : DifferentiableAt ℝ (fun z => (g z)⁻¹ i j) x :=
      ((CalderonN.contDiffOn_metric_inv_entry hg i j).contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)
    rw [show V = fderiv ℝ (fun z => (g z)⁻¹) x (axis 0) from
      congrArg (fun L : Z →L[ℝ] Mat (n+1) => L (axis 0))
        (CalderonN.hasFDerivAt_matrixField_of_entries _ _ hA).fderiv.symm]
    exact CalderonN.fderiv_inverseMetric_matrix_apply g x (axis 0) hDiff (hg.2 _ hx)
  have hMul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.2 _ hx).det_pos.ne')
  have hTrace : (A * V).trace = -(A⁻¹ * D).trace := by
    rw [hV,Matrix.mul_neg,Matrix.trace_neg,← Matrix.mul_assoc A (A⁻¹ * D) A⁻¹,
      ← Matrix.mul_assoc A A⁻¹ D,hMul,one_mul,Matrix.trace_mul_comm]
  have hRead : (A * V).trace =
      ∑ i : I (n+1), ∑ j : I (n+1), g x i j * coordDeriv 0 (fun z => (g z)⁻¹ j i) x := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,A,V,
      CalderonN.matrixFieldDerivative_apply_entry,coordDeriv]
  rw [laplace_normal_firstCoeff hO hg hN hx,← hRead,hTrace]
  change (-2 : ℝ) * ((A⁻¹ * D).trace / 2) = _
  ring

end

open scoped Matrix.Norms.Elementwise

/-- The first still unequal normal drift jet is the trace of the
first still unequal inverse metric jet against their common metric. -/
theorem signed_normalDrift_top_difference
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) (hN₁ : HasNormalMetricBlock 0 g₁ O₁)
    (hN₂ : HasNormalMetricBlock 0 g₂ O₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂)
    (L : ℕ) (hEq : ∀ l ≤ L, inverseNormalJet g₁ l y = inverseNormalJet g₂ l y) :
    normalJetAt (fun z => (-2) * laplaceFirstCoeff g₁ z 0) L y -
      normalJetAt (fun z => (-2) * laplaceFirstCoeff g₂ z 0) L y =
      (g₁ (normalFacePoint y) * (inverseNormalJet g₁ (L+1) y - inverseNormalJet g₂ (L+1) y)).trace := by
  let c (t : ℝ) := signedLayerCoordinates (y,t)
  let A (g : MetricField (n+1)) (j i : I (n+1)) (t : ℝ) := (g (c t))⁻¹ j i
  let G (g : MetricField (n+1)) (i j : I (n+1)) (t : ℝ) := g (c t) i j
  have hc : Continuous c := signedLayerCoordinates.continuous.comp (continuous_const.prodMk continuous_id)
  have hGs {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)} (hg : CalderonN.SmoothMetric O g)
      (hy : normalFacePoint y ∈ O) (i j : I (n+1)) :
      ContDiffAt ℝ ∞ (G g i j) 0 :=
    contDiffAt_normalLine hO (hg.1 i j) (by simpa only [signedLayerCoordinates_face] using hy)
  have hAs {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)} (hg : CalderonN.SmoothMetric O g)
      (hy : normalFacePoint y ∈ O) (i j : I (n+1)) :
      ContDiffAt ℝ ∞ (A g i j) 0 :=
    contDiffAt_normalLine hO (CalderonN.contDiffOn_metric_inv_entry hg i j)
      (by simpa only [signedLayerCoordinates_face] using hy)
  have hSplit {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)} (hg : CalderonN.SmoothMetric O g)
      (hN : HasNormalMetricBlock 0 g O) (hy : normalFacePoint y ∈ O) :
      normalJetAt (fun z => (-2) * laplaceFirstCoeff g z 0) L y =
        ∑ i : I (n+1), ∑ j : I (n+1), iteratedDeriv L (fun t => G g i j t * deriv (A g j i) t) 0 := by
    have hNear : ∀ᶠ t : ℝ in 𝓝 0, c t ∈ O :=
      hc.continuousAt.eventually_mem (hO.mem_nhds (by simpa only [c,signedLayerCoordinates_face] using hy))
    have he : (fun t : ℝ => (-2) * laplaceFirstCoeff g (c t) 0) =ᶠ[𝓝 0]
        fun t : ℝ => ∑ i : I (n+1), ∑ j : I (n+1), G g i j t * deriv (A g j i) t :=
      hNear.mono (fun t ht => by
        change (-2) * laplaceFirstCoeff g (c t) 0 = ∑ i, ∑ j, G g i j t * deriv (A g j i) t
        rw [signed_normalDrift_eq_trace_invDerivative hO hg hN ht]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        change g (c t) i j * coordDeriv 0 (fun z => (g z)⁻¹ j i) (c t) =
          g (c t) i j * deriv (fun s : ℝ => (g (signedLayerCoordinates (y,s)))⁻¹ j i) t
        rw [deriv_normalLine hO (CalderonN.contDiffOn_metric_inv_entry hg j i) ht])
    change iteratedDeriv L (fun t : ℝ => (-2) * laplaceFirstCoeff g (c t) 0) 0 = _
    rw [he.iteratedDeriv_eq L]
    have hF (i j : I (n+1)) :
        ContDiffAt ℝ L (fun t => G g i j t * deriv (A g j i) t) 0 :=
      ((hGs hO hg hy i j).mul ((hAs hO hg hy j i).derivWithin (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞))).of_le (by simp)
    rw [iteratedDeriv_fun_sum (fun i _ => ContDiffAt.sum (fun j _ => hF i j))]
    exact sum_congr rfl (fun i _ => iteratedDeriv_fun_sum (fun j _ => hF i j))
  rw [hSplit hO₁ hg₁ hN₁ hy₁,hSplit hO₂ hg₂ hN₂ hy₂,← sum_sub_distrib]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.sub_apply]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  have hF (l : ℕ) (hl : l ≤ L) : iteratedDeriv l (G g₁ i j) 0 = iteratedDeriv l (G g₂ i j) 0 :=
    normalJetAt_metric_entry_eq_of_inverseNormalJet_eq hO₁ hO₂ hg₁ hg₂ hy₁ hy₂ l
      (fun k hk => hEq k (hk.trans hl)) i j
  have hJ (g : MetricField (n+1)) {O : Set Z} (hO : IsOpen O) (hg : CalderonN.SmoothMetric O g)
      (hy : normalFacePoint y ∈ O) (l : ℕ) :
      iteratedDeriv l (deriv (A g j i)) 0 = inverseNormalJet g (l+1) y j i := by
    rw [← iteratedDeriv_succ',inverseNormalJet_entry hO hg hy]
    rfl
  have hG (l : ℕ) (hl : l < L) :
      iteratedDeriv l (deriv (A g₁ j i)) 0 = iteratedDeriv l (deriv (A g₂ j i)) 0 := by
    rw [hJ g₁ hO₁ hg₁ hy₁,hJ g₂ hO₂ hg₂ hy₂,hEq (l+1) (by omega)]
  rw [iteratedDeriv_mul_top_right_difference (hGs hO₁ hg₁ hy₁ i j) (hGs hO₂ hg₂ hy₂ i j)
    ((hAs hO₁ hg₁ hy₁ j i).derivWithin (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)) ((hAs hO₂ hg₂ hy₂ j i).derivWithin (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)) L hF hG,
    hJ g₁ hO₁ hg₁ hy₁,hJ g₂ hO₂ hg₂ hy₂]
  simp only [G,c,signedLayerCoordinates_face]

end CalderonPatch.BoundaryLayer
