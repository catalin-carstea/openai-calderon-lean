module

public import Proof.CalderonPatch.NativeTraceTopResponse
public import Proof.CalderonPatch.TangentialMetricBlock

import Mathlib.Tactic

public section
noncomputable section
open Finset Matrix Set

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField metricPair)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

private theorem trace_mul_eq_tangent_of_zero_normal {A B : Mat (n+1)}
    (hB : ∀ i, B 0 i = 0) (hS : B.IsSymm) :
    (A * B).trace = (tangentialMetricBlock A * tangentialMetricBlock B).trace := by
  have hb (i : I (n+1)) : B i 0 = 0 :=
    (congrArg (fun C : Mat (n+1) => C 0 i) hS.eq).trans (hB i)
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,tangentialMetricBlock,Matrix.submatrix_apply]
  rw [Fin.sum_univ_succ]
  simp only [hb,mul_zero,Finset.sum_const_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ,hB,mul_zero,zero_add]

/-- A quadratic form equal to its trace times the leading quadratic
form must vanish on a tangential space of dimension at least two. -/
theorem inverseNormalJet_eq_of_trace_direction
    (hn : 2 ≤ n) {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) (hN₁ : HasNormalMetricBlock 0 g₁ O₁)
    (hN₂ : HasNormalMetricBlock 0 g₂ O₂) {y : Y}
    (hy₁ : normalFacePoint y ∈ O₁) (hy₂ : normalFacePoint y ∈ O₂) (k : ℕ)
    (h : ∀ ξ : I n → ℝ,
      inverseQuadraticNormalJet g₁ k ξ y - inverseQuadraticNormalJet g₂ k ξ y =
        faceInverseQuadratic g₁ ξ y *
          (g₁ (normalFacePoint y) * (inverseNormalJet g₁ k y - inverseNormalJet g₂ k y)).trace) :
    inverseNormalJet g₁ k y = inverseNormalJet g₂ k y := by
  let A := g₁ (normalFacePoint y)
  let H := tangentialMetricBlock A⁻¹
  let D := inverseNormalJet g₁ k y - inverseNormalJet g₂ k y
  let F := tangentialMetricBlock D
  have hA : A.PosDef := hg₁.2 _ hy₁
  have hH : H.PosDef := tangentialMetricBlock_posDef hA.inv
  have hS : D.IsSymm :=
    (inverseNormalJet_isSymm hO₁ hg₁ hy₁ k).sub (inverseNormalJet_isSymm hO₂ hg₂ hy₂ k)
  have hF : F.IsSymm := by
    ext i j
    exact congrArg (fun B : Mat (n+1) => B i.succ j.succ) hS.eq
  have hD₀ (j : I (n+1)) : D 0 j = 0 := by
    change inverseNormalJet g₁ k y 0 j - inverseNormalJet g₂ k y 0 j = 0
    rw [inverseNormalJet_normal_row hO₁ hg₁ hN₁ hy₁,
      inverseNormalJet_normal_row hO₂ hg₂ hN₂ hy₂,sub_self]
  have hT : (A * D).trace = (H⁻¹ * F).trace := by
    rw [trace_mul_eq_tangent_of_zero_normal hD₀ hS]
    change _ = ((tangentialMetricBlock A⁻¹)⁻¹ * F).trace
    rw [tangentialMetricBlock_inverse hN₁ hy₁ hA,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (tangentialMetricBlock_posDef hA).det_pos.ne')]
  have hQ (v : Y) : faceInverseQuadratic g₁ (WithLp.ofLp v) y =
      metricPair (fun _ => H) 0 v v := by
    simp only [faceInverseQuadratic,signedLayerCoordinates_face,metricPair,H,A,tangentialMetricBlock,
      Matrix.submatrix_apply]
  have hR (v : Y) : inverseQuadraticNormalJet g₁ k (WithLp.ofLp v) y -
      inverseQuadraticNormalJet g₂ k (WithLp.ofLp v) y = metricPair (fun _ => F) 0 v v := by
    simp only [inverseQuadraticNormalJet,metricPair,F,D,tangentialMetricBlock,Matrix.submatrix_apply,
      Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
  have hF₀ : F = 0 := by
    apply normalJet_eq_zero_of_trace_direction_eq hn hH hF
    intro v hv
    have he := h (WithLp.ofLp v)
    change _ = faceInverseQuadratic g₁ (WithLp.ofLp v) y * (A * D).trace at he
    rw [hQ,hR,hv,one_mul,hT] at he
    exact he.symm
  apply inverseNormalJet_eq_of_tangential_eq hO₁ hO₂ hg₁ hg₂ hN₁ hN₂ hy₁ hy₂ k
  intro i j
  exact sub_eq_zero.mp (congrArg (fun B : Mat n => B i j) hF₀)

end CalderonPatch.BoundaryLayer
