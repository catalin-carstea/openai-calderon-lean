module

public import Proof.CalderonPatch.BoundaryNormalLaplacian
public import Proof.CalderonPatch.BoundarySymbolRecurrence

import Mathlib.Tactic

public section
noncomputable section
open Matrix Set

namespace CalderonPatch

open CalderonN (I X Mat MetricField metricPair chartVolume)

variable {n : ℕ}

/-- The tangential block in coordinates with the normal in slot zero. -/
@[expose] def tangentialMetricBlock (A : Mat (n+1)) : Mat n :=
  A.submatrix Fin.succ Fin.succ

theorem tangentialMetricBlock_posDef {A : Mat (n+1)} (hA : A.PosDef) :
    (tangentialMetricBlock A).PosDef :=
  hA.submatrix (Fin.succ_injective _)

theorem det_eq_tangentialMetricBlock {A : Mat (n+1)}
    (hA : ∀ j, A 0 j = if (0 : I (n+1)) = j then 1 else 0) :
    A.det = (tangentialMetricBlock A).det := by
  rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
  simp [hA,tangentialMetricBlock,eq_comm (a := (0 : I (n+1)))]

theorem tangentialMetricBlock_inverse {g : MetricField (n+1)} {O : Set (X (n+1))}
    (hN : HasNormalMetricBlock 0 g O) {z : X (n+1)} (hz : z ∈ O) (hg : (g z).PosDef) :
    tangentialMetricBlock ((g z)⁻¹) = (tangentialMetricBlock (g z))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  ext i j
  have h := congrArg (fun A : Mat (n+1) => A i.succ j.succ)
    (Matrix.mul_nonsing_inv (g z) (isUnit_iff_ne_zero.mpr hg.det_pos.ne'))
  rw [Matrix.mul_apply,Fin.sum_univ_succ,inverse_normalMetricBlock_row hN hz hg,ite_eq_right (Fin.succ_ne_zero j).symm,
    mul_zero,zero_add] at h
  simpa only [Matrix.mul_apply,tangentialMetricBlock,Matrix.submatrix_apply,
    Matrix.one_apply,Fin.succ_inj] using h

theorem normalMetric_eq_of_tangentialMetricBlock_eq {A B : Mat (n+1)}
    (hA : A.IsSymm) (hB : B.IsSymm)
    (hA₀ : ∀ j, A 0 j = if (0 : I (n+1)) = j then 1 else 0)
    (hB₀ : ∀ j, B 0 j = if (0 : I (n+1)) = j then 1 else 0)
    (h : tangentialMetricBlock A = tangentialMetricBlock B) : A = B := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i
  · exact (hA₀ j).trans (hB₀ j).symm
  · refine Fin.cases ?_ (fun l => ?_) j
    · have hA' := congrArg (fun C : Mat (n+1) => C 0 k.succ) hA.eq
      have hB' := congrArg (fun C : Mat (n+1) => C 0 k.succ) hB.eq
      exact hA'.trans ((hA₀ _).trans ((hB₀ _).symm.trans hB'.symm))
    · exact congrArg (fun C : Mat n => C k l) h

end CalderonPatch
