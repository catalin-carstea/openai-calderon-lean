module

public import Proof.CalderonN.AngleSpatialDerivative
public import Proof.CalderonN.CommonSupportOperatorDerivative
public import Proof.CalderonN.MatrixFieldJetNorms

import Mathlib.Tactic

/-! Adapted from `Proof/AngleLowJetDerivative.lean` in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim]

/-- Local coefficient-angle C1 control is exactly the low-jet input required
    by the genuine completed Sobolev operator derivative bounds. -/
theorem norm_fderiv_angle_spatial_low_jets_le
    (a : ℝ × (X dim) → ℝ) (ha : ContDiff ℝ ∞ a) (b : (X dim) → ℝ)
    (hb : ∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0)
    (x : (X dim)) (q : ℝ) (hq : 0 ≤ q) (h0 : |b x| ≤ q) (h1 : ‖fderiv ℝ b x‖ ≤ q)
    (j : Fin 2) :
    ‖fderiv ℝ (fun θ => iteratedFDeriv ℝ j.val (fun z => a (θ,z)) x) 0‖ ≤ q := by
  fin_cases j
  · let C := (continuousMultilinearCurryFin0 ℝ (X dim) ℝ).symm
    have h := C.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ) (hb x)
    simp only [Function.comp_def] at h
    have hSame : (fun θ => iteratedFDeriv ℝ 0 (fun z => a (θ,z)) x) = fun θ => C (a (θ,x)) := rfl
    rw [hSame]
    have hn : ‖fderiv ℝ (fun θ => C (a (θ,x))) 0‖ = ‖C (b x)‖ := by
      rw [← norm_deriv_eq_norm_fderiv]
      exact congrArg norm h.deriv
    rw [hn,LinearIsometryEquiv.norm_map,Real.norm_eq_abs]
    exact h0
  · let C := (continuousMultilinearCurryFin1 ℝ (X dim) ℝ).symm
    have h := C.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0:ℝ)
      (hasDerivAt_spatial_fderiv_of_angle_generator a ha b hb x)
    simp only [Function.comp_def] at h
    have hSame : (fun θ => iteratedFDeriv ℝ 1 (fun z => a (θ,z)) x) =
        fun θ => C (fderiv ℝ (fun z => a (θ,z)) x) := by
      funext θ
      ext v
      simp only [iteratedFDeriv_one_apply]
      rfl
    rw [hSame]
    have hn : ‖fderiv ℝ (fun θ => C (fderiv ℝ (fun z => a (θ,z)) x)) 0‖ =
        ‖C (fderiv ℝ b x)‖ := by
      rw [← norm_deriv_eq_norm_fderiv]
      exact congrArg norm h.deriv
    rw [hn,LinearIsometryEquiv.norm_map]
    exact h1



/-- A genuine matrix coefficient angle generator with a local C1 bound gives
    the actual strong/full Dirichlet operator angle derivative budgets. -/
theorem norm_fderiv_angle_commonSupport_operators_le
    (hcalc : FixedSobolevCalculus dim) (a : ℝ × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ θ z,z ∉ K → a (θ,z) = 0)
    (b : (X dim) → (Mat dim)) (hbSmooth : Differentiable ℝ b)
    (hb : ∀ z,HasDerivAt (fun θ => a (θ,z)) (b z) 0)
    (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ x ∈ ((fixedBallOpens dim):Set (X dim)),‖b x‖ ≤ q)
    (hSpatial : ∀ x ∈ ((fixedBallOpens dim):Set (X dim)),‖fderiv ℝ b x‖ ≤ q) :
    ‖fderiv ℝ (fun θ => strongDirichletOperator hcalc 0
      (commonSupportMatrixFamily 2 a ha K hK hz θ)) 0‖ ≤ 2*strongC1OperatorBudget hcalc*q ∧
    ‖fderiv ℝ (fun θ => fullBallDivergenceL 0
      (commonSupportMatrixFamily 2 a ha K hK hz θ)) 0‖ ≤ 2*fullC1OperatorBudget (dim := dim)*q := by
  have hJets (i j : (I dim)) (k : Fin 2) (x : (X dim)) (hx : x ∈ ((fixedBallOpens dim):Set (X dim))) :
      ‖fderiv ℝ (fun θ => iteratedFDeriv ℝ k.val (fun z => a (θ,z) i j) x) 0‖ ≤ q := by
    have hEntry (z : (X dim)) : HasDerivAt (fun θ => a (θ,z) i j) (b z i j) 0 := by
      simpa only [Function.comp_def,matrixEntryL_apply] using
        (matrixEntryL i j).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hb z)
    have h0 : |b x i j| ≤ q :=
      (Matrix.norm_entry_le_entrywise_sup_norm (b x) (i:=i) (j:=j)).trans (hValue x hx)
    have h1 : ‖fderiv ℝ (fun z => b z i j) x‖ ≤ q := by
      apply ContinuousLinearMap.opNorm_le_bound _ hq
      intro v
      have hEq := congrArg (fun L : (X dim) →L[ℝ] ℝ => L v) (fderiv_matrix_entry b x (hbSmooth x) i j)
      change fderiv ℝ (fun z => b z i j) x v = fderiv ℝ b x v i j at hEq
      rw [hEq]
      exact (Matrix.norm_entry_le_entrywise_sup_norm (fderiv ℝ b x v) (i:=i) (j:=j)).trans
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hSpatial x hx) (norm_nonneg v)))
    exact norm_fderiv_angle_spatial_low_jets_le (fun v => a v i j)
      (contDiff_pi.mp (contDiff_pi.mp ha i) j) (fun z => b z i j) hEntry x q hq h0 h1 k
  exact ⟨norm_fderiv_commonSupport_strongOperator_zero_le hcalc a ha K hK hz 0 q hq hJets,
    norm_fderiv_commonSupport_fullOperator_zero_le a ha K hK hz 0 q hq hJets⟩

end CalderonN
