module

public import Proof.CalderonN.FixedBallGreenPairing
public import Proof.CalderonN.SmoothSphereRotation

import Proof.CalderonN.LinearMetric
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic

/-! Adapted from `ConormalDecomposition` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- The directional vector of the metric conormal in the fixed ball. -/
@[expose] def ballConormalVector (g : (MetricField dim)) (w : (X dim)) : (X dim) :=
  WithLp.toLp 2 (fun j => ∑ i, w i * divergenceCoeff g w i j)

theorem contDiffOn_ballConormalVector {U : Set (X dim)} {g : (MetricField dim)}
    (hg : SmoothMetric U g) : ContDiffOn ℝ ∞ (ballConormalVector g) U := by
  apply (contDiffOn_piLp 2).mpr
  intro j
  change ContDiffOn ℝ ∞ (fun w : (X dim) => ∑ i, w i * divergenceCoeff g w i j) U
  exact ContDiffOn.sum fun i _ =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.mul (contDiffOn_divergenceCoeff hg i j)

theorem ballConormal_eq_fderiv_conormalVector (g : (MetricField dim)) (u : (X dim) → ℝ) (w : (X dim)) :
    ballConormal g u w = fderiv ℝ u w (ballConormalVector g w) := by
  rw [ballConormal,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct,metricFluxVector,PiLp.toLp_apply,divergenceFlux]
  conv_rhs => rw [← vector_eq_sum_axis (ballConormalVector g w)]
  simp only [map_sum,map_smul,smul_eq_mul,ballConormalVector,PiLp.toLp_apply,Finset.sum_mul,coordDeriv]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ballConormalVector_inner_pos {g : (MetricField dim)} {w : (X dim)}
    (hg : (g w).PosDef) (hw : w ≠ 0) :
    0 < ⟪w,ballConormalVector g w⟫_ℝ := by
  have hw' : (fun i : (I dim) => w i) ≠ 0 := by
    intro h
    apply hw
    ext i
    exact congrFun h i
  have h := hg.inv.dotProduct_mulVec_pos hw'
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial,dotProduct,ballConormalVector,PiLp.toLp_apply,Finset.sum_mul]
  have hEq : (∑ i : (I dim), ∑ j : (I dim), (w j * divergenceCoeff g w j i) * w i) =
      chartVolume g w * ((fun i : (I dim) => w i) ⬝ᵥ ((g w)⁻¹ *ᵥ (fun i : (I dim) => w i))) := by
    rw [Finset.sum_comm]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,divergenceCoeff]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hEq]
  exact mul_pos (Real.sqrt_pos.2 hg.det_pos) h

/-- Decompose velocity into the metric conormal and a Euclidean tangential vector. -/
@[expose] def conormalComponent (g : (MetricField dim)) (w V : (X dim)) : ℝ :=
  ⟪w,V⟫_ℝ / ⟪w,ballConormalVector g w⟫_ℝ

@[expose] def tangentialComponent (g : (MetricField dim)) (w V : (X dim)) : (X dim) :=
  V - conormalComponent g w V • ballConormalVector g w

theorem tangentialComponent_inner_zero {g : (MetricField dim)} {w V : (X dim)}
    (hg : (g w).PosDef) (hw : w ≠ 0) :
    ⟪w,tangentialComponent g w V⟫_ℝ = 0 := by
  rw [tangentialComponent,inner_sub_right,real_inner_smul_right,conormalComponent,
    div_mul_cancel₀ _ (ballConormalVector_inner_pos hg hw).ne',sub_self]

theorem sum_rotationVector_smul (w V : (X dim)) :
    (∑ i, ∑ j, (w i * V j) • rotationVector i j w) =
      ⟪w,w⟫_ℝ • V - ⟪w,V⟫_ℝ • w := by
  rw [EuclideanSpace.inner_eq_star_dotProduct,EuclideanSpace.inner_eq_star_dotProduct]
  ext k
  change EuclideanSpace.proj k (∑ i, ∑ j, (w i * V j) • rotationVector i j w) =
    EuclideanSpace.proj k (_ • V - _ • w)
  simp only [map_sum, map_sub, map_smul, smul_eq_mul, EuclideanSpace.coe_proj, star_trivial, dotProduct]
  have hsplit (i j : I dim) :
      w i * V j * rotationVector i j w k =
        (if k = j then w i * w i * V j else 0) - (if k = i then w i * w j * V j else 0) := by
    simp only [rotationVector,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply]
    split_ifs <;> ring
  simp_rw [hsplit,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j : I dim => if k = i then w i * w j * V j else 0)]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  congr 1
  · rw [Finset.sum_mul]
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The first derivative of a moving trace on the fixed sphere is the
conormal derivative plus the sum of tangential rotation derivatives. -/
theorem fderiv_eq_conormal_add_rotations {g : (MetricField dim)} {w : (X dim)}
    (hg : (g w).PosDef) (hw : w ∈ (standardSphere dim)) (u : (X dim) → ℝ) (V : (X dim)) :
    fderiv ℝ u w V = conormalComponent g w V * ballConormal g u w +
      ∑ i, ∑ j, (w i * tangentialComponent g w V j) * sphereRotationDerivative i j u w := by
  have hn : ‖w‖ = 1 := by simpa only [standardSphere,Metric.mem_sphere,dist_zero_right] using hw
  have hw₀ : w ≠ 0 := fun hz => by simp [hz] at hn
  have hi : ⟪w,w⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,hn,one_pow]
  have hSum := sum_rotationVector_smul w (tangentialComponent g w V)
  rw [hi,tangentialComponent_inner_zero hg hw₀,one_smul,zero_smul,sub_zero] at hSum
  conv_lhs =>
    rw [show V = conormalComponent g w V • ballConormalVector g w + tangentialComponent g w V by
      unfold tangentialComponent
      abel, ← hSum]
  simp only [map_add,map_sum,map_smul,smul_eq_mul,ballConormal_eq_fderiv_conormalVector,
    sphereRotationDerivative]

end CalderonN
