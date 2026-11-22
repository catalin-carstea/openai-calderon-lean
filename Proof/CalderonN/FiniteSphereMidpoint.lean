module

public import Proof.CalderonN.SphereSobolevMidpointFiniteBound
public import Proof.CalderonN.HarmonicH1Lift

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

/-! Use the released finite Hilbert-block interpolation estimate on a
shared finite harmonic datum with compatible weak and strong outputs. -/

public section

noncomputable section
open Set Filter
open scoped ENNReal Topology Classical DirectSum
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon.SphereHarmonic

variable {dim : ℕ} [NeZero dim]

theorem harmonicBoundaryFiniteL_mem_finiteSupport (s : ℝ) (f : HarmonicFiniteCoefficients dim) :
    harmonicBoundaryFiniteL s f ∈ sphereSobolevFiniteSupport s := by
  refine ⟨f.support.sup id + 1,?_⟩
  intro k hk
  have hNot : k ∉ f.support := by
    intro h
    have hle : k ≤ f.support.sup id := Finset.le_sup (f := id) h
    omega
  rw [harmonicBoundaryFiniteL_eq_sum,map_sum]
  exact Finset.sum_eq_zero fun i hi => sphereSobolevCoefficientL_single_ne s i k
    (fun h => hNot (h.symm ▸ hi)) (f i)

theorem sphereSobolevInclusionL_harmonicBoundaryFiniteL (s t : ℝ) (h : t ≤ s)
    (f : HarmonicFiniteCoefficients dim) :
    sphereSobolevInclusionL s t h (harmonicBoundaryFiniteL s f) = harmonicBoundaryFiniteL t f := by
  simp only [harmonicBoundaryFiniteL_eq_sum,map_sum,sphereSobolevInclusionL_single]

private def extendFiniteBoundaryL (s t : ℝ)
    (R : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim t) :
    SphereSobolev dim s →L[ℝ] SphereSobolev dim t :=
  LinearMap.extendOfNorm R (harmonicBoundaryFiniteL s)

private theorem extendFiniteBoundaryL_apply (s t : ℝ)
    (R : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim t) (B : ℝ)
    (hR : ∀ f, ‖R f‖ ≤ B*‖harmonicBoundaryFiniteL s f‖) (f : HarmonicFiniteCoefficients dim) :
    extendFiniteBoundaryL s t R (harmonicBoundaryFiniteL s f) = R f := by
  unfold extendFiniteBoundaryL
  exact LinearMap.extendOfNorm_eq (denseRange_harmonicBoundaryFiniteL s) ⟨B,hR⟩ f

private theorem norm_extendFiniteBoundaryL_le (s t : ℝ)
    (R : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim t) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ f, ‖R f‖ ≤ B*‖harmonicBoundaryFiniteL s f‖) :
    ‖extendFiniteBoundaryL s t R‖ ≤ B := by
  unfold extendFiniteBoundaryL
  exact LinearMap.opNorm_extendOfNorm_le (denseRange_harmonicBoundaryFiniteL s) hB hR

theorem norm_finiteSphere_midpoint_le
    (R0 : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim (-1/2 : ℝ))
    (R : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim 0)
    (R1 : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim (1/2 : ℝ))
    (hR0 : ∀ f, sphereSobolevInclusionL 0 (-1/2 : ℝ) (by norm_num) (R f) = R0 f)
    (hR1 : ∀ f, sphereSobolevInclusionL (1/2 : ℝ) (-1/2 : ℝ) (by norm_num) (R1 f) = R0 f)
    (M0 M1 : ℝ) (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1)
    (h0 : ∀ f, ‖R0 f‖ ≤ M0*‖harmonicBoundaryFiniteL (1/2 : ℝ) f‖)
    (h1 : ∀ f, ‖R1 f‖ ≤ M1*‖harmonicBoundaryFiniteL (3/2 : ℝ) f‖)
    (f : HarmonicFiniteCoefficients dim) :
    ‖R f‖ ≤ ((M0+M1)/2)*‖harmonicBoundaryFiniteL 1 f‖ := by
  let T0 := extendFiniteBoundaryL (1/2 : ℝ) (-1/2 : ℝ) R0
  let T1 := extendFiniteBoundaryL (3/2 : ℝ) (1/2 : ℝ) R1
  let J := sphereSobolevInclusionL (dim := dim) (1/2 : ℝ) (-1/2 : ℝ) (by norm_num)
  let K := sphereSobolevInclusionL (dim := dim) (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  have hT0 := norm_extendFiniteBoundaryL_le (1/2 : ℝ) (-1/2 : ℝ) R0 M0 hM0 h0
  have hT1 := norm_extendFiniteBoundaryL_le (3/2 : ℝ) (1/2 : ℝ) R1 M1 hM1 h1
  have hCompat : J.comp T1 = T0.comp K := by
    apply ContinuousLinearMap.ext
    intro x
    refine (denseRange_harmonicBoundaryFiniteL (dim := dim) (3/2 : ℝ)).induction_on x
      (isClosed_eq (J.continuous.comp T1.continuous) (T0.continuous.comp K.continuous)) ?_
    intro a
    change J (T1 (harmonicBoundaryFiniteL (3/2 : ℝ) a)) =
      T0 (K (harmonicBoundaryFiniteL (3/2 : ℝ) a))
    rw [show T1 (harmonicBoundaryFiniteL (3/2 : ℝ) a) = R1 a from
        extendFiniteBoundaryL_apply (3/2 : ℝ) (1/2 : ℝ) R1 M1 h1 a,
      show K (harmonicBoundaryFiniteL (3/2 : ℝ) a) = harmonicBoundaryFiniteL (1/2 : ℝ) a from
        sphereSobolevInclusionL_harmonicBoundaryFiniteL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) a,
      show T0 (harmonicBoundaryFiniteL (1/2 : ℝ) a) = R0 a from
        extendFiniteBoundaryL_apply (1/2 : ℝ) (-1/2 : ℝ) R0 M0 h0 a]
    exact hR1 a
  let u := harmonicBoundaryFiniteL (dim := dim) 1 f
  have hT : T0 (sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) u) = R0 f := by
    rw [show sphereSobolevInclusionL 1 (1/2 : ℝ) (by norm_num) u = harmonicBoundaryFiniteL (1/2 : ℝ) f from
      sphereSobolevInclusionL_harmonicBoundaryFiniteL 1 (1/2 : ℝ) (by norm_num) f]
    exact extendFiniteBoundaryL_apply (1/2 : ℝ) (-1/2 : ℝ) R0 M0 h0 f
  have hCoef (k : ℕ) : sphereSobolevCoefficientL (-1/2 : ℝ) k (R0 f) = R f k := by
    rw [← hR0 f,sphereSobolevCoefficientL_inclusion,sphereSobolevCoefficientL_apply]
    simp only [besselWeight,neg_zero,Real.rpow_zero,one_smul]
  have hSq : ‖R f‖^2 ≤ ((M0+M1)/2)^2*‖u‖^2 := by
    have hLim := (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (R f)).tendsto_sum_nat
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hLim
    apply le_of_tendsto_of_tendsto' hLim tendsto_const_nhds
    intro k
    have h := sphereSobolev_midpoint_finite_bound T0 T1 hCompat M0 M1 hM0 hM1 hT0 hT1 u
      (harmonicBoundaryFiniteL_mem_finiteSupport 1 f) (Finset.range k)
    simpa only [hT,hCoef] using h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hSq.trans_eq (by rw [mul_pow]))

end CalderonN
