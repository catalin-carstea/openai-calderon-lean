module

public import Proof.CalderonN.NativeWeakHarmonicResponse
public import Proof.CalderonN.SharpBallValueTrace

import Mathlib.Tactic

/-! Smooth boundary data in the weighted Hilbert sum. Finite harmonic
testing recovers exactly the negative half-order norm. -/

public section

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal ContDiff InnerProductSpace Classical Topology DirectSum
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic

variable {dim : ℕ} [NeZero dim]

def smoothBoundarySobolev (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) (u : SmoothData dim) :
    SphereSobolev dim s :=
  sphereHarmonicDecomposition (ambientBesselField hn s hs
    (u.1 ∘ Prod.snd) (u.2.comp contDiff_snd) 0)

theorem smoothBoundarySobolev_apply (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (u : SmoothData dim) (k : ℕ) :
    smoothBoundarySobolev hn s hs u k =
      besselWeight s k • harmonicProjection k (smoothSphereLift u.1 u.2) := by
  unfold smoothBoundarySobolev
  rw [sphereHarmonicDecomposition_apply,ambientBesselField_projection,ambientSphereL2_eq_smoothSphereLift]
  rfl

theorem inner_smoothBoundarySobolev_dual (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2) (hns : -s ≤ 2)
    (u v : SmoothData dim) :
    ⟪smoothBoundarySobolev hn (-s) hns u,smoothBoundarySobolev hn s hs v⟫_ℝ =
      ∫ w : ↥(standardSphere dim), u.1 w*v.1 w ∂(sphereProbability dim) := by
  have hW (k : ℕ) : besselWeight (-s) k*besselWeight s k = 1 := by
    simpa only [besselWeight,neg_add_cancel,Real.rpow_zero] using
      (Real.rpow_add (by positivity : 0 < 1+(k : ℝ)) (-s) s).symm
  change _ = ∫ w : UnitSphere dim, u.1 w.val*v.1 w.val ∂(unitSphereProbability dim)
  rw [← smoothSphereLift_inner _ _ u.2 v.2,← sphereHarmonicDecomposition.inner_map_map (smoothSphereLift u.1 u.2)
    (smoothSphereLift v.1 v.2),lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  rw [smoothBoundarySobolev_apply,smoothBoundarySobolev_apply,
    sphereHarmonicDecomposition_apply,sphereHarmonicDecomposition_apply,
    real_inner_smul_left,real_inner_smul_right,← mul_assoc,hW,one_mul]

theorem abs_integral_mul_le_smoothBoundarySobolev (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (hns : -s ≤ 2) (u v : SmoothData dim) :
    |∫ w : ↥(standardSphere dim), u.1 w*v.1 w ∂(sphereProbability dim)| ≤
      ‖smoothBoundarySobolev hn (-s) hns u‖*‖smoothBoundarySobolev hn s hs v‖ := by
  rw [← inner_smoothBoundarySobolev_dual hn s hs hns]
  exact abs_real_inner_le_norm _ _

variable [Nontrivial (Fin dim)]

omit [Nontrivial (Fin dim)] in
theorem smoothSphereLift_harmonicFiniteSmooth (g : HarmonicFiniteCoefficients dim) :
    smoothSphereLift (harmonicFiniteSmooth g).1 (harmonicFiniteSmooth g).2 =
      ∑ k ∈ g.support, (g k : SphereL2 dim) := by
  unfold harmonicFiniteSmooth
  rw [smoothSphereLift_polynomialEvaluation]
  unfold harmonicFinitePolynomial
  simp only [map_sum,polynomialSphereL2_harmonicPolynomialRepresentative]

omit [Nontrivial (Fin dim)] in
theorem smoothBoundarySobolev_harmonicFiniteSmooth (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (g : HarmonicFiniteCoefficients dim) :
    smoothBoundarySobolev hn s hs (harmonicFiniteSmooth g) = harmonicBoundaryFiniteL s g := by
  apply lp.ext
  funext k
  rw [smoothBoundarySobolev_apply,smoothSphereLift_harmonicFiniteSmooth,
    ← sphereHarmonicDecomposition_apply,map_sum,harmonicBoundaryFiniteL_eq_sum]
  simp only [sphereHarmonicDecomposition_subtype,sphereSobolevSingleL,smul_apply,
    lp.singleContinuousLinearMap_apply,lp.coeFn_sum,Finset.sum_apply,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change besselWeight s k • (lp.single (E := fun j => harmonicSphereSubspace dim j) 2 i (g i)) k =
    (besselWeight s i • lp.single (E := fun j => harmonicSphereSubspace dim j) 2 i (g i)) k
  by_cases h : k = i
  · subst h
    simp only [lp.coeFn_smul,Pi.smul_apply]
  · rw [lp.coeFn_smul,Pi.smul_apply,lp.single_apply_ne (E := fun j : ℕ => harmonicSphereSubspace dim j) 2 i (g i) h,smul_zero,smul_zero]

/-- Uniform finite harmonic testing is sufficient for the actual
negative-order norm of a smooth boundary response. -/
theorem norm_smoothBoundarySobolev_le_of_finite_tests (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    (hns : -s ≤ 2) (u : SmoothData dim) (B : ℝ) (hB : 0 ≤ B)
    (hTest : ∀ g : HarmonicFiniteCoefficients dim,
      |∫ w : ↥(standardSphere dim), u.1 w*(harmonicFiniteSmooth g).1 w ∂(sphereProbability dim)| ≤
        B*‖harmonicBoundaryFiniteL s g‖) :
    ‖smoothBoundarySobolev hn (-s) hns u‖ ≤ B := by
  let U := smoothBoundarySobolev hn (-s) hns u
  have hAll (v : SphereSobolev dim s) : |⟪U,v⟫_ℝ| ≤ B*‖v‖ := by
    refine (denseRange_harmonicBoundaryFiniteL (dim := dim) s).induction_on v ?_ ?_
    · exact isClosed_le ((innerSL ℝ U).continuous.abs) (continuous_norm.const_mul B)
    · intro g
      rw [← smoothBoundarySobolev_harmonicFiniteSmooth hn s hs g,show U = smoothBoundarySobolev hn (-s) hns u from rfl,
        inner_smoothBoundarySobolev_dual hn s hs hns]
      simpa only [smoothBoundarySobolev_harmonicFiniteSmooth hn s hs g] using hTest g
  by_cases h : U = 0
  · change ‖U‖ ≤ B
    rwa [h,norm_zero]
  have hU := hAll U
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _),pow_two] at hU
  exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr h)).mp hU

/-- The sharp trace estimate uses just first-order bulk energy. -/
theorem sq_smoothBoundarySobolev_half_le (hn : 3 ≤ dim) (u : SmoothData dim) :
    unitSphereArea dim * ‖smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u‖ ^ 2 ≤
      ((dim : ℝ)+3)*‖smoothSobolev u‖ ^ 2 := by
  let U := smoothBoundarySobolev hn (1/2 : ℝ) (by norm_num) u
  have hT := (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) U).tendsto_sum_nat
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hT
  have h' := hT.const_mul (unitSphereArea dim)
  apply le_of_tendsto_of_tendsto' h' tendsto_const_nhds
  intro k
  simp only [U,smoothBoundarySobolev_apply,norm_smul,Real.norm_eq_abs,
    abs_of_pos (besselWeight_pos _ _),mul_pow,besselWeight_one_half_sq]
  exact sum_sharpBallValueTrace_le u (Finset.range k)

end CalderonN
