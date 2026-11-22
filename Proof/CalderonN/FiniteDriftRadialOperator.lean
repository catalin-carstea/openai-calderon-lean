module

public import Proof.CalderonN.FiniteFlatRadialOperator

import Mathlib.Tactic

/-! The radial trace of the model drift correction is the released
bounded degree-lowering operator on the actual Hilbert sphere. -/

public section

noncomputable section
open Set Metric MvPolynomial
open scoped ContDiff DirectSum InnerProductSpace Classical
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace
variable {dim : ℕ} [NeZero dim]

private theorem harmonicProjection_subtype_diag {m : ℕ} (v : harmonicSphereSubspace dim m) :
    harmonicProjection m (v : SphereL2 dim) = v := by
  rw [← sphereHarmonicDecomposition_apply,sphereHarmonicDecomposition_subtype,lp.single_apply_self]

private theorem harmonicProjection_subtype_off {m k : ℕ} (h : m ≠ k)
    (v : harmonicSphereSubspace dim k) :
    harmonicProjection m (v : SphereL2 dim) = 0 := by
  rw [← sphereHarmonicDecomposition_apply,sphereHarmonicDecomposition_subtype,
    lp.single_apply_ne _ _ _ h]

private theorem harmonicProjection_extensional {u v : SphereL2 dim}
    (h : ∀ k, harmonicProjection k u = harmonicProjection k v) : u = v := by
  apply sphereHarmonicDecomposition.injective
  apply lp.ext
  funext k
  simpa only [sphereHarmonicDecomposition_apply] using h k

private theorem radialDriftOperator_degree_zero (b : X dim) (v : harmonicSphereSubspace dim 0) :
    radialDriftOperator b (v : SphereL2 dim) = 0 := by
  apply harmonicProjection_extensional
  intro k
  rw [radialDriftOperator_projection,harmonicProjection_subtype_off (by omega)]
  simp

private theorem radialDriftOperator_degree_succ (b : X dim) (m : ℕ)
    (p : harmonicHomogeneous dim (m+1)) :
    radialDriftOperator b (polynomialSphereL2 p.1) =
      polynomialSphereL2 (C (-(2*(m:ℝ)+(dim:ℝ))⁻¹) * driftDerivative (fun i => b i) p.1) := by
  let c : ℝ := -(2*(m:ℝ)+(dim:ℝ))⁻¹
  let a : harmonicSphereSubspace dim (m+1) := harmonicPolynomialSphereMap (m+1) p
  let q := C c * driftDerivative (fun i => b i) p.1
  have hq : q ∈ harmonicHomogeneous dim m := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.add_sub_cancel,q] using (driftDerivative_isHomogeneous p.2.1 (fun i => b i)).C_mul c
    · rw [show q = C c*driftDerivative (fun i => b i) p.1 from rfl,laplacian_C_mul,
        laplacian_driftDerivative _ _ p.2.2,mul_zero]
  let v : harmonicSphereSubspace dim m := ⟨polynomialSphereL2 q,polynomialSphereL2_mem m q hq⟩
  change radialDriftOperator b (a : SphereL2 dim) = (v : SphereL2 dim)
  apply harmonicProjection_extensional
  intro k
  by_cases hkm : k = m
  · subst k
    rw [radialDriftOperator_projection,harmonicProjection_subtype_diag,harmonicProjection_subtype_diag]
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul]
    change (∑ i, (c*b i) • ((harmonicDerivative (sphereFischerInner dim) m i a :
        harmonicSphereSubspace dim m) : SphereL2 dim)) = polynomialSphereL2 q
    have he (i : Fin dim) : ((harmonicDerivative (sphereFischerInner dim) m i a :
        harmonicSphereSubspace dim m) : SphereL2 dim) = polynomialSphereL2 (pderiv i p.1) := by
      rw [show a = harmonicPolynomialSphereMap (m+1) p from rfl,harmonicDerivative_apply_image]
      rfl
    simp only [he,q,driftDerivative,Finset.mul_sum,map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc,← map_mul,← smul_eq_C_mul,map_smul]
  · rw [radialDriftOperator_projection,harmonicProjection_subtype_off (by omega),
      harmonicProjection_subtype_off hkm]
    simp

@[expose] def driftCoordinates (ell : X dim →L[ℝ] ℝ) : X dim :=
  WithLp.toLp 2 (fun i => ell (axis i))

theorem smoothSphereLift_finite_drift_radial (hn : 3 ≤ dim) (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) :
    let q := smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ell f)
    smoothSphereLift q.1 q.2 =
      radialDriftOperator (driftCoordinates ell)
        (smoothSphereLift (harmonicFiniteSmooth f).1 (harmonicFiniteSmooth f).2) := by
  let S := smoothBoundaryLiftL (dim:=dim) hn
  let R := radialDriftOperator (driftCoordinates ell)
  have hEq : S.comp (smoothBallRadialDataL.comp (harmonicFiniteDriftVariationSmoothL ell)) =
      R.toLinearMap.comp (S.comp (harmonicFiniteSmoothL (dim:=dim))) := by
    ext k u : 2
    simp only [LinearMap.comp_apply]
    let b := driftCoordinates ell
    let p : harmonicHomogeneous dim k :=
      ⟨harmonicPolynomialRepresentativeL k u,harmonicPolynomialRepresentative_mem k u⟩
    let q := driftFirstVariation k (fun i => ell (axis i)) p.1
    rw [show S = smoothBoundaryLiftL hn from rfl,smoothBoundaryLiftL_apply,smoothBoundaryLiftL_apply]
    have hInput :
        smoothSphereLift (harmonicFiniteSmoothL
          (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k u)).1
          (smoothBallData_contDiff _) = polynomialSphereL2 p.1 := by
      rw [← smoothSphereLift_polynomialEvaluation p.1]
      apply smoothSphereLift_eq_of_eqOn ⟨_,_⟩
        ⟨polynomialEvaluation p.1,contDiff_polynomialEvaluation p.1⟩
      intro z _
      exact congrFun (harmonicFiniteSmoothL_lof k u) z
    have hOut :
        (smoothBallRadialDataL (harmonicFiniteDriftVariationSmoothL ell
          (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k u))).1 =
          fun z => fderiv ℝ (polynomialEvaluation q) z z := by
      rw [smoothBallRadialDataL_val,harmonicFiniteDriftVariationSmoothL_lof]
    rw [ContinuousLinearMap.coe_coe,hInput]
    let W := smoothBallRadialDataL (harmonicFiniteDriftVariationSmoothL ell
      (DirectSum.lof ℝ ℕ (fun l => ↥(harmonicSphereSubspace dim l)) k u))
    let D : SmoothData dim := ⟨W.1,smoothBallData_contDiff W⟩
    have hD : D.1 = fun z => fderiv ℝ (polynomialEvaluation q) z z := hOut
    change smoothSphereLift D.1 D.2 = _
    cases k with
    | zero =>
        have hp := eq_C_of_mem_harmonicHomogeneous_zero p.2
        have hz : q = 0 := by dsimp only [q]; rw [hp,driftFirstVariation_C]
        have h₀ : polynomialSphereL2 p.1 = ((harmonicPolynomialSphereMap 0 p) : SphereL2 dim) := rfl
        rw [h₀,show R = radialDriftOperator b from rfl,radialDriftOperator_degree_zero]
        rw [← map_zero (polynomialSphereL2 (n:=dim)), ← smoothSphereLift_polynomialEvaluation]
        apply smoothSphereLift_eq_of_eqOn D
          ⟨polynomialEvaluation 0,contDiff_polynomialEvaluation 0⟩
        intro z _
        change D.1 z = polynomialEvaluation 0 z
        rw [congrFun hD,hz]
        have hZero : polynomialEvaluation (0 : MvPolynomial (Fin dim) ℝ) = 0 := by
          funext x
          simp [polynomialEvaluation]
        simp [hZero]
    | succ m =>
        rw [show R = radialDriftOperator b from rfl,radialDriftOperator_degree_succ b m p,
          ← smoothSphereLift_polynomialEvaluation]
        let p' := C (-(2*(m:ℝ)+(dim:ℝ))⁻¹) * driftDerivative (fun i => b i) p.1
        apply smoothSphereLift_eq_of_eqOn D
          ⟨polynomialEvaluation p',contDiff_polynomialEvaluation p'⟩
        intro z hz
        change D.1 z = polynomialEvaluation p' z
        rw [congrFun hD]
        change fderiv ℝ (polynomialEvaluation q) z z = _
        change fderiv ℝ (polynomialEvaluation (driftFirstVariation (m+1) (fun i => b i) p.1)) z z = _
        rw [euclidean_radial_driftFirstVariation m b z p.1 (mem_sphere_zero_iff_norm.mp hz),
          fderiv_polynomialEvaluation_apply]
        simp only [p',polynomialEvaluation,driftDerivative,map_mul,map_sum,eval_C]
  have hF := congrArg (fun L : HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereL2 dim => L f) hEq
  simpa only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe,S,R,smoothBoundaryLiftL_apply,
    smoothBallRadialDerivative,smoothBallRadialDataL_val,harmonicFiniteDriftVariationSmoothL_val,harmonicFiniteSmoothL_val] using hF

theorem radialDriftOperator_coordinates_norm_le (ell : X dim →L[ℝ] ℝ) :
    ‖radialDriftOperator (driftCoordinates ell)‖ ≤
      (∑ i : Fin dim, ‖radialDriftOperator (axis i)‖)*‖ell‖ := by
  have hF : radialDriftOperator (driftCoordinates ell) =
      ∑ i, ell (axis i) • radialDriftOperator (axis i) := by
    ext u : 1
    apply harmonicProjection_extensional
    intro m
    rw [radialDriftOperator_projection]
    simp only [ContinuousLinearMap.sum_apply,smul_apply,map_sum,map_smul,
      radialDriftOperator_projection,axis,PiLp.single_apply,Finset.smul_sum,smul_smul,
      mul_ite,mul_zero,mul_one,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl,smul_smul]
      congr 1
      change -(2*(m:ℝ)+(dim:ℝ))⁻¹*ell (axis i) =
        ell (axis i)*(-(2*(m:ℝ)+(dim:ℝ))⁻¹)
      ring
    · intro j _ hij
      simp [hij]
    · simp
  rw [hF,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul,Real.norm_eq_abs,mul_comm |ell (axis i)|]
  have hi : |ell (axis i)| ≤ ‖ell‖ := by simpa [Real.norm_eq_abs,axis] using ell.le_opNorm (axis i)
  exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)

theorem norm_first_finite_radial_zero_le (hn : 3 ≤ dim) (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) :
    ‖smoothBoundarySobolev hn 0 (by norm_num)
      (smoothBallRadialDerivative (harmonicFiniteDriftVariationSmooth ell f))‖ ≤
      ((∑ i : Fin dim, ‖radialDriftOperator (axis i)‖)*‖ell‖)*‖harmonicBoundaryFiniteL 1 f‖ := by
  let u := harmonicFiniteSmooth f
  have hU : ‖smoothSphereLift u.1 u.2‖ ≤ ‖harmonicBoundaryFiniteL 1 f‖ := by
    rw [← norm_smoothBoundarySobolev_zero_eq hn u,smoothBoundarySobolev_harmonicFiniteSmooth]
    exact norm_harmonicBoundaryFiniteL_zero_le_one f
  rw [norm_smoothBoundarySobolev_zero_eq,smoothSphereLift_finite_drift_radial hn]
  exact ((radialDriftOperator (driftCoordinates ell)).le_opNorm _).trans
    (mul_le_mul (radialDriftOperator_coordinates_norm_le ell) hU (norm_nonneg _) (by positivity))

end CalderonN
