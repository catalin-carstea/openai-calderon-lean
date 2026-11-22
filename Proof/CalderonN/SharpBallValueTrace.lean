module

public import Proof.CalderonN.SharpBallTraceEnergy

import Mathlib.Tactic

/-! The constant mode in the sharp trace estimate. The (L^2) endpoint
uses the fixed-ball divergence theorem on the density (u^2 x). -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Gradient InnerProductSpace
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem sq_smoothSphereLift_le_BallH1 (u : SmoothData dim) :
    unitSphereArea dim * ‖smoothSphereLift u.1 u.2‖^2 ≤
      ((dim : ℝ)+2)*‖smoothSobolev u‖^2 := by
  let U := smoothSobolev u
  let W : X dim → X dim := fun x => (u.1 x)^2 • x
  have hW : ContDiff ℝ ∞ W := (u.2.pow 2).smul contDiff_id
  have hD (x : X dim) :
      coordinateFluxDivergence W x = (dim : ℝ)*u.1 x^2+2*u.1 x*(fderiv ℝ u.1 x x) := by
    have hF : HasFDerivAt W
        ((u.1 x)^2 • ContinuousLinearMap.id ℝ (X dim) +
          ((2*u.1 x) • fderiv ℝ u.1 x).smulRight x) x := by
      have hU := ((u.2.differentiable (by simp) x).hasFDerivAt.pow 2).smul (hasFDerivAt_id x)
      change HasFDerivAt W _ x at hU
      simpa only [id_eq, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat] using hU
    have hSum (i : Fin dim) : coordDeriv i (fun z => W z i) x =
        (u.1 x)^2 + 2*u.1 x*(x i * fderiv ℝ u.1 x (axis i)) := by
      change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ W) x (axis i) = _
      rw [((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hF).fderiv]
      simp [axis, mul_comm, mul_left_comm, mul_assoc]
    unfold coordinateFluxDivergence
    simp_rw [hSum]
    have hX : ∑ i : Fin dim, x i * fderiv ℝ u.1 x (axis i) = fderiv ℝ u.1 x x := by
      rw [← congrArg (fderiv ℝ u.1 x) (vector_eq_sum_axis x)]
      simp only [map_sum,map_smul,smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hX, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hPoint (x : X dim) (hx : x ∈ ball (0 : X dim) 1) :
      coordinateFluxDivergence W x ≤ ((dim : ℝ)+1)*u.1 x^2+‖gradient u.1 x‖^2 := by
    rw [hD]
    have hB : ‖fderiv ℝ u.1 x x‖ ≤ ‖gradient u.1 x‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map]
      refine ((fderiv ℝ u.1 x).le_opNorm x).trans ?_
      exact mul_le_of_le_one_right (norm_nonneg _) ((mem_ball_zero_iff.mp hx).le)
    have hSq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hB
    rw [Real.norm_eq_abs, sq_abs] at hSq
    nlinarith only [hSq, sq_nonneg (u.1 x - fderiv ℝ u.1 x x)]
  have hBdy : unitSphereFlux W = unitSphereArea dim * ‖smoothSphereLift u.1 u.2‖^2 := by
    rw [← real_inner_self_eq_norm_sq, smoothSphereLift_inner, ← integral_const_mul]
    change _ = ∫ w : ↥(standardSphere dim),
      unitSphereArea dim * (u.1 w*u.1 w) ∂(sphereProbability dim)
    rw [integral_unitSphereArea_mul_probability (fun w : ↥(standardSphere dim) => u.1 w*u.1 w)]
    unfold unitSphereFlux
    apply integral_congr_ae
    filter_upwards with w
    change ⟪(w : X dim), (u.1 w)^2 • (w : X dim)⟫_ℝ = _
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp w.property]
    ring
  rw [← hBdy, ← integral_unitBall_coordinateFluxDivergence W hW]
  have hV : (∫ x in ball (0 : X dim) 1, u.1 x^2) = ‖TauCeti.W1p.value U‖^2 := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [value_smoothSobolev_ae u] with x hx
    change u.1 x^2 = ⟪(TauCeti.W1p.value U) x,(TauCeti.W1p.value U) x⟫_ℝ
    rw [show (TauCeti.W1p.value U) x = u.1 x from hx,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  have hG : (∫ x in ball (0 : X dim) 1, ‖gradient u.1 x‖^2) = ‖TauCeti.W1p.gradient U‖^2 := by
    rw [← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae u] with x hx
    rw [show (TauCeti.W1p.gradient U) x = gradient u.1 x from hx]
  have hV' : Continuous (fun x => u.1 x^2) := u.2.continuous.pow 2
  have hG' : Continuous (fun x => ‖gradient u.1 x‖^2) := by
    simp only [gradient,LinearIsometryEquiv.norm_map]
    exact (u.2.continuous_fderiv (by simp)).norm.pow 2
  let B := ball (0 : X dim) 1
  let C := closedBall (0 : X dim) 1
  have hi (f : X dim → ℝ) (hf : Continuous f) : IntegrableOn f B :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set
      (show B ⊆ C from ball_subset_closedBall)
  have hvI := hi _ hV'
  have hgI := hi _ hG'
  have hD' : ContinuousOn (coordinateFluxDivergence W) C := by
    rw [funext hD]
    exact ((hV'.const_mul _).add
      ((u.2.continuous.const_mul _).mul
        ((u.2.continuous_fderiv (by simp)).clm_apply continuous_id))).continuousOn
  have hDI : IntegrableOn (coordinateFluxDivergence W) B :=
    (hD'.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall
  refine (setIntegral_mono_on hDI ((hvI.const_mul _).add hgI) measurableSet_ball hPoint).trans ?_
  change (∫ x in B, ((dim : ℝ)+1)*u.1 x^2+‖gradient u.1 x‖^2) ≤ _
  rw [integral_add (hvI.const_mul _) hgI, integral_const_mul]
  change ((dim : ℝ)+1)*(∫ x in ball (0 : X dim) 1, u.1 x^2)+
    (∫ x in ball (0 : X dim) 1, ‖gradient u.1 x‖^2) ≤ _
  rw [hV,hG]
  have hv := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (TauCeti.W1p.norm_value_le U)
  have hg := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (TauCeti.W1p.norm_gradient_le U)
  calc
    _ ≤ ((dim : ℝ)+1)*‖U‖^2+‖U‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hv (by positivity)) hg
    _ = _ := by ring

/-- Inhomogeneous half-order trace on smooth data, uniform in the
finite set of degrees used by the angular energy. -/
theorem sum_sharpBallValueTrace_le (u : SmoothData dim) (s : Finset ℕ) :
    unitSphereArea dim * ∑ k ∈ s, (1+(k : ℝ))*
      ‖harmonicProjection k (smoothSphereLift u.1 u.2)‖^2 ≤
      ((dim : ℝ)+3)*‖smoothSobolev u‖^2 := by
  let v := smoothSphereLift u.1 u.2
  let U := smoothSobolev u
  have hBessel : (∑ k ∈ s, ‖harmonicProjection k v‖^2) ≤ ‖v‖^2 := by
    have h := lp.sum_rpow_le_norm_rpow (show 0 < (2 : ℝ≥0∞).toReal by norm_num)
      (sphereHarmonicDecomposition v) s
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, sphereHarmonicDecomposition_apply,
      LinearIsometryEquiv.norm_map] using h
  have h0 := (mul_le_mul_of_nonneg_left hBessel (unitSphereArea_pos (dim := dim)).le).trans
    (sq_smoothSphereLift_le_BallH1 u)
  have h1 := (sum_halfTrace_energy_le u s).trans
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (TauCeti.W1p.norm_gradient_le U))
  simp only [add_mul, one_mul, Finset.sum_add_distrib,mul_add]
  exact (add_le_add h0 h1).trans_eq (by ring)

end CalderonN
