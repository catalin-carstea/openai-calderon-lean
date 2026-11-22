module

public import Proof.CalderonN.NativeWeakHarmonicResponse
public import Proof.CalderonN.PolynomialPoissonFirstVariation
import Proof.CalderonN.ChartBilinear

import Mathlib.Tactic

/-! Identification of the affine energy coefficient with the classical
first conormal derivative, using the released solid-harmonic variation. -/

public section

noncomputable section
open Set Metric MeasureTheory MvPolynomial
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Classical DirectSum
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon AngularPolynomial SphereHarmonic GreenRadialTrace

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem gradient_coordDeriv (v : X dim → ℝ) (z : X dim) (i : Fin dim) :
    gradient v z i = coordDeriv i v z := by
  rw [coordDeriv,← inner_gradient_left (𝕜 := ℝ)]
  simp only [axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem smoothBallFlux_scalar_apply (a : X dim → ℝ) (u : X dim → ℝ) (z : X dim) (i : Fin dim) :
    smoothBallFlux (fun x => a x • (1 : Mat dim)) u z i = a z*coordDeriv i u z := by
  classical
  rw [smoothBallFlux_apply]
  simp [Matrix.one_apply,apply_ite,ite_mul]

omit [NeZero dim] [Nontrivial (Fin dim)] in
/-- Contract the scalar multiple of the flat flux in the actual Euclidean
normal direction, with no tangential correction. -/
theorem inner_smoothBallFlux_scalar (a : X dim → ℝ) (u : X dim → ℝ) (z : X dim) :
    ⟪z,smoothBallFlux (fun x => a x • (1 : Mat dim)) u z⟫_ℝ =
      a z * fderiv ℝ u z z := by
  rw [covector_axis_sum (fderiv ℝ u z) z]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,dotProduct,
    smoothBallFlux_scalar_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordDeriv]
  ring

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem energyFormH1_one_eq_gradient_inner (u v : FixedBallH1 dim) :
    energyFormH1 (fun _ => (1 : Mat dim)) 0 0 u v =
      ⟪W1p.gradient u,W1p.gradient v⟫_ℝ := by
  rw [energyFormH1_const_eq_setIntegral,L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  simp only [matrixBilinearForm_apply,Matrix.one_mulVec]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]

private theorem energyFormH1_flat_eq_zero_of_finite_test (q : SmoothData dim)
    (g : HarmonicFiniteCoefficients dim) (hq : EqOn q.1 0 (standardSphere dim)) :
    energyFormH1 (fun _ => (1 : Mat dim)) 0 0 (smoothSobolev q)
      (smoothSobolev (harmonicFiniteSmooth g)) = 0 := by
  have hSphere : smoothSphereLift q.1 q.2 = 0 := by
    unfold smoothSphereLift
    rw [show smoothSphereRestriction q.1 q.2 = 0 by
      apply ContinuousMap.ext
      intro z
      exact hq z.2]
    exact map_zero _
  have hV : smoothSobolev (harmonicFiniteSmooth g) =
      polynomialBallH1L dim (∑ k ∈ g.support, harmonicPolynomialRepresentativeL k (g k)) := by
    rw [polynomialBallH1L_apply]
    unfold harmonicFiniteSmooth harmonicFinitePolynomial
    rfl
  rw [energyFormH1_one_eq_gradient_inner,hV,map_sum]
  simp only [← W1p.gradientL_apply,map_sum,inner_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [W1p.gradientL_apply, W1p.gradientL_apply, polynomialBallH1L_apply,
    inner_nativeGradient_harmonicPolynomial q k _ (harmonicPolynomialRepresentative_mem k (g k)),
    hSphere,inner_zero_left,mul_zero]

/-- For a harmonic test, the weak affine energy agrees with the classical
differentiated conormal flux of a smooth flat first variation. -/
theorem affineEnergy_eq_firstConormal_of_firstVariation (ell : X dim →L[ℝ] ℝ)
    (u q : SmoothData dim) (g : HarmonicFiniteCoefficients dim)
    (hq : EqOn q.1 0 (standardSphere dim))
    (hEq : ∀ z ∈ ball (0 : X dim) 1,
      negativeBallDivergence (fun _ => (1 : Mat dim)) q.1 z +
        negativeBallDivergence (fun x => ell x • (1 : Mat dim)) u.1 z = 0) :
    energyFormH1 (fun z => ell z • (1 : Mat dim)) 0 0 (smoothSobolev u)
      (smoothSobolev (harmonicFiniteSmooth g)) =
      unitSphereArea dim * ∫ w : ↥(standardSphere dim),
        (harmonicFiniteSmooth g).1 w *
          (ell w*fderiv ℝ u.1 w w+fderiv ℝ q.1 w w) ∂(sphereProbability dim) := by
  let v := harmonicFiniteSmooth g
  let A (x : X dim) : Mat dim := ell x • 1
  let J := smoothBallFlux A u.1
  let Q := smoothBallFlux (fun _ => (1 : Mat dim)) q.1
  let F (x : X dim) := J x+Q x
  have hJ : ContDiff ℝ ∞ J := contDiff_smoothBallFlux (ell.contDiff.smul contDiff_const) u
  have hQ : ContDiff ℝ ∞ Q := contDiff_smoothBallFlux contDiff_const q
  have hF : ContDiff ℝ ∞ F := hJ.add hQ
  have hD : EqOn (coordinateFluxDivergence F) 0 (ball (0 : X dim) 1) := by
    intro x hx
    have h (i : Fin dim) : coordDeriv i (fun z => F z i) x =
        coordDeriv i (fun z => J z i) x + coordDeriv i (fun z => Q z i) x := by
      change coordDeriv i (fun z => J z i + Q z i) x = _
      exact Elliptic.pd_add ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hJ)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hQ) x
    change (∑ i, coordDeriv i (fun z => F z i) x) = 0
    simp_rw [h]
    rw [Finset.sum_add_distrib]
    change coordinateFluxDivergence J x+coordinateFluxDivergence Q x = 0
    rw [coordinateFluxDivergence_smoothBallFlux,coordinateFluxDivergence_smoothBallFlux]
    linarith only [hEq x hx]
  have hSum (G : X dim → X dim) (hG : ContDiff ℝ ∞ G) :
      Integrable (fun x => ∑ i, gradient v.1 x i * G x i)
        ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := by
    have h : Continuous (fun x => ∑ i, gradient v.1 x i * G x i) := by
      apply continuous_finsetSum
      intro i _
      rw [show (fun x => gradient v.1 x i * G x i) = fun x => coordDeriv i v.1 x * G x i from by
        funext x; rw [gradient_coordDeriv]]
      exact ((Elliptic.contDiff_pd v.2).continuous).mul
        ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hG.continuous)
    exact (h.continuousOn.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall
  have hBulk (a : X dim → Mat dim) (b : SmoothData dim) :
      energyFormH1 a 0 0 (smoothSobolev b) (smoothSobolev v) =
        ∫ x in fixedBallOpens dim, ∑ i, gradient v.1 x i*smoothBallFlux a b.1 x i := by
    rw [energyFormH1_smooth_left]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae v] with x hx
    rw [hx]
  have h := integral_smoothFlux_gradient_eq_boundary F hF v hD
  have hSplit (x : X dim) : (∑ i, gradient v.1 x i * F x i) =
      (∑ i, gradient v.1 x i * J x i)+(∑ i, gradient v.1 x i * Q x i) := by
    simp only [F,PiLp.add_apply,mul_add,Finset.sum_add_distrib]
  simp_rw [hSplit] at h
  rw [integral_add (hSum J hJ) (hSum Q hQ),← hBulk A u,← hBulk (fun _ => (1 : Mat dim)) q,
    energyFormH1_flat_eq_zero_of_finite_test q g hq,add_zero] at h
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  have h1 : ⟪(w : X dim), J w⟫_ℝ = ell w*fderiv ℝ u.1 w w :=
    inner_smoothBallFlux_scalar ell u.1 w
  have h2 : ⟪(w : X dim), Q w⟫_ℝ = fderiv ℝ q.1 w w := by
    simpa only [one_smul,one_mul] using inner_smoothBallFlux_scalar (fun _ => 1) q.1 (w : X dim)
  rw [show ⟪(w : X dim), F w⟫_ℝ = ⟪(w : X dim),J w⟫_ℝ+⟪(w : X dim),Q w⟫_ℝ from inner_add_right _ _ _,h1,h2]

@[expose] def harmonicFiniteDriftVariationSmooth (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) : SmoothData dim :=
  let q := ∑ k ∈ f.support,
    driftFirstVariation k (fun i => ell (axis i)) (harmonicPolynomialRepresentativeL k (f k))
  ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩

omit [Nontrivial (Fin dim)] in
theorem harmonicFiniteDriftVariationSmooth_trace (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) :
    EqOn (harmonicFiniteDriftVariationSmooth ell f).1 0 (standardSphere dim) := by
  intro z hz
  unfold harmonicFiniteDriftVariationSmooth
  change eval (euclideanCoordinates dim z) (∑ k ∈ f.support,
    driftFirstVariation k (fun i => ell (axis i)) (harmonicPolynomialRepresentativeL k (f k))) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero fun k _ =>
    eval_driftFirstVariation_eq_zero k (fun i => ell (axis i)) _ _ (unitSphere_sum_sq ⟨z,hz⟩)

theorem harmonicFiniteDriftVariationSmooth_flat_laplace (ell : X dim →L[ℝ] ℝ)
    (f : HarmonicFiniteCoefficients dim) (z : X dim) :
    laplace (fun _ => (1 : Mat dim)) (harmonicFiniteDriftVariationSmooth ell f).1 z =
      -(∑ i, ell (axis i)*coordDeriv i (harmonicFiniteSmooth f).1 z) := by
  let p (k : ℕ) := harmonicPolynomialRepresentativeL k (f k)
  let q (k : ℕ) := driftFirstVariation k (fun i => ell (axis i)) (p k)
  have h (k : ℕ) :
      polynomialEvaluation (AngularPolynomial.laplacian (q k)) z =
        -(∑ i, ell (axis i)*polynomialEvaluation (pderiv i (p k)) z) := by
    have hp := harmonicPolynomialRepresentative_mem k (f k)
    have h' := cartesianLaplacian_driftFirstVariation hp.1 hp.2
      (fun i => ell (axis i)) (euclideanCoordinates dim z)
    rw [cartesianLaplacian_eval, fderiv_eval_apply] at h'
    exact h'
  change laplace (fun _ => (1 : Mat dim)) (polynomialEvaluation (∑ k ∈ f.support, q k)) z =
    -(∑ i, ell (axis i)*coordDeriv i (polynomialEvaluation (∑ k ∈ f.support, p k)) z)
  rw [laplace_identity_polynomialEvaluation,laplacian_sum]
  simp only [coordDeriv_polynomialEvaluation,map_sum]
  change eval (euclideanCoordinates dim z) (∑ k ∈ f.support, AngularPolynomial.laplacian (q k)) =
    -(∑ i, ell (axis i) * eval (euclideanCoordinates dim z) (∑ k ∈ f.support, pderiv i (p k)))
  simp only [map_sum]
  change (∑ k ∈ f.support, polynomialEvaluation (AngularPolynomial.laplacian (q k)) z) =
    -(∑ i, ell (axis i) * (∑ k ∈ f.support, polynomialEvaluation (pderiv i (p k)) z))
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]

/-- The weak first Taylor coefficient is the outward radial derivative of
the first solid-harmonic correction plus the first conormal weight. -/
theorem affineEnergy_harmonicFinite_eq_firstConormal (ell : X dim →L[ℝ] ℝ)
    (f g : HarmonicFiniteCoefficients dim) :
    let u := harmonicFiniteSmooth f
    let q := harmonicFiniteDriftVariationSmooth ell f
    energyFormH1 (fun z => ell z • (1 : Mat dim)) 0 0 (smoothSobolev u)
      (smoothSobolev (harmonicFiniteSmooth g)) =
      unitSphereArea dim * ∫ w : ↥(standardSphere dim),
        (harmonicFiniteSmooth g).1 w *
          (ell w*fderiv ℝ u.1 w w+fderiv ℝ q.1 w w) ∂(sphereProbability dim) := by
  let u := harmonicFiniteSmooth f
  let q := harmonicFiniteDriftVariationSmooth ell f
  apply affineEnergy_eq_firstConormal_of_firstVariation ell u q g
    (harmonicFiniteDriftVariationSmooth_trace ell f)
  intro z _
  have hQ := negativeBallDivergence_scalar (fun _ => (1 : ℝ)) q contDiff_const z
  have hU := negativeBallDivergence_scalar ell u ell.contDiff z
  simp only [one_smul,one_mul,coordDeriv,fderiv_fun_const,Pi.zero_apply,zero_apply,
    zero_mul,Finset.sum_const_zero,add_zero] at hQ
  rw [hQ,hU,harmonicFiniteDriftVariationSmooth_flat_laplace,laplace_flat_harmonicFiniteSmooth]
  simp only [coordDeriv,ContinuousLinearMap.fderiv,mul_zero,zero_add,neg_neg,u,add_neg_cancel]

end CalderonN
