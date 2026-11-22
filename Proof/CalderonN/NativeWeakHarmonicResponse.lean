module

public import Proof.CalderonN.HarmonicH1Lift
public import Proof.CalderonN.FixedBallSmoothFlux
public import Proof.CalderonN.FixedBallSmoothEnergy
public import Proof.CalderonN.NativeCoefficientBallPoisson

import Proof.CalderonN.PolynomialPoissonFirstVariation
import Mathlib.Tactic

/-! The weak and strong Poisson responses in the common native ball,
specialized to the actual finite harmonic tests used in Proposition 5.3. -/

public section

noncomputable section
open Set Metric MvPolynomial MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise Classical DirectSum
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon AngularPolynomial SphereHarmonic GreenRadialTrace
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def harmonicFinitePolynomial (f : HarmonicFiniteCoefficients dim) : MvPolynomial (Fin dim) ℝ :=
  ∑ k ∈ f.support, harmonicPolynomialRepresentativeL k (f k)

@[expose] def harmonicFiniteSmooth (f : HarmonicFiniteCoefficients dim) : SmoothData dim :=
  ⟨polynomialEvaluation (harmonicFinitePolynomial f),
    contDiff_polynomialEvaluation (harmonicFinitePolynomial f)⟩

theorem harmonicFirstOrderLift_finite_smooth (f : HarmonicFiniteCoefficients dim) :
    harmonicFirstOrderLift dim (harmonicBoundaryFiniteL (1/2 : ℝ) f) =
      smoothSobolev (harmonicFiniteSmooth f) := by
  rw [harmonicFirstOrderLift_finite, harmonicFirstOrderFiniteL_eq_polynomial,
    polynomialBallH1L_apply]
  unfold harmonicFiniteSmooth harmonicFinitePolynomial
  rfl

omit [Nontrivial (Fin dim)] in
private theorem laplacian_harmonicFinitePolynomial (f : HarmonicFiniteCoefficients dim) :
    AngularPolynomial.laplacian (harmonicFinitePolynomial f) = 0 := by
  unfold harmonicFinitePolynomial
  rw [laplacian_sum, Finset.sum_eq_zero]
  exact fun k _ => (harmonicPolynomialRepresentative_mem k (f k)).2

theorem laplace_flat_harmonicFiniteSmooth (f : HarmonicFiniteCoefficients dim)
    (z : X dim) :
    laplace (fun _ => (1 : Mat dim)) (harmonicFiniteSmooth f).1 z = 0 := by
  unfold harmonicFiniteSmooth
  rw [laplace_identity_polynomialEvaluation, laplacian_harmonicFinitePolynomial]
  exact map_zero (eval (euclideanCoordinates dim z))

omit [Nontrivial (Fin dim)] in
theorem negativeBallDivergence_flat_harmonicFiniteSmooth
    (f : HarmonicFiniteCoefficients dim) (z : X dim) :
    negativeBallDivergence (fun _ => (1 : Mat dim)) (harmonicFiniteSmooth f).1 z = 0 := by
  classical
  let p := harmonicFinitePolynomial f
  unfold harmonicFiniteSmooth negativeBallDivergence Elliptic.Lop
  change -(∑ i, coordDeriv i (fun x => ∑ j, (1 : Mat dim) i j *
    coordDeriv j (polynomialEvaluation p) x) z) = 0
  have h (i : Fin dim) : (fun x => ∑ j, (1 : Mat dim) i j * coordDeriv j (polynomialEvaluation p) x) =
      coordDeriv i (polynomialEvaluation p) := by
    funext x
    simp [Matrix.one_apply,ite_mul]
  simp_rw [h,coordDeriv_polynomialEvaluation]
  change -(∑ i, eval (euclideanCoordinates dim z) (pderiv i (pderiv i p))) = 0
  rw [← map_sum]
  change -polynomialEvaluation (AngularPolynomial.laplacian p) z = 0
  rw [laplacian_harmonicFinitePolynomial,show polynomialEvaluation (0 : MvPolynomial (Fin dim) ℝ) z = 0
    from map_zero (eval (euclideanCoordinates dim z)),neg_zero]

@[expose] def fixedBallFlatEnergyL (dim : ℕ) [NeZero dim] :
    FixedBallH1 dim →L[ℝ] FixedBallH1 dim →L[ℝ] ℝ :=
  fixedBallSmoothEnergyL (continuous_const (y := (1 : Mat dim)))

theorem fixedBallFlatEnergyL_harmonicFirstOrderLift_zero
    (f : SphereSobolev dim (1/2 : ℝ)) (v : FixedBallH1Zero dim) :
    fixedBallFlatEnergyL dim (harmonicFirstOrderLift dim f) (fixedBallZeroInclusionL dim v) = 0 := by
  let E := fixedBallFlatEnergyL dim
  let P := harmonicFirstOrderLift dim
  have hclosed : IsClosed {g : SphereSobolev dim (1/2 : ℝ) |
      E (P g) (fixedBallZeroInclusionL dim v) = 0} :=
    isClosed_eq ((ContinuousLinearMap.apply ℝ ℝ (fixedBallZeroInclusionL dim v)).continuous.comp
      (E.continuous.comp P.continuous)) continuous_const
  refine (denseRange_harmonicBoundaryFiniteL (dim := dim) (1/2 : ℝ)).induction_on f hclosed ?_
  intro a
  change E (P (harmonicBoundaryFiniteL (1/2 : ℝ) a)) (fixedBallZeroInclusionL dim v) = 0
  rw [show P = harmonicFirstOrderLift dim from rfl, harmonicFirstOrderLift_finite_smooth]
  unfold E fixedBallFlatEnergyL
  rw [fixedBallSmoothEnergyL_apply]
  exact energyFormH1_smooth_zeroDirichlet contDiff_const (harmonicFiniteSmooth a)
    (fun z _ => negativeBallDivergence_flat_harmonicFiniteSmooth a z) v

theorem fixedBallFlatEnergyL_harmonicFirstOrderLift_zero_left
    (f : SphereSobolev dim (1/2 : ℝ)) (v : FixedBallH1Zero dim) :
    fixedBallFlatEnergyL dim (fixedBallZeroInclusionL dim v) (harmonicFirstOrderLift dim f) = 0 := by
  rw [← fixedBallFlatEnergyL_harmonicFirstOrderLift_zero f v]
  unfold fixedBallFlatEnergyL
  simp only [fixedBallSmoothEnergyL_apply]
  exact energyFormH1_comm_of_isSymm_ae (Filter.Eventually.of_forall fun _ => Matrix.isSymm_one) _ _

omit [Nontrivial (Fin dim)] in
/-- The zero-Dirichlet correction in the strong operator is still
zero-Dirichlet after projecting to the first-order graph space. -/
theorem firstOrder_ballPoissonOperatorL_sub_mem (F : SmoothCoefficientMatrix dim 2)
    (U : BallSobolev dim 2) :
    TauCeti.Wkp.firstOrder 1 (ballPoissonOperatorL 0 F U) - TauCeti.Wkp.firstOrder 1 U ∈
      w1p0Submodule volume (fixedBallOpens dim) 2 := by
  let C := (strongDirichletOperator fixedSobolevCalculus 0 F).inverse (fullBallDivergenceL 0 F U)
  have hC := (mem_strongDirichletSubmodule 0 (C : BallSobolev dim 2)).mp C.property
  have hEq : TauCeti.Wkp.firstOrder 1 (ballPoissonOperatorL 0 F U) - TauCeti.Wkp.firstOrder 1 U =
      -TauCeti.Wkp.firstOrder 1 (C : BallSobolev dim 2) := by
    unfold ballPoissonOperatorL
    simp only [sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, ← TauCeti.Wkp.firstOrderL_apply, map_sub, C]
    abel
  rw [hEq]
  exact (w1p0Submodule volume (fixedBallOpens dim) 2).neg_mem hC

/-- On a finite smooth datum, the weak conormal uses the same classical
solution as the strong normalized Poisson operator. -/
theorem weakPoissonL_eq_native_classical_finite
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (coefficientMatrixField 2 F) lo hi) (f : HarmonicFiniteCoefficients dim) :
    let a := coefficientMatrixField 2 F
    let hA := (contDiff_coefficientMatrixField 2 F).continuous
    let E := fixedBallSmoothEnergyL hA
    let P := weakDirichletPoissonL (fixedBallZeroInclusionL dim) E
      (isCoercive_fixedBallSmoothEnergy hA hEll) (harmonicFirstOrderLift dim)
    ∃ b : SmoothData dim,
      EqOn b.1 (harmonicFiniteSmooth f).1 (standardSphere dim) ∧
      EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1) ∧
      P (harmonicBoundaryFiniteL (1/2 : ℝ) f) = smoothSobolev b := by
  dsimp only
  let a := coefficientMatrixField 2 F
  let hA := (contDiff_coefficientMatrixField 2 F).continuous
  let E := fixedBallSmoothEnergyL hA
  let u := harmonicFiniteSmooth f
  obtain ⟨b,hb,hbT,hbH,hbRep⟩ := exists_native_classicalBallPoisson 0 F hEll u
  let B : SmoothData dim := ⟨b,hb⟩
  refine ⟨B,hbT,hbH,?_⟩
  symm
  apply eq_weakDirichletPoissonL_of_equation
  · have hM := firstOrder_ballPoissonOperatorL_sub_mem F (smoothBallSobolev 2 u)
    rw [hbRep, firstOrder_smoothBallSobolev, firstOrder_smoothBallSobolev] at hM
    rw [harmonicFirstOrderLift_finite_smooth]
    exact ⟨⟨_,hM⟩,rfl⟩
  · intro v
    rw [fixedBallSmoothEnergyL_apply]
    exact energyFormH1_smooth_zeroDirichlet (contDiff_coefficientMatrixField 2 F) B hbH v

end CalderonN
