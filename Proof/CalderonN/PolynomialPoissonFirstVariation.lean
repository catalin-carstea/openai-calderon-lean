module

public import Proof.CalderonN.NativeCoefficientBallForcing
public import Proof.CalderonN.PolynomialBallGreenPairing
public import Proof.CalderonN.PolynomialDriftVariation

import Proof.CalderonN.FlatBallPolynomials
import Proof.CalderonN.GreenSourceCutoff
import Proof.CalderonN.HarmonicL2Space
import Mathlib.Tactic

/-! The released affine drift polynomial represents the same first
variation as the native strong inverse on the fixed ball. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory MvPolynomial
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial GreenRadialTrace BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem laplace_identity_metric (u : X dim → ℝ) (z : X dim) :
    laplace (fun _ => (1 : Mat dim)) u z = ∑ i, coordDeriv i (coordDeriv i u) z := by
  simpa only [flatBallMetric,one_pow,one_smul,inv_one,one_mul] using
    laplace_flatBallMetric (dim := dim) one_pos u z

theorem laplace_identity_polynomialEvaluation (p : MvPolynomial (Fin dim) ℝ) (z : X dim) :
    laplace (fun _ => (1 : Mat dim)) (polynomialEvaluation p) z =
      polynomialEvaluation (AngularPolynomial.laplacian p) z := by
  rw [laplace_identity_metric]
  simp only [coordDeriv_polynomialEvaluation,AngularPolynomial.laplacian,polynomialEvaluation,map_sum]

theorem negativeBallDivergence_scalar (f : X dim → ℝ) (u : SmoothData dim)
    (hf : ContDiff ℝ ∞ f) (z : X dim) :
    negativeBallDivergence (fun w => f w • (1 : Mat dim)) u.1 z =
      -(f z * laplace (fun _ => (1 : Mat dim)) u.1 z +
          ∑ i, coordDeriv i f z * coordDeriv i u.1 z) := by
  classical
  rw [laplace_identity_metric]
  unfold negativeBallDivergence Elliptic.Lop
  have hRow (i : Fin dim) :
      (fun w => ∑ j, ((f w) • (1 : Mat dim)) i j * coordDeriv j u.1 w) =
      fun w => f w * coordDeriv i u.1 w := by
    funext w
    simp [Matrix.one_apply, apply_ite, ite_mul]
  simp_rw [hRow]
  have hProduct (i : Fin dim) :
      Elliptic.pd i (fun w => f w * coordDeriv i u.1 w) z =
        f z * coordDeriv i (coordDeriv i u.1) z + coordDeriv i f z * coordDeriv i u.1 z := by
    have hu : DifferentiableAt ℝ (coordDeriv i u.1) z :=
      (smoothDataCoordDeriv i u).2.differentiable (by simp) z
    change fderiv ℝ (fun w => f w * coordDeriv i u.1 w) z (axis i) = _
    rw [fderiv_fun_mul (hf.differentiable (by simp) z) hu]
    simp only [add_apply,smul_apply,smul_eq_mul,coordDeriv]
    ring
  simp_rw [hProduct,Finset.sum_add_distrib,← Finset.mul_sum]

omit [Nontrivial (Fin dim)] in
private theorem smoothBallSobolev_eq_on_ball (k : ℕ) (u v : SmoothData dim)
    (h : EqOn u.1 v.1 (ball (0 : X dim) 1)) : smoothBallSobolev k u = smoothBallSobolev k v := by
  apply TauCeti.Wkp.ext k
  apply Lp.ext
  have hm := ae_restrict_mem (μ := (volume : Measure (X dim))) (fixedBallOpens dim).isOpen.measurableSet
  filter_upwards [value_smoothBallSobolev_ae k u,value_smoothBallSobolev_ae k v,hm] with z ha hb hz
  exact ha.trans ((h hz).trans hb.symm)

/-- The normalized affine model has the precise polynomial first
variation from the checked dimension-three development. -/
theorem polynomialFirstVariation_represents_strongInverse
    (F0 F1 : SmoothCoefficientMatrix dim 2)
    (hF0 : ∀ z ∈ closedBall (0 : X dim) 2, coefficientMatrixField 2 F0 z = 1)
    (ell : X dim →L[ℝ] ℝ)
    (hF1 : EqOn (coefficientMatrixField 2 F1) (fun z => ell z • (1 : Mat dim))
      (ball (0 : X dim) (5/4))) (k : ℕ) (p : MvPolynomial (Fin dim) ℝ)
    (hp : p ∈ harmonicHomogeneous dim k) :
    let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
    let q := driftFirstVariation k (fun i => ell (axis i)) p
    let v : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
    let j := (strongDirichletSubmodule dim 0).toSubmodule.subtypeL
    let I₀ := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
    smoothBallSobolev 2 v = -j (I₀ (fullBallDivergenceL 0 F1 (smoothBallSobolev 2 u))) := by
  let u : SmoothData dim := ⟨polynomialEvaluation p,contDiff_polynomialEvaluation p⟩
  let b (i : Fin dim) := ell (axis i)
  let q := driftFirstVariation k b p
  let v : SmoothData dim := ⟨polynomialEvaluation q,contDiff_polynomialEvaluation q⟩
  let A := coefficientMatrixField 2 F0
  let C := coefficientMatrixField 2 F1
  have hEll : TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A 1 1 := by
    have hh := TauCeti.PDE.uniformlyEllipticOn_const_one_one (n := Fin dim) (fixedBallOpens dim : Set (X dim))
    refine ⟨hh.1,hh.2.1,fun z hz => ?_⟩
    rw [show A z = 1 from hF0 z (closedBall_subset_closedBall (by norm_num : (1:ℝ) ≤ 2)
      (ball_subset_closedBall hz))]
    exact hh.2.2 hz
  obtain ⟨hD,hDOp⟩ := fullBallDivergence_native_smooth 0 F1 u
  let f : SmoothData dim := ⟨negativeBallDivergence C u.1,hD⟩
  let g : SmoothData dim := ⟨-f.1,f.2.neg⟩
  obtain ⟨w,hwT,hwL,hwRep⟩ := exists_native_classical_zeroDirichlet F0 hEll g
  have hDOp' : fullBallDivergenceL 0 F1 (smoothBallSobolev 2 u) = smoothBallSobolev 0 f := hDOp
  have hG : smoothBallSobolev 0 g = -smoothBallSobolev 0 f := by
    let f' : smoothBallDataSubmodule dim := ⟨f.1,f.2⟩
    exact map_neg ((smoothBallSobolevLinear dim) 0) f'
  have hA (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A =ᶠ[𝓝 z] fun _ => (1 : Mat dim) := by
    have hz' : z ∈ ball (0 : X dim) 2 := ball_subset_ball (by norm_num) hz
    filter_upwards [isOpen_ball.mem_nhds hz'] with x hx
    exact hF0 x (ball_subset_closedBall hx)
  have hC (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      C =ᶠ[𝓝 z] fun x => (ell x) • (1 : Mat dim) := by
    have hz' : z ∈ ball (0 : X dim) (5/4) := ball_subset_ball (by norm_num) hz
    filter_upwards [isOpen_ball.mem_nhds hz'] with x hx using hF1 hx
  have hLapU (z : X dim) : laplace (fun _ => (1 : Mat dim)) u.1 z = 0 := by
    change laplace (fun _ => (1 : Mat dim)) (polynomialEvaluation p) z = 0
    rw [laplace_identity_polynomialEvaluation,hp.2]
    exact map_zero (eval (euclideanCoordinates dim z))
  have hLapW (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
      laplace (fun _ => (1 : Mat dim)) w.1 z =
        -(∑ i, b i * polynomialEvaluation (pderiv i p) z) := by
    have h := hwL hz
    change negativeBallDivergence A w.1 z = -negativeBallDivergence C u.1 z at h
    rw [negativeBallDivergence_congr_germ (hA z hz) EventuallyEq.rfl,
      negativeBallDivergence_congr_germ (hC z hz) EventuallyEq.rfl] at h
    have h1 := negativeBallDivergence_scalar (fun _ => (1 : ℝ)) w contDiff_const z
    have h2 := negativeBallDivergence_scalar ell u ell.contDiff z
    rw [show (fun _ : X dim => (1 : ℝ) • (1 : Mat dim)) = fun _ => (1 : Mat dim) from
      funext (fun _ => one_smul _ _)] at h1
    rw [h1,h2,hLapU z] at h
    change laplace (fun _ => (1 : Mat dim)) w.1 z = _
    have he (i : Fin dim) : coordDeriv i u.1 z = polynomialEvaluation (pderiv i p) z :=
      congrFun (coordDeriv_polynomialEvaluation i p) z
    have hf (i : Fin dim) : coordDeriv i (fun _ : X dim => (1 : ℝ)) z = 0 := by
      simp [coordDeriv]
    have hb (i : Fin dim) : coordDeriv i ell z = b i := by
      rw [coordDeriv,ContinuousLinearMap.fderiv]
    simp only [hf,hb,he,mul_zero,one_mul,zero_mul,Finset.sum_const_zero,add_zero,
      zero_add,neg_neg] at h
    exact neg_eq_iff_eq_neg.mp h
  have hLapV (z : X dim) : laplace (fun _ => (1 : Mat dim)) v.1 z =
      -(∑ i, b i * polynomialEvaluation (pderiv i p) z) := by
    change laplace (fun _ => (1 : Mat dim)) (polynomialEvaluation q) z = _
    rw [laplace_identity_polynomialEvaluation]
    have h := cartesianLaplacian_driftFirstVariation hp.1 hp.2 b (euclideanCoordinates dim z)
    rw [cartesianLaplacian_eval, fderiv_eval_apply] at h
    exact h
  have hvT : EqOn v.1 0 (standardSphere dim) := by
    intro z hz
    change eval (euclideanCoordinates dim z) q = 0
    exact eval_driftFirstVariation_eq_zero k b p _ (unitSphere_sum_sq ⟨z,hz⟩)
  have hMetric : SmoothMetric univ (fun _ : X dim => (1 : Mat dim)) :=
    ⟨fun _ _ => contDiffOn_const,fun _ _ => Matrix.PosDef.one⟩
  have hDiff := eqOn_closedUnitBall_of_laplace_eq_zero isOpen_univ (subset_univ _) hMetric
    ((v.2.sub w.2).contDiffOn) (u := v.1-w.1)
    (by
      intro z hz
      change laplace (fun _ => (1 : Mat dim)) (fun x => v.1 x-w.1 x) z = 0
      rw [laplace_sub isOpen_univ _ v.2.contDiffOn w.2.contDiffOn (mem_univ z),
        hLapV z,hLapW z hz,sub_self])
    (fun z hz => by change v.1 z-w.1 z = 0; rw [hvT hz,hwT hz]; exact sub_self 0)
  have hvw : smoothBallSobolev 2 v = smoothBallSobolev 2 w :=
    smoothBallSobolev_eq_on_ball 2 v w (fun z hz => sub_eq_zero.mp (hDiff (ball_subset_closedBall hz)))
  change smoothBallSobolev 2 v = -(((strongDirichletSubmodule dim) 0).toSubmodule.subtypeL.comp
    (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse)
      (fullBallDivergenceL 0 F1 (smoothBallSobolev 2 u))
  rw [hvw,hwRep,hG,hDOp',map_neg]

end CalderonN
