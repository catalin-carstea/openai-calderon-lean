module

public import Proof.CalderonN.BallRotationFlux
public import Proof.CalderonN.FixedBallSmoothEnergy

import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! The angular commutator of a smooth conormal response is a single
coefficient-variation energy pairing. The zero-boundary part of the
rotated solution drops out by Green's identity. -/

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation BallDirichlet TauCeti PDE

variable {dim : ℕ} [NeZero dim]

@[expose] def smoothBallConormal (a : X dim → Mat dim) (u : X dim → ℝ) (z : X dim) : ℝ :=
  ⟪z, smoothBallFlux a u z⟫_ℝ

theorem contDiff_smoothBallConormal {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    (u : SmoothData dim) : ContDiff ℝ ∞ (smoothBallConormal a u.1) :=
  contDiff_id.inner ℝ (contDiff_smoothBallFlux ha u)

theorem smoothBallFlux_sub_solution (a : X dim → Mat dim)
    {u v : X dim → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (z : X dim) :
    smoothBallFlux a (u-v) z = smoothBallFlux a u z-smoothBallFlux a v z := by
  ext i
  simp only [smoothBallFlux_apply, PiLp.sub_apply, coordDeriv,
    fderiv_sub (hu z) (hv z), sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem sphereRotationDerivative_smoothBallConormal (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (u : SmoothData dim) (z : X dim) :
    sphereRotationDerivative i j (smoothBallConormal a u.1) z =
      ⟪z, smoothBallFlux a (sphereRotationDerivative i j u.1) z +
        smoothBallFlux (ballRotationCoefficient i j a) u.1 z⟫_ℝ := by
  let J := ballRotationGeneratorL i j
  let F := smoothBallFlux a u.1
  have hF := (contDiff_smoothBallFlux ha u).differentiable (by simp) z
  have hd := (hasFDerivAt_id z).inner ℝ hF.hasFDerivAt
  have h := congrArg (fun D : X dim →L[ℝ] ℝ => D (J z)) hd.fderiv
  change fderiv ℝ (smoothBallConormal a u.1) z (J z) = _ at h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderivInnerCLM_apply, id_eq] at h
  rw [sphereRotationDerivative,← ballRotationGeneratorL_apply,h]
  change ⟪z, fderiv ℝ F z (J z)⟫_ℝ+⟪J z,F z⟫_ℝ = _
  rw [← neg_eq_iff_eq_neg.mpr (inner_ballRotationGeneratorL_skew i j z (F z))]
  rw [← sub_eq_add_neg,← inner_sub_right]
  rw [show fderiv ℝ F z (J z)-J (F z) = _ from
    linearDirectional_smoothBallFlux_sub_rotation i j ha u z]

@[expose] def angularBallCorrection (i j : Fin dim) (u b : SmoothData dim) : SmoothData dim :=
  ⟨sphereRotationDerivative i j u.1-b.1,
    (contDiff_sphereRotationDerivative i j u.1 u.2).sub b.2⟩

/-- The full angular flux correction, including its coefficient term,
is divergence-free whenever the two solutions are harmonic. -/
theorem coordinateFluxDivergence_angularBallCorrection (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (u b : SmoothData dim)
    (hu : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1))
    (hb : EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1)) :
    EqOn (coordinateFluxDivergence (fun z =>
      smoothBallFlux a (angularBallCorrection i j u b).1 z+
      smoothBallFlux (ballRotationCoefficient i j a) u.1 z)) 0 (ball (0 : X dim) 1) := by
  let J := ballRotationGeneratorL i j
  let F := smoothBallFlux a u.1
  let R (z : X dim) := fderiv ℝ F z (J z)-J (F z)
  let G := smoothBallFlux a b.1
  have hFs := contDiff_smoothBallFlux ha u
  have hRs : ContDiff ℝ ∞ R :=
    ((hFs.fderiv_right (m := ∞) (by simp)).clm_apply J.contDiff).sub (J.contDiff.comp hFs)
  have hGs := contDiff_smoothBallFlux ha b
  have hIdentity : (fun z =>
      smoothBallFlux a (angularBallCorrection i j u b).1 z+
      smoothBallFlux (ballRotationCoefficient i j a) u.1 z) = R-G := by
    funext z
    rw [show (angularBallCorrection i j u b).1 = sphereRotationDerivative i j u.1-b.1 from rfl]
    rw [smoothBallFlux_sub_solution a ((contDiff_sphereRotationDerivative i j u.1 u.2).differentiable (by simp))
      (b.2.differentiable (by simp))]
    change _ = R z-G z
    rw [show R z = _ from linearDirectional_smoothBallFlux_sub_rotation i j ha u z]
    abel
  rw [hIdentity]
  intro z hz
  have hSub : coordinateFluxDivergence (R-G) z =
      coordinateFluxDivergence R z-coordinateFluxDivergence G z := by
    unfold coordinateFluxDivergence
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    change coordDeriv k ((fun x => R x k)-(fun x => G x k)) z = _
    have hp (H : X dim → X dim) (hH : ContDiff ℝ ∞ H) :
        DifferentiableAt ℝ (fun x => H x k) z :=
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp hH).differentiable (by simp) z
    simp only [coordDeriv,fderiv_sub (hp R hRs) (hp G hGs),sub_apply]
  rw [hSub,coordinateFluxDivergence_rotation_sub i j hFs z,
    coordinateFluxDivergence_smoothBallFlux,show negativeBallDivergence a b.1 z = 0 from hb hz]
  have hLoc : coordinateFluxDivergence F =ᶠ[nhds z] fun _ => 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    rw [coordinateFluxDivergence_smoothBallFlux,show negativeBallDivergence a u.1 w = 0 from hu hw,
      neg_zero]
  rw [sphereRotationDerivative,hLoc.fderiv_eq,fderiv_fun_const]
  simp

variable [Nontrivial (Fin dim)]

theorem angularBallCorrection_trace_zero (i j : Fin dim) (u b f : SmoothData dim)
    (hu : EqOn u.1 f.1 (standardSphere dim))
    (hb : EqOn b.1 (sphereRotationDerivative i j f.1) (standardSphere dim)) :
    EqOn (angularBallCorrection i j u b).1 0 (standardSphere dim) := by
  intro z hz
  have hz' := sphereRotationDerivative_eq_zero_of_sphere_zero i j (u.1-f.1) (u.2.sub f.2)
    (fun w => sub_eq_zero.mpr (hu w.property)) ⟨z,hz⟩
  change sphereRotationDerivative i j u.1 z-b.1 z = 0
  rw [hb hz]
  simpa only [sphereRotationDerivative,fderiv_sub ((u.2.differentiable (by simp)) z)
    ((f.2.differentiable (by simp)) z),sub_apply] using hz'

private theorem integrableOn_smoothBallFlux_pair {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    (u v : SmoothData dim) :
    IntegrableOn (fun z => ∑ k, gradient v.1 z k * smoothBallFlux a u.1 z k)
      (fixedBallOpens dim : Set (X dim)) := by
  have h : Continuous (fun z => ∑ k, gradient v.1 z k * smoothBallFlux a u.1 z k) := by
    apply continuous_finsetSum
    intro k _
    exact ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp
      (v.2.gradient_right (m := ∞) (by simp)).continuous).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp (contDiff_smoothBallFlux ha u).continuous)
  exact (h.continuousOn.integrableOn_compact (isCompact_closedBall (0 : X dim) 1)).mono_set ball_subset_closedBall

/-- The boundary variation of a Dirichlet solution pairs with a
harmonic test through the variation of the coefficient alone. -/
theorem integral_linearizedBallConormal
    {a da : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (hd : ContDiff ℝ ∞ da)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, (a z).IsSymm)
    (u w v : SmoothData dim)
    (hwT : EqOn w.1 0 (standardSphere dim))
    (hZero : EqOn (coordinateFluxDivergence (fun z =>
      smoothBallFlux a w.1 z+smoothBallFlux da u.1 z)) 0 (ball (0 : X dim) 1))
    (hv : EqOn (negativeBallDivergence a v.1) 0 (ball (0 : X dim) 1)) :
    (unitSphereArea dim * ∫ z : ↥(standardSphere dim), v.1 z *
        ⟪(z : X dim),smoothBallFlux a w.1 z+smoothBallFlux da u.1 z⟫_ℝ ∂(sphereProbability dim)) =
      energyFormH1 da 0 0 (smoothSobolev u) (smoothSobolev v) := by
  let F (z : X dim) := smoothBallFlux a w.1 z+smoothBallFlux da u.1 z
  have hFT : ContDiff ℝ ∞ F :=
    (contDiff_smoothBallFlux ha w).add (contDiff_smoothBallFlux hd u)
  have hE : energyFormH1 a 0 0 (smoothSobolev w) (smoothSobolev v) = 0 := by
    have hSymAE : ∀ᵐ z ∂(volume : Measure (X dim)).restrict (fixedBallOpens dim : Set (X dim)), (a z).IsSymm := by
      filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with z hz
      exact hSym z hz
    rw [energyFormH1_comm_of_isSymm_ae hSymAE,energyFormH1_smooth_eq_boundary_flux ha v w hv]
    have he : (fun z : ↥(standardSphere dim) => w.1 z *
        ⟪(z : X dim),smoothBallFlux a v.1 z⟫_ℝ) = fun _ => 0 := by
      funext z
      rw [show w.1 z = 0 from hwT z.property,zero_mul]
    rw [he,integral_zero,mul_zero]
  have hG := integral_smoothFlux_gradient_eq_boundary F hFT v hZero
  have hPair (x : X dim) : (∑ k, gradient v.1 x k * F x k) =
      (∑ k, gradient v.1 x k * smoothBallFlux a w.1 x k) +
        ∑ k, gradient v.1 x k * smoothBallFlux da u.1 x k := by
    simp only [F,PiLp.add_apply,mul_add,Finset.sum_add_distrib]
  have hBulk (A : X dim → Mat dim) (q : SmoothData dim) :
      energyFormH1 A 0 0 (smoothSobolev q) (smoothSobolev v) =
      ∫ x in fixedBallOpens dim, ∑ k, gradient v.1 x k * smoothBallFlux A q.1 x k := by
    rw [energyFormH1_smooth_left]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae v] with x hx
    rw [hx]
  simp_rw [hPair] at hG
  rw [integral_add (integrableOn_smoothBallFlux_pair ha w v)
      (integrableOn_smoothBallFlux_pair hd u v), ← hBulk, ← hBulk, hE, zero_add] at hG
  exact hG.symm

/-- Testing the actual angular conormal commutator against a harmonic
response leaves the derivative of the coefficient in the bulk energy. -/
theorem integral_angular_conormal_commutator (i j : Fin dim)
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    (hSym : ∀ z ∈ ball (0 : X dim) 1, (a z).IsSymm)
    (u b v f : SmoothData dim)
    (huT : EqOn u.1 f.1 (standardSphere dim))
    (hbT : EqOn b.1 (sphereRotationDerivative i j f.1) (standardSphere dim))
    (hu : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1))
    (hb : EqOn (negativeBallDivergence a b.1) 0 (ball (0 : X dim) 1))
    (hv : EqOn (negativeBallDivergence a v.1) 0 (ball (0 : X dim) 1)) :
    (unitSphereArea dim * ∫ z : ↥(standardSphere dim), v.1 z *
      (sphereRotationDerivative i j (smoothBallConormal a u.1) z-
        smoothBallConormal a b.1 z) ∂(sphereProbability dim)) =
      energyFormH1 (ballRotationCoefficient i j a) 0 0 (smoothSobolev u) (smoothSobolev v) := by
  let w := angularBallCorrection i j u b
  let aθ := ballRotationCoefficient i j a
  let F (z : X dim) := smoothBallFlux a w.1 z + smoothBallFlux aθ u.1 z
  have hθ := contDiff_ballRotationCoefficient i j ha
  have hG := integral_linearizedBallConormal ha hθ hSym u w v
    (angularBallCorrection_trace_zero i j u b f huT hbT)
    (coordinateFluxDivergence_angularBallCorrection i j ha u b hu hb) hv
  rw [← hG]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  rw [sphereRotationDerivative_smoothBallConormal i j ha u z]
  unfold smoothBallConormal
  rw [← inner_sub_right]
  congr 1
  change _ = smoothBallFlux a (sphereRotationDerivative i j u.1-b.1) z+_
  rw [smoothBallFlux_sub_solution a ((contDiff_sphereRotationDerivative i j u.1 u.2).differentiable (by simp))
    (b.2.differentiable (by simp))]
  abel

end CalderonN
