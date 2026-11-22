module

public import Proof.CalderonN.FlatTraceRaisingAction
public import Proof.CalderonN.SmoothTraceFlatDegree
public import Proof.CalderonN.SmoothTraceMultiplierOrder
public import Proof.CalderonN.SmoothTraceFiniteExt

import Mathlib.Tactic

/-! Both flat translation maps act on the same core, with their genuine
sphere adjunction and polynomial degree actions. -/

public section

noncomputable section
open Set MvPolynomial
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon
  SphereHarmonic AngularPolynomial GreenRadialTrace SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothTraceRaising (B : Module.End ℝ (SmoothSphereTrace dim)) (i : Fin dim) :
    Module.End ℝ (SmoothSphereTrace dim) := smoothSphereGaussAdjoint B (smoothAxisVelocity i)

@[expose] def smoothTraceLowering (B : Module.End ℝ (SmoothSphereTrace dim)) (i : Fin dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  smoothSphereTraceMul (smoothCoordinateData i)*B+
    ∑ j, smoothSphereTraceMul (smoothCoordinateData j)*smoothSphereTraceRotation j i

theorem smoothTraceRaising_eq_coordinate_rotation (B : Module.End ℝ (SmoothSphereTrace dim)) (i : Fin dim) :
    smoothTraceRaising B i = B*smoothSphereTraceMul (smoothCoordinateData i)-
      ∑ j, smoothSphereTraceRotation j i*smoothSphereTraceMul (smoothCoordinateData j) := by
  have hM : smoothVelocityNormal (smoothAxisVelocity i) = smoothCoordinateData i :=
    Subtype.ext (smoothVelocityNormal_axis i)
  rw [smoothTraceRaising,smoothSphereGaussAdjoint,hM]
  congr 1
  ext u : 1
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let F : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  apply Subtype.ext
  funext z
  change (smoothSphereVelocityTangent (smoothAxisVelocity i) (smoothSphereTrace F)).1 z = _
  rw [smoothSphereVelocityTangent_axis_apply,LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  let FJ : SmoothData dim :=
    ⟨fun x => F.1 x*x j,F.2.mul (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff⟩
  have h : smoothSphereTraceMul (smoothCoordinateData j) (smoothSphereTrace F) = smoothSphereTrace FJ := by
    apply Subtype.ext
    funext w
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    change w.val j*F.1 w = F.1 w*w.val j
    exact mul_comm _ _
  change _ = (smoothSphereTraceRotation j i (smoothSphereTraceMul (smoothCoordinateData j) (smoothSphereTrace F))).1 z
  rw [h,smoothSphereTraceRotation_apply,smoothSphereTrace_apply]

theorem smoothTraceRaising_adjoint (hn : 3 ≤ dim) (B : Module.End ℝ (SmoothSphereTrace dim))
    (hB : SmoothTraceAdjoint hn B B) (i : Fin dim) :
    SmoothTraceAdjoint hn (smoothTraceRaising B i) (smoothTraceLowering B i) := by
  rw [smoothTraceRaising_eq_coordinate_rotation]
  unfold smoothTraceLowering
  let M (j : Fin dim) := smoothSphereTraceMul (smoothCoordinateData j)
  let K (j : Fin dim) := smoothSphereTraceRotation j i
  have hM (j : Fin dim) : SmoothTraceAdjoint hn (M j) (M j) := smoothSphereTraceMul_symmetric hn _
  have hK (j : Fin dim) : SmoothTraceAdjoint hn (K j) (-K j) := smoothTraceRotation_skew hn _ _
  have hSum : SmoothTraceAdjoint hn (∑ j, K j*M j) (∑ j, M j*(-K j)) :=
    SmoothTraceAdjoint.sum Finset.univ _ _ (fun j _ => (hK j).mul (hM j))
  have h := (hB.mul (hM i)).sub hSum
  simp only [mul_neg,Finset.sum_neg_distrib,sub_neg_eq_add] at h
  exact h

private theorem sum_coordinate_rotationPolynomial_eq (k : ℕ) (i : Fin dim)
    (p : MvPolynomial (Fin dim) ℝ) (hp : p.IsHomogeneous k) :
    (∑ j, MvPolynomial.X j*polynomialRotation j i p) =
      radiusSq*pderiv i p-C (k:ℝ)*(MvPolynomial.X i*p) := by
  simp only [polynomialRotation,mul_sub,Finset.sum_sub_distrib,← mul_assoc,← pow_two,
    ← Finset.sum_mul, mul_right_comm (MvPolynomial.X _) (MvPolynomial.X i),← mul_assoc]
  change radiusSq*pderiv i p- _ = _
  congr 1
  rw [← polynomialEuler,polynomialEuler_homogeneous k p hp]
  ring

theorem smoothTraceLowering_polynomial
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (k : ℕ) (i : Fin dim) (p : MvPolynomial (Fin dim) ℝ) (hp : p ∈ harmonicHomogeneous dim k) :
    smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i (smoothSphereTrace (smoothPolynomialData p)) =
      smoothSphereTrace (smoothPolynomialData (pderiv i p)) := by
  apply Subtype.ext
  funext z
  have hB := smoothSphereTaylor_flat_degree_polynomial hA hEll S k p hp
  unfold smoothTraceLowering
  simp only [LinearMap.add_apply,LinearMap.sum_apply,Module.End.mul_apply,Submodule.coe_add,
    Pi.add_apply,Submodule.coe_sum,Finset.sum_apply,smoothSphereTraceMul_apply,
    smoothSphereTraceRotation_apply,smoothSphereTrace_apply,smoothCoordinateData,smoothPolynomialData,
    Subtype.coe_mk,sphereRotationDerivative_polynomialEvaluation]
  have hPart :
      (∑ j, z.val j*polynomialEvaluation (polynomialRotation j i p) z) =
        polynomialEvaluation (pderiv i p) z-(k:ℝ)*(z.val i*polynomialEvaluation p z) := by
    have hEval (j : Fin dim) : eval (euclideanCoordinates dim (z : X dim))
        (MvPolynomial.X j*polynomialRotation j i p) =
          z.val j*polynomialEvaluation (polynomialRotation j i p) z := by
      rw [map_mul,eval_X]
      rfl
    simp_rw [← hEval]
    rw [← map_sum,sum_coordinate_rotationPolynomial_eq k i p hp.1,map_sub,map_mul,map_mul,eval_C,map_mul,eval_X]
    have hR : eval (euclideanCoordinates dim (z : X dim)) (radiusSq : MvPolynomial (Fin dim) ℝ) = 1 := by
      simp only [radiusSq,map_sum,map_pow,eval_X]
      change (∑ j, (z.val j)^2) = 1
      exact unitSphere_sum_sq (⟨z,z.2⟩ : UnitSphere dim)
    rw [hR,one_mul]
    have hcoord : euclideanCoordinates dim (z : X dim) i = z.val i := rfl
    simp only [polynomialEvaluation,hcoord]
  change (z.val i)*(smoothTraceFlatDegree hA hEll S (smoothSphereTrace (smoothPolynomialData p))).1 z+
    (∑ j, z.val j*polynomialEvaluation (polynomialRotation j i p) z) =
      polynomialEvaluation (pderiv i p) z
  rw [hPart]
  have hD : (smoothTraceFlatDegree hA hEll S (smoothSphereTrace (smoothPolynomialData p))).1 z =
      (k:ℝ)*polynomialEvaluation p z := congrArg (fun u : SmoothSphereTrace dim => u.1 z) hB
  rw [hD]
  ring

end CalderonN
