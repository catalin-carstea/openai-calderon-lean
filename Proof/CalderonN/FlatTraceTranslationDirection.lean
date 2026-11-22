module

public import Proof.CalderonN.FlatTraceRaisingIdentities
public import Proof.CalderonN.SmoothTraceVelocityAffine

import Mathlib.Tactic

/-! Independence of the flat degree from the chosen Poisson solutions,
and the flat translation adjoint in any chart direction. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothTraceFlatDegree_eq (hn : 3 ≤ dim)
    {A D : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hD : ContDiff ℝ ∞ D)
    {lo hi p q : ℝ}
    (hAE : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (hDE : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) D p q)
    {a b : X dim →L[ℝ] ℝ}
    (SA : ∀ f : SmoothData dim, ConormalTaylorSolutions A a f)
    (SD : ∀ f : SmoothData dim, ConormalTaylorSolutions D b f) :
    smoothTraceFlatDegree hA hAE SA = smoothTraceFlatDegree hD hDE SD := by
  apply SmoothTraceAdjoint.eq_of_finite
    (smoothTraceFlatDegree_symmetric hn hA hAE SA) (smoothTraceFlatDegree_symmetric hn hD hDE SD)
  intro f
  rw [smoothTraceFlatDegree_finite,smoothTraceFlatDegree_finite]

private theorem smoothSphereTraceMul_sum {ι : Type*} [Fintype ι]
    (m : SmoothData dim) (f : ι → SmoothData dim) (a : ι → ℝ)
    (h : EqOn m.1 (fun z => ∑ i,a i*(f i).1 z) (standardSphere dim)) :
    smoothSphereTraceMul m = ∑ i,a i • smoothSphereTraceMul (f i) := by
  ext u : 1
  apply Subtype.ext
  funext z
  simp only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,
    LinearMap.smul_apply,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,smoothSphereTraceMul_apply,h z.2,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

theorem smoothTraceRaising_const_eq_sum (B : Module.End ℝ (SmoothSphereTrace dim)) (a : X dim) :
    smoothSphereGaussAdjoint B (smoothConstantVelocity a) = ∑ i : I dim, a i • smoothTraceRaising B i := by
  let V := smoothConstantVelocity a
  let W := smoothAxisVelocity (dim:=dim)
  have hN : smoothSphereTraceMul (smoothVelocityNormal V) =
      ∑ i : I dim,a i • smoothSphereTraceMul (smoothVelocityNormal (W i)) := by
    apply smoothSphereTraceMul_sum
    intro z _
    have ha : (∑ i : I dim,a i • axis i) = a := by
      classical
      ext i
      simp [axis,Pi.single_apply,mul_ite]
    change ⟪z,a⟫_ℝ = ∑ i : I dim,a i*⟪z,axis i⟫_ℝ
    conv_lhs => rw [← ha]
    rw [inner_sum]
    simp_rw [real_inner_smul_right]
  have hA (i j : I dim) : smoothSphereTraceMul (smoothVelocityAngular V i j) =
      ∑ k : I dim,a k • smoothSphereTraceMul (smoothVelocityAngular (W k) i j) := by
    classical
    apply smoothSphereTraceMul_sum
    intro z _
    change z i*a j = ∑ k : I dim,a k*(z i*axis k j)
    simp [axis,PiLp.single_apply,mul_ite,mul_comm]
  have hT : smoothSphereVelocityTangent V = ∑ k : I dim,a k • smoothSphereVelocityTangent (W k) := by
    unfold smoothSphereVelocityTangent
    let E (i j k : I dim) := a k • (smoothSphereTraceRotation i j *
      smoothSphereTraceMul (smoothVelocityAngular (W k) i j))
    simp only [hA,Finset.mul_sum,mul_smul_comm,Finset.smul_sum]
    change (∑ i : I dim,∑ j : I dim,∑ k : I dim,E i j k) = ∑ k : I dim,∑ i : I dim,∑ j : I dim,E i j k
    simp_rw [Finset.sum_comm (f := fun j k => E _ j k)]
    exact Finset.sum_comm
  change smoothSphereGaussAdjoint B V = ∑ i : I dim,a i • smoothSphereGaussAdjoint B (W i)
  conv_lhs => rw [smoothSphereGaussAdjoint,hN,hT,Finset.mul_sum]
  have hEq (i : I dim) : a i • smoothSphereGaussAdjoint B (W i) =
      B*(a i • smoothSphereTraceMul (smoothVelocityNormal (W i)))-
        a i • smoothSphereVelocityTangent (W i) := by
    rw [smoothSphereGaussAdjoint,mul_smul_comm]
    apply LinearMap.ext
    intro u
    simp only [LinearMap.smul_apply,LinearMap.sub_apply,smul_sub]
  simp_rw [hEq]
  symm
  exact Finset.sum_sub_distrib (s:=Finset.univ)
    (fun i : I dim => B*(a i • smoothSphereTraceMul (smoothVelocityNormal (W i))))
    (fun i : I dim => a i • smoothSphereVelocityTangent (W i))

end CalderonN
