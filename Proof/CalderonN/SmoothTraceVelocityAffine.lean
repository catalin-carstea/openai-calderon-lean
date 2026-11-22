module

public import Proof.CalderonN.SmoothTraceGaussAdjoint
public import Proof.CalderonN.MovingAdjointExpansionAlgebra

import Mathlib.Tactic

/-! The affine translation and radial velocity parts of the sphere
adjoint, including the exact cancellation of the radial tangential term. -/

public section

noncomputable section
open Set
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothConstantVelocity (a : X dim) : SmoothBallVelocity dim :=
  ⟨fun _ => a,contDiff_const⟩

@[expose] def smoothAffineVelocity (a : X dim) (b c : ℝ) (U : SmoothBallVelocity dim) :
    SmoothBallVelocity dim :=
  ⟨fun z => a+b • z+c • U.1 z,(contDiff_const.add (contDiff_id.const_smul b)).add (U.2.const_smul c)⟩

theorem smoothSphereTraceMul_affine (m u v : SmoothData dim) (a b : ℝ)
    (h : EqOn m.1 (fun z => a*u.1 z+b*v.1 z) (standardSphere dim)) :
    smoothSphereTraceMul m = a • smoothSphereTraceMul u+b • smoothSphereTraceMul v := by
  ext f : 1
  apply Subtype.ext
  funext z
  change (smoothSphereTraceMul m f).1 z =
    a*(smoothSphereTraceMul u f).1 z+b*(smoothSphereTraceMul v f).1 z
  rw [smoothSphereTraceMul_apply,smoothSphereTraceMul_apply,smoothSphereTraceMul_apply,h z.2]
  change (a*u.1 z+b*v.1 z)*f.1 z = _
  ring

theorem smoothSphereTraceMul_add (m u v : SmoothData dim)
    (h : EqOn m.1 (fun z => u.1 z+v.1 z) (standardSphere dim)) :
    smoothSphereTraceMul m = smoothSphereTraceMul u+smoothSphereTraceMul v := by
  have hM : EqOn m.1 (fun z => 1*u.1 z+1*v.1 z) (standardSphere dim) := by simpa only [one_mul] using h
  simpa only [one_smul] using smoothSphereTraceMul_affine m u v 1 1 hM

theorem smoothSphereTraceMul_one : smoothSphereTraceMul (dim:=dim) ⟨1,contDiff_const⟩ = 1 := by
  ext f : 1
  apply Subtype.ext
  funext z
  rw [smoothSphereTraceMul_apply]
  change 1*f.1 z = f.1 z
  rw [one_mul]

theorem smoothSphereVelocityNormal_affine (a : X dim) (b c : ℝ) (U : SmoothBallVelocity dim) :
    smoothSphereTraceMul (smoothVelocityNormal (smoothAffineVelocity a b c U)) =
      smoothSphereTraceMul (smoothVelocityNormal (smoothConstantVelocity a))+
        b • 1+c • smoothSphereTraceMul (smoothVelocityNormal U) := by
  let M := smoothVelocityNormal (smoothConstantVelocity a)
  let P : SmoothData dim := ⟨fun z => M.1 z+b,M.2.add contDiff_const⟩
  let V := smoothVelocityNormal (smoothAffineVelocity a b c U)
  have hV : EqOn V.1 (fun z => 1*P.1 z+c*(smoothVelocityNormal U).1 z) (standardSphere dim) := by
    intro z hz
    have hN : ⟪z,z⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp hz,one_pow]
    change ⟪z,a+b • z+c • U.1 z⟫_ℝ = 1*(⟪z,a⟫_ℝ+b)+c*⟪z,U.1 z⟫_ℝ
    rw [inner_add_right,inner_add_right,real_inner_smul_right,real_inner_smul_right,hN,mul_one,one_mul]
  have hP : EqOn P.1 (fun z => 1*M.1 z+b*((1 : X dim → ℝ) z)) (standardSphere dim) := by
    intro z _
    change M.1 z+b = 1*M.1 z+b*1
    ring
  have h := smoothSphereTraceMul_affine P M ⟨1,contDiff_const⟩ 1 b hP
  rw [smoothSphereTraceMul_one,one_smul] at h
  change smoothSphereTraceMul V = smoothSphereTraceMul M+b • 1+c • smoothSphereTraceMul (smoothVelocityNormal U)
  rw [smoothSphereTraceMul_affine V P (smoothVelocityNormal U) 1 c hV,one_smul,h]

theorem smoothSphereVelocityTangent_radial :
    smoothSphereVelocityTangent (dim:=dim) ⟨id,contDiff_id⟩ = 0 := by
  ext u : 1
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let g : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  apply Subtype.ext
  funext z
  change (smoothSphereVelocityTangent ⟨id,contDiff_id⟩ (smoothSphereTrace g)).1 z = 0
  rw [smoothSphereVelocityTangent_apply]
  change (∑ i,∑ j,sphereRotationDerivative i j (fun x => g.1 x*(x i*x j)) z) = 0
  let S := ∑ i,∑ j,sphereRotationDerivative i j (fun x => g.1 x*(x i*x j)) z
  have hNeg : S = -S := by
    conv_lhs => rw [show S = ∑ i,∑ j,sphereRotationDerivative i j (fun x => g.1 x*(x i*x j)) z from rfl,
      Finset.sum_comm]
    rw [show -S = ∑ i,∑ j,-sphereRotationDerivative i j (fun x => g.1 x*(x i*x j)) z from by
      dsimp only [S]; simp only [Finset.sum_neg_distrib]]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show (fun x => g.1 x*(x j*x i)) = fun x => g.1 x*(x i*x j) from funext (fun x => by ring)]
    unfold sphereRotationDerivative
    rw [show rotationVector j i z = -rotationVector i j z from (neg_sub _ _).symm,map_neg]
  change S = 0
  linarith only [hNeg]

theorem smoothSphereVelocityTangent_affine (a : X dim) (b c : ℝ) (U : SmoothBallVelocity dim) :
    smoothSphereVelocityTangent (smoothAffineVelocity a b c U) =
      smoothSphereVelocityTangent (smoothConstantVelocity a)+c • smoothSphereVelocityTangent U := by
  let Z : SmoothBallVelocity dim := ⟨id,contDiff_id⟩
  let L := smoothConstantVelocity a
  let V := smoothAffineVelocity a b c U
  have hM (i j : Fin dim) :
      smoothSphereTraceMul (smoothVelocityAngular V i j) =
        smoothSphereTraceMul (smoothVelocityAngular L i j)+b • smoothSphereTraceMul (smoothVelocityAngular Z i j)+
          c • smoothSphereTraceMul (smoothVelocityAngular U i j) := by
    let P : SmoothData dim := ⟨fun z => (smoothVelocityAngular L i j).1 z+b*(smoothVelocityAngular Z i j).1 z,
      (smoothVelocityAngular L i j).2.add ((smoothVelocityAngular Z i j).2.const_smul b)⟩
    have hP : EqOn P.1 (fun z => 1*(smoothVelocityAngular L i j).1 z+
        b*(smoothVelocityAngular Z i j).1 z) (standardSphere dim) := by
      intro z _
      dsimp only [P]
      rw [one_mul]
    have hV : EqOn (smoothVelocityAngular V i j).1 (fun z => 1*P.1 z+
        c*(smoothVelocityAngular U i j).1 z) (standardSphere dim) := by
      intro z _
      change z i*(a+b • z+c • U.1 z) j = 1*(z i*a j+b*(z i*z j))+c*(z i*U.1 z j)
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [smoothSphereTraceMul_affine _ P _ 1 c hV,smoothSphereTraceMul_affine P _ _ 1 b hP,one_smul,one_smul]
  change smoothSphereVelocityTangent V = smoothSphereVelocityTangent L+c • smoothSphereVelocityTangent U
  have hZero : (∑ i,∑ j,smoothSphereTraceRotation i j*smoothSphereTraceMul (smoothVelocityAngular Z i j)) = 0 :=
    smoothSphereVelocityTangent_radial
  unfold smoothSphereVelocityTangent
  simp only [hM,mul_add,mul_smul_comm,Finset.sum_add_distrib,Finset.smul_sum]
  simp only [← Finset.smul_sum,hZero,smul_zero,add_zero]

theorem smoothSphereGaussAdjoint_affineTaylor
    (B L Q R H₂ : Module.End ℝ (SmoothSphereTrace dim)) (r b : ℝ)
    (a : X dim) (U : SmoothBallVelocity dim) :
    let S := B+r • (L*B+Q)+r^2 • R
    let H := 1-r • L+r^2 • H₂
    let F := Q-(B*L-L*B)
    let G := B*H₂+(L*B+Q)*(-L+r • H₂)+R*H
    let M := smoothSphereTraceMul (smoothVelocityNormal (smoothConstantVelocity a))
    let T := smoothSphereGaussAdjoint B (smoothConstantVelocity a)
    smoothSphereGaussAdjoint (S*H) (smoothAffineVelocity a b (r^2) U) =
      T+b • B+r • (F*M+b • F)+
        r^2 • (G*(M+b • 1)+(S*H)*smoothSphereTraceMul (smoothVelocityNormal U)-
          smoothSphereVelocityTangent U) := by
  dsimp only
  conv_lhs =>
    rw [smoothSphereGaussAdjoint,smoothSphereVelocityNormal_affine,smoothSphereVelocityTangent_affine]
  unfold smoothSphereGaussAdjoint
  have h := conormal_times_inverseWeight_expansion B L Q R H₂ r
  dsimp only at h
  exact moving_adjoint_affine_expansion
    ((B+r • (L*B+Q)+r^2 • R)*(1-r • L+r^2 • H₂)) B (Q-(B*L-L*B))
    (B*H₂+(L*B+Q)*(-L+r • H₂)+R*(1-r • L+r^2 • H₂))
    (smoothSphereTraceMul (smoothVelocityNormal (smoothConstantVelocity a)))
    (smoothSphereTraceMul (smoothVelocityNormal U))
    (smoothSphereVelocityTangent (smoothConstantVelocity a)) (smoothSphereVelocityTangent U) r b h

end CalderonN
