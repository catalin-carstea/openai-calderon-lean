module

public import Proof.CalderonN.HarmonicRotationCasimir
public import Proof.CalderonN.HarmonicDerivativeOperator

import Mathlib.Tactic

/-! Rotation covariance of harmonic lowering and raising, adapted from
the corresponding dimension-three harmonic block identities. -/

public section

noncomputable section
open Set MvPolynomial
open scoped InnerProductSpace ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic AngularPolynomial
variable {dim : ℕ} [NeZero dim]

lemma polynomialRotation_pderiv_commutator (i j a : I dim) (p : MvPolynomial (I dim) ℝ) :
    polynomialRotation i j (pderiv a p)-pderiv a (polynomialRotation i j p) =
      (if a=j then pderiv i p else 0)-(if a=i then pderiv j p else 0) := by
  classical
  simp only [polynomialRotation,map_sub,pderiv_mul,pderiv_X,Pi.single_apply]
  rw [pderiv_pderiv_comm a j,pderiv_pderiv_comm a i]
  by_cases haj : a=j <;> by_cases hai : a=i <;>
    simp_all only [eq_comm,ite_true,ite_false,mul_zero,mul_one,zero_mul,one_mul] <;> ring


lemma harmonicSphereRotation_derivative_commutator
    (hF : SphereFischerInner dim) (k : ℕ) (i j a : I dim) (u : harmonicSphereSubspace dim (k+1)) :
    harmonicSphereRotation k i j (harmonicDerivative hF k a u) -
      harmonicDerivative hF k a (harmonicSphereRotation (k+1) i j u) =
      (if a=j then harmonicDerivative hF k i u else 0) -
      (if a=i then harmonicDerivative hF k j u else 0) := by
  rcases harmonicPolynomialSphereMap_surjective (k+1) u with ⟨p,rfl⟩
  have hRot (n : ℕ) (s t : I dim) (q : harmonicHomogeneous dim n) :
      harmonicSphereRotation n s t (harmonicPolynomialSphereMap n q) =
        harmonicPolynomialSphereMap n
          ⟨polynomialRotation s t q,polynomialRotation_harmonic_all n s t q q.property⟩ := by
    rw [harmonicSphereRotation_apply_image]
    rfl
  have hDerivative (b : I dim) (q : harmonicHomogeneous dim (k+1)) :
      harmonicDerivative hF k b (harmonicPolynomialSphereMap (k+1) q) =
        harmonicPolynomialSphereMap k
          ⟨pderiv b (q : MvPolynomial (I dim) ℝ),pderiv_harmonicHomogeneous_succ k b q q.property⟩ := by
    rw [harmonicDerivative_apply_image]
    rfl
  simp only [hRot,hDerivative]
  apply Subtype.ext
  have hVal (P : Prop) [Decidable P] (z : harmonicSphereSubspace dim k) :
      ((if P then z else 0) : harmonicSphereSubspace dim k).val=(if P then z.val else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,Submodule.coe_zero]
  have hPolyI (P : Prop) [Decidable P] (z : MvPolynomial (I dim) ℝ) :
      polynomialSphereL2 (if P then z else 0)=(if P then polynomialSphereL2 z else 0) := by
    by_cases hP : P <;> simp only [hP,ite_true,ite_false,map_zero]
  simpa only [Submodule.coe_sub,Submodule.coe_zero,hVal,hPolyI,
    harmonicPolynomialSphereMap,LinearMap.codRestrict_apply,LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,map_sub,map_zero] using
    congrArg polynomialSphereL2 (polynomialRotation_pderiv_commutator i j a p)


lemma harmonicSphereRotation_raising_commutator
    (hF : SphereFischerInner dim) (k : ℕ) (i j a : I dim) (u : harmonicSphereSubspace dim k) :
    harmonicSphereRotation (k+1) i j (harmonicDerivativeAdjoint hF k a u) -
      harmonicDerivativeAdjoint hF k a (harmonicSphereRotation k i j u) =
      (if a=j then harmonicDerivativeAdjoint hF k i u else 0) -
      (if a=i then harmonicDerivativeAdjoint hF k j u else 0) := by
  apply ext_inner_right ℝ
  intro v
  have he := congrArg (fun z : harmonicSphereSubspace dim k => ⟪u,z⟫_ℝ)
    (harmonicSphereRotation_derivative_commutator hF k i j a v)
  have hs := inner_harmonicSphereRotation_skew k i j u (harmonicDerivative hF k a v)
  have ht := inner_harmonicSphereRotation_skew (k+1) i j (harmonicDerivativeAdjoint hF k a u) v
  rw [inner_harmonicDerivativeAdjoint] at ht
  have hConditionalAdjunction (P : Prop) [Decidable P] (b : I dim) :
      ⟪(if P then harmonicDerivativeAdjoint hF k b u else 0),v⟫_ℝ =
        ⟪u,(if P then harmonicDerivative hF k b v else 0)⟫_ℝ := by
    by_cases hP : P <;>
      simp only [hP,ite_true,ite_false,inner_zero_left,inner_zero_right,inner_harmonicDerivativeAdjoint]
  by_cases haj : a=j <;> by_cases hai : a=i <;>
    (try simp only [haj,hai] at hs ht) <;>
    simp only [haj,hai,ite_true,ite_false,inner_sub_right,inner_zero_right] at he <;>
    simp only [haj,hai,ite_true,ite_false,inner_sub_left,inner_zero_left,
      hConditionalAdjunction,inner_harmonicDerivativeAdjoint] <;> linarith

end CalderonN
