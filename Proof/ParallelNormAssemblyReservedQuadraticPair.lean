import Proof.ParallelNormAssemblyReservedQuadraticJetAlgebra
import Proof.ReflectedFirstCorrectionAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

def fiveHalfSectionCovariantDerivativeL (d : Data) (U : X → SphereSobolev (5/2:ℝ))
    (y a : X) : SphereSobolev (3/2:ℝ) :=
  sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (fderiv ℝ U y a)-
    frameAngularConnectionFiveHalfL d y a (U y)

lemma frame_connection_five_half_compatible (d : Data) (y a : X) (u : SphereSobolev (5/2:ℝ)) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (frameAngularConnectionFiveHalfL d y a u)=
      frameAngularConnectionHigherL d y a (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) u) := by
  simp only [frameAngularConnectionFiveHalfL,frameAngularConnectionHigherL,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simpa only [sphereSobolevInclusionL,show (5/2:ℝ)-1=3/2 by norm_num,
    show (3/2:ℝ)-1=1/2 by norm_num] using
    (sphereSobolevRotationL_inclusion_apply (5/2:ℝ) (3/2:ℝ) (by norm_num) i j u).symm

/-- Reflection of the explicit normalized rotation formulas, at their
actual source/target grades. This is an adjunction identity, not an
inference of higher regularity from an underlying carrier. -/
lemma frame_connection_negative_half_adjoint (d : Data) (y a : X) :
    (frameAngularConnectionNegativeHalfL d y a).adjoint= -frameAngularConnectionHigherL d y a := by
  change (frameAngularConnectionHalfL d y a).adjoint= -frameAngularConnectionHalfL d y a
  exact frameAngularConnectionHalfL_adjoint d y a

lemma quadratic_dual_inclusion_pair (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev (-(1/2:ℝ))) :
    sphereSobolevDualPairing (3/2:ℝ) u
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) v)=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) v := by
  have hNeg := sphereSobolevInclusionL_normalized_gap_one (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num) (by norm_num)
  have hPos := sphereSobolevInclusionL_normalized_gap_one (3/2:ℝ) (1/2:ℝ) (by norm_num) (by norm_num)
  simp only [sphereSobolevDualPairing,hNeg,hPos]
  exact ((sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).adjoint_inner_left v u).symm.trans
    (by rw [sphereSobolevHalfNegativeInclusion_adjoint])

lemma quadratic_dual_connection_pair (d : Data) (y a : X)
    (u : SphereSobolev (3/2:ℝ)) (v : SphereSobolev (-(1/2:ℝ))) :
    sphereSobolevDualPairing (3/2:ℝ) u (frameAngularConnectionNegativeHalfL d y a v)=
      -sphereSobolevDualPairing (1/2:ℝ) (frameAngularConnectionHigherL d y a u) v := by
  dsimp only [sphereSobolevDualPairing]
  rw [←(frameAngularConnectionNegativeHalfL d y a).adjoint_inner_left v u,
    frame_connection_negative_half_adjoint]
  simp only [_root_.neg_apply,inner_neg_left]

/-- Covariant Leibniz formula for a genuine TWO-angular-order potential
pair. Negative inclusions and connection adjunction cancel exactly, before
norms. No second HIGH operator derivative is needed. -/
theorem quadratic_covariant_pair_fderiv (d : Data)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U V : X → SphereSobolev (5/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hU : ContDiffAt ℝ ∞ U y) (hV : ContDiffAt ℝ ∞ V y) :
    fderiv ℝ (fun x => sphereSobolevDualPairing (1/2:ℝ)
      (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U x))
      (C x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V x)))) y a=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (fiveHalfSectionCovariantDerivativeL d U y a))
        (C y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V y)))+
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
        (C y (fiveHalfSectionCovariantDerivativeL d V y a))+
      sphereSobolevDualPairing (3/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))
        (quadraticOperatorCovariantDerivativeL d C y a (V y)) := by
  let J := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num)
  let K := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  have hJU := J.hasFDerivAt.comp y (hU.differentiableAt (by simp)).hasFDerivAt
  have hKV := K.hasFDerivAt.comp y (hV.differentiableAt (by simp)).hasFDerivAt
  have hCV := (hC.differentiableAt (by simp)).hasFDerivAt.clm_apply hKV
  have hRaw := fderiv_inner_apply ℝ hJU.differentiableAt hCV.differentiableAt a
  rw [hJU.fderiv,hCV.fderiv] at hRaw
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,ContinuousLinearMap.flip_apply,inner_add_right,Function.comp_apply] at hRaw
  have hInc1 := quadratic_dual_inclusion_pair (K (U y)) ((fderiv ℝ C y a) (K (V y)))
  have hInc2 := quadratic_dual_inclusion_pair (K (U y)) (C y (frameAngularConnectionFiveHalfL d y a (V y)))
  have hConn := quadratic_dual_connection_pair d y a (K (U y)) (C y (K (V y)))
  simp only [K,sphereSobolevInclusionL_trans_apply] at hInc1 hInc2
  simp only [fiveHalfSectionCovariantDerivativeL,quadraticOperatorCovariantDerivativeL,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,map_sub,sphereSobolevInclusionL_trans_apply,
    frame_connection_five_half_compatible]
  simp only [sphereSobolevDualPairing,inner_sub_left,inner_add_right,inner_sub_right] at hInc1 hInc2 hConn ⊢
  change fderiv ℝ (fun x => ⟪J (U x),C x (K (V x))⟫_ℝ) y a=_ at hRaw ⊢
  dsimp only [J,K] at hRaw hConn ⊢
  rw [hInc1,hInc2,hConn]
  linarith only [hRaw]

end ShrinkingSpheres.ParallelEnergy
