import Proof.ParallelNormAssemblyReservedQuadraticPair
import Proof.ParallelScalarFirstPairIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Weak left-source product rule: the left family is smooth only at its
actual H1/2 endpoint. Its H3/2 value is an explicit genuine pointwise lift;
no smoothness of that chosen higher lift is assumed. -/
theorem quadratic_weak_left_pair_fderiv (d : Data)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Z : X → SphereSobolev (1/2:ℝ)) (V : X → SphereSobolev (5/2:ℝ)) (y a : X)
    (hC : ContDiffAt ℝ ∞ C y) (hZ : ContDiffAt ℝ ∞ Z y) (hV : ContDiffAt ℝ ∞ V y)
    (z : SphereSobolev (3/2:ℝ))
    (hz : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) z=Z y) :
    fderiv ℝ (fun x => sphereSobolevDualPairing (1/2:ℝ) (Z x)
      (C x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V x)))) y a=
      sphereSobolevDualPairing (1/2:ℝ) (fderiv ℝ Z y a-frameAngularConnectionHigherL d y a z)
        (C y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V y)))+
      sphereSobolevDualPairing (1/2:ℝ) (Z y) (C y (fiveHalfSectionCovariantDerivativeL d V y a))+
      sphereSobolevDualPairing (3/2:ℝ) z (quadraticOperatorCovariantDerivativeL d C y a (V y)) := by
  let K := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  have hKV := K.hasFDerivAt.comp y (hV.differentiableAt (by simp)).hasFDerivAt
  have hCV := (hC.differentiableAt (by simp)).hasFDerivAt.clm_apply hKV
  have hRaw := fderiv_inner_apply ℝ (hZ.differentiableAt (by simp)) hCV.differentiableAt a
  rw [hCV.fderiv] at hRaw
  simp only [ContinuousLinearMap.comp_apply,_root_.add_apply,ContinuousLinearMap.flip_apply,
    inner_add_right,Function.comp_apply] at hRaw
  have hInc1 := quadratic_dual_inclusion_pair z ((fderiv ℝ C y a) (K (V y)))
  have hInc2 := quadratic_dual_inclusion_pair z (C y (frameAngularConnectionFiveHalfL d y a (V y)))
  rw [hz] at hInc1 hInc2
  have hConn := quadratic_dual_connection_pair d y a z (C y (K (V y)))
  simp only [fiveHalfSectionCovariantDerivativeL,quadraticOperatorCovariantDerivativeL,
    ContinuousLinearMap.comp_apply,_root_.add_apply,_root_.sub_apply,map_sub]
  simp only [sphereSobolevDualPairing,inner_sub_left,inner_add_right,inner_sub_right] at hInc1 hInc2 hConn ⊢
  change fderiv ℝ (fun x => ⟪Z x,C x (K (V x))⟫_ℝ) y a=_ at hRaw ⊢
  dsimp only [K] at hRaw hInc1 hInc2 hConn ⊢
  rw [hInc1,hInc2,hConn]
  linarith only [hRaw]

def quadraticWeakLeftPairDensity (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Z : X → SphereSobolev (1/2:ℝ)) (ZH : X → SphereSobolev (3/2:ℝ))
    (V : X → SphereSobolev (5/2:ℝ)) (a x : X) : ℝ :=
  q x*(sphereSobolevDualPairing (1/2:ℝ) (fderiv ℝ Z x a-frameAngularConnectionHigherL d x a (ZH x))
      (C x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V x)))+
    sphereSobolevDualPairing (1/2:ℝ) (Z x) (C x (fiveHalfSectionCovariantDerivativeL d V x a))+
    sphereSobolevDualPairing (3/2:ℝ) (ZH x) (quadraticOperatorCovariantDerivativeL d C x a (V x)))+
  fderiv ℝ q x a*sphereSobolevDualPairing (1/2:ℝ) (Z x)
    (C x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V x)))

/-- The weak-left covariant Green datum integrates to zero. The chosen
higher left family is used only through its genuine value graph on Y,
so no regularity is manufactured for arbitrary coherent packet choices. -/
theorem quadratic_weak_left_pair_weighted_data {Y : Set X} (hY : IsOpen Y) (d : Data)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hC : ContDiffOn ℝ ∞ C Y)
    (Z : X → SphereSobolev (1/2:ℝ)) (ZH : X → SphereSobolev (3/2:ℝ))
    (hZH : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (ZH x)=Z x)
    (V : X → SphereSobolev (5/2:ℝ)) (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hZ0 : ∀ x ∉ S,Z x=0) (hV0 : ∀ x ∉ S,V x=0) (a : X) :
    IntegrableOn (quadraticWeakLeftPairDensity d q C Z ZH V a) Y ∧
      (∫ x in Y,quadraticWeakLeftPairDensity d q C Z ZH V a x)=0 := by
  let K := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let W := fun x => C x (K (V x))
  let F := fun x => q x*sphereSobolevDualPairing (1/2:ℝ) (Z x) (W x)
  have hKV : ContDiff ℝ ∞ (fun x => K (V x)) := K.contDiff.comp hV
  have hKV0 (x : X) (hx : x ∉ S) : K (V x)=0 := by rw [hV0 x hx,map_zero]
  have hW : ContDiff ℝ ∞ W := OperatorForms.contDiff_supported_operator_apply _ _ S hS.isClosed hKV hKV0
    (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
  have hW0 (x : X) (hx : x ∉ S) : W x=0 := by simp only [W,hKV0 x hx,map_zero]
  have hPair : ContDiff ℝ ∞ (fun x => sphereSobolevDualPairing (1/2:ℝ) (Z x) (W x)) := hZ.inner ℝ hW
  have hPair0 (x : X) (hx : x ∉ S) : sphereSobolevDualPairing (1/2:ℝ) (Z x) (W x)=0 := by
    simp only [sphereSobolevDualPairing,hW0 x hx,inner_zero_right]
  have hF : ContDiff ℝ ∞ F := OperatorForms.contDiff_supported_smul q _ S hS.isClosed hPair hPair0
    (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx)))
  have hF0 (x : X) (hx : x ∉ S) : F x=0 := by simp only [F,hPair0 x hx,mul_zero]
  have hDerivative := integrable_fderiv_apply_eq_zero_of_support F hF S hS hF0 a
  have hEq : (fun x => fderiv ℝ F x a)=ᵐ[volume.restrict Y]
      quadraticWeakLeftPairDensity d q C Z ZH V a := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hPoint := quadratic_weak_left_pair_fderiv d C Z V x a
      (hC.contDiffAt (hY.mem_nhds hx)) hZ.contDiffAt hV.contDiffAt (ZH x) (hZH x hx)
    have hMul := fderiv_mul ((hq.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      (hPair.differentiable (by simp) x)
    have hMulA := DFunLike.congr_fun hMul a
    change fderiv ℝ F x a=_ at hMulA
    rw [hMulA]
    simp only [quadraticWeakLeftPairDensity,F,W,K,_root_.add_apply,_root_.smul_apply,smul_eq_mul,hPoint]
    ring
  refine ⟨hDerivative.1.integrableOn.congr hEq,?_⟩
  calc
    _ = ∫ x in Y,fderiv ℝ F x a := integral_congr_ae hEq.symm
    _ = ∫ x,fderiv ℝ F x a := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      OperatorForms.directional_eq_zero_off F S hS.isClosed hF0 a x (fun hs => hx (hSY hs)))
    _ = 0 := hDerivative.2

end ShrinkingSpheres.ParallelEnergy
