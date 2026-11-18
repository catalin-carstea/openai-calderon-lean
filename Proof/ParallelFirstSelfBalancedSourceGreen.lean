import Proof.ParallelScalarFirstPairIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Positive half derivative with a genuine higher source, used only by
its point graph. Its selected higher family need not be smooth. -/
def balancedPositiveHalfDerivative (d : Data)
    (L : X → SphereSobolev (1/2:ℝ)) (H : X → SphereSobolev (3/2:ℝ)) (y a : X) : SphereSobolev (1/2:ℝ) :=
  fderiv ℝ L y a-frameAngularConnectionHigherL d y a (H y)

def balancedNegativeHalfDerivative (d : Data)
    (V : X → SphereSobolev (-(1/2:ℝ))) (L : X → SphereSobolev (1/2:ℝ)) (y a : X) : SphereSobolev (-(1/2:ℝ)) :=
  fderiv ℝ V y a-frameAngularConnectionHalfL d y a (L y)

/-- The actual frame connection cancels across two balanced source
endpoints, without differentiating either selected higher representative. -/
lemma balanced_source_half_connection_cancel (d : Data) (y a : X)
    (L : SphereSobolev (1/2:ℝ)) (H : SphereSobolev (3/2:ℝ))
    (V : SphereSobolev (-(1/2:ℝ))) (W : SphereSobolev (1/2:ℝ))
    (hH : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) H=L)
    (hW : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) W=V) :
    sphereSobolevDualPairing (1/2:ℝ) (frameAngularConnectionHigherL d y a H) V+
      sphereSobolevDualPairing (1/2:ℝ) L (frameAngularConnectionHalfL d y a W)=0 := by
  let I0 := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let R := frameAngularConnectionHalfL d y a
  have hR := DFunLike.congr_fun (frameAngularConnectionHigherL_compatible d y a) H
  simp only [ContinuousLinearMap.comp_apply,hH] at hR
  have hI : I0.adjoint=I0 := sphereSobolevHalfNegativeInclusion_adjoint
  have hRA : R.adjoint=-R := frameAngularConnectionHalfL_adjoint d y a
  have hi := I0.adjoint_inner_right (frameAngularConnectionHigherL d y a H) W
  rw [hI] at hi
  have hr := R.adjoint_inner_right L W
  rw [hRA] at hr
  simp only [_root_.neg_apply,inner_neg_right] at hr
  rw [←hW]
  dsimp only [sphereSobolevDualPairing]
  change ⟪frameAngularConnectionHigherL d y a H,I0 W⟫_ℝ+⟪L,R W⟫_ℝ=0
  change I0 (frameAngularConnectionHigherL d y a H)=R L at hR
  rw [hR] at hi
  linarith only [hi,hr]

/-- Leibniz for balanced positive/negative sources. Smoothness is required
only for the actual LOWER sources which are differentiated. -/
theorem balanced_source_half_pair_fderiv (d : Data)
    (L : X → SphereSobolev (1/2:ℝ)) (H : X → SphereSobolev (3/2:ℝ))
    (V : X → SphereSobolev (-(1/2:ℝ))) (W : X → SphereSobolev (1/2:ℝ)) (y a : X)
    (hL : DifferentiableAt ℝ L y) (hV : DifferentiableAt ℝ V y)
    (hH : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H y)=L y)
    (hW : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W y)=V y) :
    fderiv ℝ (fun x => sphereSobolevDualPairing (1/2:ℝ) (L x) (V x)) y a=
      sphereSobolevDualPairing (1/2:ℝ) (balancedPositiveHalfDerivative d L H y a) (V y)+
      sphereSobolevDualPairing (1/2:ℝ) (L y) (balancedNegativeHalfDerivative d V W y a) := by
  have hRaw := fderiv_inner_apply ℝ hL hV a
  have hCancel := balanced_source_half_connection_cancel d y a (L y) (H y) (V y) (W y) hH hW
  unfold balancedPositiveHalfDerivative balancedNegativeHalfDerivative sphereSobolevDualPairing
  simp only [inner_sub_left,inner_sub_right]
  dsimp only [sphereSobolevDualPairing] at hCancel
  linarith only [hRaw,hCancel]

def balancedSourceHalfPairDensity (d : Data) (q : X → ℝ)
    (L : X → SphereSobolev (1/2:ℝ)) (H : X → SphereSobolev (3/2:ℝ))
    (V : X → SphereSobolev (-(1/2:ℝ))) (W : X → SphereSobolev (1/2:ℝ)) (a x : X) : ℝ :=
  q x*(sphereSobolevDualPairing (1/2:ℝ) (balancedPositiveHalfDerivative d L H x a) (V x)+
      sphereSobolevDualPairing (1/2:ℝ) (L x) (balancedNegativeHalfDerivative d V W x a))+
    fderiv ℝ q x a*sphereSobolevDualPairing (1/2:ℝ) (L x) (V x)

/-- Genuine covariant Green for balanced sources whose higher choices
have no asserted regularity. The complete packed density is integrable
because it is the derivative of one smooth supported scalar flux. -/
theorem balanced_source_half_pair_weighted_data {Y : Set X} (hY : IsOpen Y) (d : Data)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (L : X → SphereSobolev (1/2:ℝ)) (H : X → SphereSobolev (3/2:ℝ))
    (V : X → SphereSobolev (-(1/2:ℝ))) (W : X → SphereSobolev (1/2:ℝ))
    (hL : ContDiff ℝ ∞ L) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hL0 : ∀ x ∉ S,L x=0) (hV0 : ∀ x ∉ S,V x=0)
    (hH : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H x)=L x)
    (hW : ∀ x ∈ Y,sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (W x)=V x)
    (a : X) :
    IntegrableOn (balancedSourceHalfPairDensity d q L H V W a) Y ∧
      (∫ x in Y,balancedSourceHalfPairDensity d q L H V W a x)=0 := by
  let P := fun x => sphereSobolevDualPairing (1/2:ℝ) (L x) (V x)
  let F := fun x => q x*P x
  have hP : ContDiff ℝ ∞ P := hL.inner ℝ hV
  have hP0 (x : X) (hx : x ∉ S) : P x=0 := by
    simp only [P,sphereSobolevDualPairing,hV0 x hx,inner_zero_right]
  have hF : ContDiff ℝ ∞ F := OperatorForms.contDiff_supported_smul q P S hS.isClosed hP hP0
    (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx)))
  have hF0 (x : X) (hx : x ∉ S) : F x=0 := by simp only [F,hP0 x hx,mul_zero]
  have hDerivative := integrable_fderiv_apply_eq_zero_of_support F hF S hS hF0 a
  have hEq : (fun x => fderiv ℝ F x a)=ᵐ[volume.restrict Y]
      balancedSourceHalfPairDensity d q L H V W a := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hqx := hq.contDiffAt (hY.mem_nhds hx)
    have hPoint := balanced_source_half_pair_fderiv d L H V W x a
      (hL.differentiable (by simp) x) (hV.differentiable (by simp) x) (hH x hx) (hW x hx)
    have hMul := DFunLike.congr_fun (fderiv_mul (hqx.differentiableAt (by simp))
      (hP.differentiable (by simp) x)) a
    change fderiv ℝ F x a=_ at hMul
    rw [hMul]
    simp only [balancedSourceHalfPairDensity,F,P,_root_.add_apply,_root_.smul_apply,smul_eq_mul,hPoint]
    ring
  refine ⟨hDerivative.1.integrableOn.congr hEq,?_⟩
  calc
    _ = ∫ x in Y,fderiv ℝ F x a := integral_congr_ae hEq.symm
    _ = ∫ x,fderiv ℝ F x a := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      OperatorForms.directional_eq_zero_off F S hS.isClosed hF0 a x (fun hs => hx (hSY hs)))
    _ = 0 := hDerivative.2

end ShrinkingSpheres.ParallelEnergy
