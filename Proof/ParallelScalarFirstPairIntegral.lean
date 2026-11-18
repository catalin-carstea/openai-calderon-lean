import Proof.ParallelScalarFirstCovariantPair
import Proof.SupportedHalfCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma integrable_fderiv_apply_eq_zero_of_support (f : X → ℝ) (hf : ContDiff ℝ ∞ f)
    (S : Set X) (hS : IsCompact S) (h0 : ∀ x ∉ S,f x=0) (a : X) :
    Integrable (fun x => fderiv ℝ f x a) ∧ (∫ x,fderiv ℝ f x a)=0 := by
  have hc : HasCompactSupport f := HasCompactSupport.intro hS h0
  have hd : ContDiff ℝ ∞ (fun x => fderiv ℝ f x a) :=
    (hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hDI : Integrable (fun x => fderiv ℝ f x a) :=
    hd.continuous.integrable_of_hasCompactSupport (hc.fderiv_apply (𝕜:=ℝ) a)
  have hFI : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hZero : Integrable (fun x => ⟪fderiv ℝ (fun _ : X => (1:ℝ)) x a,f x⟫_ℝ) := by
    apply (hDI.const_mul 0).congr
    exact Eventually.of_forall (fun x => by simp only [fderiv_const_apply,_root_.zero_apply,
      inner_zero_left,zero_mul])
  have hRight : Integrable (fun x => ⟪(1:ℝ),fderiv ℝ f x a⟫_ℝ) := by
    simpa only [Real.inner_apply,one_mul] using hDI
  have hBase : Integrable (fun x => ⟪(1:ℝ),f x⟫_ℝ) := by
    simpa only [Real.inner_apply,one_mul] using hFI
  have hIntegral := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B:=innerSL ℝ) (v:=a) hZero hRight hBase
    (fun _ _ => differentiableAt_const (1:ℝ)) (fun x _ => hf.differentiable (by simp) x)
  refine ⟨hDI,?_⟩
  change (∫ x,⟪(1:ℝ),fderiv ℝ f x a⟫_ℝ)=
    -(∫ x,⟪fderiv ℝ (fun _ : X => (1:ℝ)) x a,f x⟫_ℝ) at hIntegral
  simpa only [fderiv_const_apply,_root_.zero_apply,inner_zero_left,Real.inner_apply,one_mul,
    integral_zero,neg_zero] using hIntegral

def halfCovariantPairDensity (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U V : X → SphereSobolev (3/2:ℝ)) (a x : X) : ℝ :=
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  q x*(sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U x a) (C x (J (V x)))+
      sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (C x (halfSectionCovariantDerivativeL d V x a))+
      sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (halfOperatorCovariantDerivativeL d C Ch x a (V x)))+
    fderiv ℝ q x a*sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (C x (J (V x)))

/-- The packed covariant pairing derivative is integrable and integrates
to zero. Only the low coefficient is differentiated; the higher family
is used through its genuine graph and need not have chosen regularity. -/
theorem half_covariant_pair_weighted_data {Y : Set X} (hY : IsOpen Y) (d : Data)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y)
    (hCh : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch x)=
      (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (U V : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0V : ∀ x ∉ S,V x=0) (a : X) :
    IntegrableOn (halfCovariantPairDensity d q C Ch U V a) Y ∧
      (∫ x in Y,halfCovariantPairDensity d q C Ch U V a x)=0 := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let W := fun x => C x (J (V x))
  let F := fun x => q x*sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (W x)
  have hJV : ContDiff ℝ ∞ (fun x => J (V x)) := J.contDiff.comp hV
  have hJV0 (x : X) (hx : x ∉ S) : J (V x)=0 := by rw [h0V x hx,map_zero]
  have hW : ContDiff ℝ ∞ W := OperatorForms.contDiff_supported_operator_apply _ _ S hS.isClosed hJV hJV0
    (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
  have hW0 (x : X) (hx : x ∉ S) : W x=0 := by simp only [W,hJV0 x hx,map_zero]
  have hPair : ContDiff ℝ ∞ (fun x => sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (W x)) :=
    (J.contDiff.comp hU).inner ℝ hW
  have hPair0 (x : X) (hx : x ∉ S) : sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (W x)=0 := by
    simp only [sphereSobolevDualPairing,hW0 x hx,inner_zero_right]
  have hF : ContDiff ℝ ∞ F := OperatorForms.contDiff_supported_smul q _ S hS.isClosed hPair hPair0
    (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx)))
  have hF0 (x : X) (hx : x ∉ S) : F x=0 := by simp only [F,hPair0 x hx,mul_zero]
  have hDerivative := integrable_fderiv_apply_eq_zero_of_support F hF S hS hF0 a
  have hEq : (fun x => fderiv ℝ F x a)=ᵐ[volume.restrict Y]
      halfCovariantPairDensity d q C Ch U V a := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hqx := hq.contDiffAt (hY.mem_nhds hx)
    have hCx := hC.contDiffAt (hY.mem_nhds hx)
    have hPoint := half_covariant_pair_fderiv d C Ch U V x a hCx (hU.contDiffAt) (hV.contDiffAt) (hCh x hx)
    have hMul := fderiv_mul (hqx.differentiableAt (by simp)) (hPair.differentiable (by simp) x)
    have hMulA := DFunLike.congr_fun hMul a
    change fderiv ℝ F x a=_ at hMulA
    rw [hMulA]
    simp only [halfCovariantPairDensity,F,W,J,_root_.add_apply,_root_.smul_apply,smul_eq_mul,
      hPoint]
    ring
  refine ⟨hDerivative.1.integrableOn.congr hEq,?_⟩
  calc
    _ = ∫ x in Y,fderiv ℝ F x a := integral_congr_ae hEq.symm
    _ = ∫ x,fderiv ℝ F x a := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      OperatorForms.directional_eq_zero_off F S hS.isClosed hF0 a x (fun hs => hx (hSY hs)))
    _ = 0 := hDerivative.2

end ShrinkingSpheres.ParallelEnergy
