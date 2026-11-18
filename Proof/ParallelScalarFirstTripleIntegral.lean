import Proof.ParallelScalarFirstTriplePoint
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

def halfCovariantThirdDensity (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (H : X → X → SphereSobolev (3/2:ℝ)) (a b c x : X) : ℝ :=
  q x*sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d (H b) x a)
    (C x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H c x)))

def halfCovariantThirdRemainder (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (H : X → X → SphereSobolev (3/2:ℝ))
    (R : X → X → X → SphereSobolev (1/2:ℝ)) (a b c x : X) : ℝ :=
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num);
  -fderiv ℝ q x a*halfPair C (H b) (H c) x-
    fderiv ℝ q x b*halfPair C (H a) (H c) x+
    fderiv ℝ q x c*halfPair C (H a) (H b) x-
    q x*halfPairCoefficientDerivative d C Ch (H b) (H c) x a-
    q x*halfPairCoefficientDerivative d C Ch (H a) (H c) x b+
    q x*halfPairCoefficientDerivative d C Ch (H a) (H b) x c+
    q x*sphereSobolevDualPairing (1/2:ℝ) (R a b x) (C x (J (H c x)))+
    q x*sphereSobolevDualPairing (1/2:ℝ) (R c b x) (C x (J (H a x)))-
    q x*sphereSobolevDualPairing (1/2:ℝ) (R a c x) (C x (J (H b x)))

/-- Complete integrated operator-valued third-base reduction. The final
remainder has only first section derivatives, one covariant coefficient
jet, relative scalar-weight derivatives and the physical curvature.
The theorem never bounds a moving-frame connection coefficient. -/
theorem symmetric_half_covariant_third_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y)
    (hCh : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch x)=
      (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hSym : ∀ x ∈ Y,(C x).adjoint=C x)
    (H : X → X → SphereSobolev (3/2:ℝ)) (hH : ∀ v,ContDiff ℝ ∞ (H v))
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hH0 : ∀ v x,x ∉ S → H v x=0)
    (R : X → X → X → SphereSobolev (1/2:ℝ))
    (hR : ∀ x ∈ Y,∀ v w,halfSectionCovariantDerivativeL d (H w) x v-
      halfSectionCovariantDerivativeL d (H v) x w=R v w x) (a b c : X) :
    IntegrableOn (halfCovariantThirdDensity d q C H a b c) Y ∧
      IntegrableOn (halfCovariantThirdRemainder d q C Ch H R a b c) Y ∧
      2*(∫ x in Y,halfCovariantThirdDensity d q C H a b c x)=
        ∫ x in Y,halfCovariantThirdRemainder d q C Ch H R a b c x := by
  let T := halfCovariantThirdDensity d q C H a b c
  let Rem := halfCovariantThirdRemainder d q C Ch H R a b c
  let G1 := halfCovariantPairDensity d q C Ch (H b) (H c) a
  let G2 := halfCovariantPairDensity d q C Ch (H a) (H c) b
  let G3 := halfCovariantPairDensity d q C Ch (H a) (H b) c
  have hG1 := half_covariant_pair_weighted_data hY d q hq C Ch hC hCh
    (H b) (H c) (hH b) (hH c) S hS hSY (hH0 b) (hH0 c) a
  have hG2 := half_covariant_pair_weighted_data hY d q hq C Ch hC hCh
    (H a) (H c) (hH a) (hH c) S hS hSY (hH0 a) (hH0 c) b
  have hG3 := half_covariant_pair_weighted_data hY d q hq C Ch hC hCh
    (H a) (H b) (hH a) (hH b) S hS hSY (hH0 a) (hH0 b) c
  change IntegrableOn G1 Y ∧ (∫ x in Y,G1 x)=0 at hG1
  change IntegrableOn G2 Y ∧ (∫ x in Y,G2 x)=0 at hG2
  change IntegrableOn G3 Y ∧ (∫ x in Y,G3 x)=0 at hG3
  have hDH := contDiff_supported_halfSectionCovariantDerivative hY d hg hK he (H b) (hH b)
    S hS.isClosed hSY (hH0 b) a
  have hJH : ContDiff ℝ ∞ (fun x => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H c x)) :=
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).contDiff.comp (hH c)
  have hJH0 (x : X) (hx : x ∉ S) : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H c x)=0 := by
    rw [hH0 c x hx,map_zero]
  have hTI : IntegrableOn T Y := by
    have hh := OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) q
      (fun x => halfSectionCovariantDerivativeL d (H b) x a)
      (fun x => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H c x)) C S hS
      (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx))) hDH.1 hJH hJH0
      (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
    exact hh.integrableOn
  have hPoint : Rem =ᵐ[volume.restrict Y] (fun x => 2*T x-G1 x-G2 x+G3 x) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
    let B := fun (u v : SphereSobolev (1/2:ℝ)) => sphereSobolevDualPairing (1/2:ℝ) u (C x v)
    have hB (u v : SphereSobolev (1/2:ℝ)) : B u v=B v u := by
      dsimp only [B,sphereSobolevDualPairing]
      calc
        _ = ⟪(C x).adjoint u,v⟫_ℝ := ((C x).adjoint_inner_left v u).symm
        _ = _ := by rw [hSym x hx,real_inner_comm]
    have hSub (u v w : SphereSobolev (1/2:ℝ)) : B (u-v) w=B u w-B v w := inner_sub_left _ _ _
    have hAlg := symmetric_pair_second_triple_algebra B hB hSub
      (fun v => J (H v x)) (fun v w => halfSectionCovariantDerivativeL d (H w) x v)
      (fun v w => R v w x) (hR x hx) a b c
    dsimp only [Rem,T,G1,G2,G3,halfCovariantThirdRemainder,halfCovariantThirdDensity,
      halfCovariantPairDensity,halfPair,halfPairCoefficientDerivative,B,J] at hAlg ⊢
    linear_combination -q x*hAlg
  have hRemI : IntegrableOn Rem Y :=
    ((((hTI.const_mul 2).sub hG1.1).sub hG2.1).add hG3.1).congr hPoint.symm
  have hIntegral : (∫ x in Y,Rem x)=2*(∫ x in Y,T x) := by
    calc
      _ = ∫ x in Y,2*T x-G1 x-G2 x+G3 x := integral_congr_ae hPoint
      _ = (∫ x in Y,2*T x-G1 x-G2 x)+(∫ x in Y,G3 x) :=
        integral_add (((hTI.const_mul 2).sub hG1.1).sub hG2.1) hG3.1
      _ = ((∫ x in Y,2*T x)-(∫ x in Y,G1 x)-(∫ x in Y,G2 x))+(∫ x in Y,G3 x) := by
        calc
          _ = ((∫ x in Y,2*T x-G1 x)-(∫ x in Y,G2 x))+(∫ x in Y,G3 x) :=
            congrArg (fun r : ℝ => r+(∫ x in Y,G3 x))
              (integral_sub ((hTI.const_mul 2).sub hG1.1) hG2.1)
          _ = _ := congrArg (fun r : ℝ => r-(∫ x in Y,G2 x)+(∫ x in Y,G3 x))
            (integral_sub (hTI.const_mul 2) hG1.1)
      _ = _ := by rw [integral_const_mul,hG1.2,hG2.2,hG3.2];ring
  exact ⟨hTI,hRemI,hIntegral.symm⟩

end ShrinkingSpheres.ParallelEnergy
