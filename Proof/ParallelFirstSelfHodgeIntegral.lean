import Proof.ParallelFirstSelfHodgePair
import Proof.FrameCurvatureSobolevSmoothness
import Proof.LocalSupportedOperatorPairing

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

def balancedHalfHodgePairDensity (d : Data) (q : X → ℝ)
    (LR LS : X → SphereSobolev (1/2:ℝ)) (HR HS : X → SphereSobolev (3/2:ℝ)) (a b y : X) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  q y*(⟪Z (balancedPositiveHalfDerivative d LR HR y b),Z (balancedPositiveHalfDerivative d LS HS y a)⟫_ℝ-
    ⟪Z (balancedPositiveHalfDerivative d LR HR y a),Z (balancedPositiveHalfDerivative d LS HS y b)⟫_ℝ)

def balancedHalfHodgePairRemainder (d : Data) (q : X → ℝ)
    (LR LS : X → SphereSobolev (1/2:ℝ)) (a b y : X) : ℝ :=
  q y*sphereSobolevDualPairing (1/2:ℝ) (LR y)
      (frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame y a b (LS y))+
    fderiv ℝ q y a*sphereSobolevDualPairing (1/2:ℝ) (LR y) (weakHalfSourceCovariantDerivative d LS y b)-
    fderiv ℝ q y b*sphereSobolevDualPairing (1/2:ℝ) (LR y) (weakHalfSourceCovariantDerivative d LS y a)

/-- A covariant Hodge exchange through the genuine balanced endpoints.
Only actual LOWER sources are smooth; higher witnesses need no regularity. -/
theorem balanced_half_hodge_pair_integral {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ k,ContDiffOn ℝ ∞ (fun x => d.frame x k) Y)
    (hFrame : ∀ x ∈ Y,∀ k l,metricPair d.γ x (d.frame x k) (d.frame x l)=if k=l then 1 else 0)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (LR LS : X → SphereSobolev (1/2:ℝ)) (HR HS : X → SphereSobolev (3/2:ℝ))
    (hLR : ContDiff ℝ ∞ LR) (hLS : ContDiff ℝ ∞ LS)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hLR0 : ∀ x ∉ S,LR x=0) (hLS0 : ∀ x ∉ S,LS x=0)
    (hHR : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (HR x)=LR x)
    (hHS : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (HS x)=LS x)
    (a b : X) :
    IntegrableOn (balancedHalfHodgePairDensity d q LR LS HR HS a b) Y ∧
      IntegrableOn (balancedHalfHodgePairRemainder d q LR LS a b) Y ∧
      (∫ y in Y,balancedHalfHodgePairDensity d q LR LS HR HS a b y)=
        ∫ y in Y,balancedHalfHodgePairRemainder d q LR LS a b y := by
  let V := fun v x => weakHalfSourceCovariantDerivative d LS x v
  let G := fun v x => balancedPositiveHalfDerivative d LS HS x v
  have hV (v : X) : ContDiff ℝ ∞ (V v) ∧ ∀ x ∉ S,V v x=0 := by
    simpa only [V,weakHalfSourceCovariantDerivative_eq_graded] using
      contDiff_supported_gradedSphereSectionCovariantDerivative hY (1/2:ℝ) d hg hK he LS hLS S hS.isClosed hSY hLS0 v
  have hG (v x : X) (hx : x ∈ Y) : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (G v x)=V v x :=
    balanced_positive_half_derivative_weak_graph d LS HS x v (hHS x hx)
  let F := balancedSourceHalfPairDensity d q LR HR (V a) (G a) b
  let Q := balancedSourceHalfPairDensity d q LR HR (V b) (G b) a
  have hF := balanced_source_half_pair_weighted_data hY d q hq LR HR (V a) (G a)
    hLR (hV a).1 S hS hSY hLR0 (hV a).2 hHR (hG a) b
  have hQ := balanced_source_half_pair_weighted_data hY d q hq LR HR (V b) (G b)
    hLR (hV b).1 S hS hSY hLR0 (hV b).2 hHR (hG b) a
  have hDq (v : X) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ q x v) Y :=
    (hq.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hC : IntegrableOn (fun x => q x*sphereSobolevDualPairing (1/2:ℝ) (LR x)
      (frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame x a b (LS x))) Y := by
    have hh := OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) q LR LS
      (fun x => frameCurvatureSobolevL (1/2:ℝ) d.γ d.frame x a b) S hS
      (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx))) hLR hLS hLS0
      (fun x hx => (hg.contDiffOn_frameCurvatureSobolevL hY hK d.frame he hFrame (1/2:ℝ) a b).contDiffAt
        (hY.mem_nhds (hSY hx)))
    exact hh.integrableOn
  have hD (v w : X) : IntegrableOn (fun x => fderiv ℝ q x v*sphereSobolevDualPairing (1/2:ℝ) (LR x) (V w x)) Y := by
    have hh := OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ)
      (fun x => fderiv ℝ q x v) LR (V w) (fun _ => ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) S hS
      (fun x hx => (hDq v).contDiffAt (hY.mem_nhds (hSY hx))) hLR (hV w).1 (hV w).2
      (fun _ _ => contDiffAt_const)
    exact hh.integrableOn
  have hR : IntegrableOn (balancedHalfHodgePairRemainder d q LR LS a b) Y := (hC.add (hD a b)).sub (hD b a)
  have hEq : balancedHalfHodgePairDensity d q LR LS HR HS a b=ᵐ[volume.restrict Y]
      fun x => balancedHalfHodgePairRemainder d q LR LS a b x+F x-Q x := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    exact balanced_half_hodge_pair_identity hY d hg hK he hFrame q LR LS HR HS hLS.contDiffOn hHS hx a b
  refine ⟨((hR.add hF.1).sub hQ.1).congr hEq.symm,hR,?_⟩
  rw [integral_congr_ae hEq]
  change (∫ x in Y,(balancedHalfHodgePairRemainder d q LR LS a b+F-Q) x)=_
  have hFI : IntegrableOn F Y := hF.1
  have hQI : IntegrableOn Q Y := hQ.1
  have hFZ : (∫ x in Y,F x)=0 := hF.2
  have hQZ : (∫ x in Y,Q x)=0 := hQ.2
  have hTotal := (integral_sub (hR.add hFI) hQI).trans
    (congrArg (fun t => t-∫ x in Y,Q x) (integral_add hR hFI))
  simpa only [Pi.sub_apply,Pi.add_apply,hFZ,hQZ,add_zero,sub_zero] using hTotal


end ShrinkingSpheres.ParallelEnergy
