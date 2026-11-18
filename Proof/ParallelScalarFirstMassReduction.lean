import Proof.ParallelScalarFirstPairIntegral

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

def halfCovariantSecondMassDensity (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U V : X → SphereSobolev (3/2:ℝ)) (a x : X) : ℝ :=
  q x*sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U x))
    (C x (halfSectionCovariantDerivativeL d V x a))

def halfCovariantSecondMassRemainder (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U V : X → SphereSobolev (3/2:ℝ)) (a x : X) : ℝ :=
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num);
  -q x*(sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U x a) (C x (J (V x)))+
    sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (halfOperatorCovariantDerivativeL d C Ch x a (V x)))-
    fderiv ℝ q x a*sphereSobolevDualPairing (1/2:ℝ) (J (U x)) (C x (J (V x)))

/-- A single covariant Green operation reduces the scalar second/mass
pair to first section derivatives and one genuine coefficient derivative. -/
theorem half_covariant_second_mass_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y)
    (hCh : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch x)=
      (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (U V : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hU0 : ∀ x ∉ S,U x=0) (hV0 : ∀ x ∉ S,V x=0) (a : X) :
    IntegrableOn (halfCovariantSecondMassDensity d q C U V a) Y ∧
    IntegrableOn (halfCovariantSecondMassRemainder d q C Ch U V a) Y ∧
    (∫ x in Y,halfCovariantSecondMassDensity d q C U V a x)=
      ∫ x in Y,halfCovariantSecondMassRemainder d q C Ch U V a x := by
  let T := halfCovariantSecondMassDensity d q C U V a
  let R := halfCovariantSecondMassRemainder d q C Ch U V a
  let G := halfCovariantPairDensity d q C Ch U V a
  have hG := half_covariant_pair_weighted_data hY d q hq C Ch hC hCh U V hU hV S hS hSY hU0 hV0 a
  change IntegrableOn G Y ∧ (∫ x in Y,G x)=0 at hG
  have hDV := contDiff_supported_halfSectionCovariantDerivative hY d hg hK he V hV S hS.isClosed hSY hV0 a
  have hJU := (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).contDiff.comp hU
  have hTI : IntegrableOn T Y := by
    have hh := OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) q
      (fun x => sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U x))
      (fun x => halfSectionCovariantDerivativeL d V x a) C S hS
      (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx))) hJU hDV.1 hDV.2
      (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
    exact hh.integrableOn
  have hR : R=fun x => T x-G x := by
    funext x
    dsimp only [R,T,G,halfCovariantSecondMassDensity,halfCovariantSecondMassRemainder,halfCovariantPairDensity]
    ring
  change IntegrableOn T Y ∧ IntegrableOn R Y ∧ (∫ x in Y,T x)=∫ x in Y,R x
  refine ⟨hTI,by rw [hR];exact hTI.sub hG.1,?_⟩
  rw [hR,integral_sub hTI hG.1,hG.2,sub_zero]

end ShrinkingSpheres.ParallelEnergy
