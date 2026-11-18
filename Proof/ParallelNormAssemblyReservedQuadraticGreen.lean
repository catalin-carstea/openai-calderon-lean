import Proof.ParallelNormAssemblyReservedQuadraticWeakPair
import Proof.ParallelNormAssemblyReservedFiveHalfSections

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

def quadraticWeakMassDensity (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Z : X → SphereSobolev (1/2:ℝ)) (V : X → SphereSobolev (5/2:ℝ)) (a x : X) : ℝ :=
  q x*sphereSobolevDualPairing (1/2:ℝ) (Z x) (C x (fiveHalfSectionCovariantDerivativeL d V x a))

def quadraticWeakMassRemainder (d : Data) (q : X → ℝ)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Z : X → SphereSobolev (1/2:ℝ)) (ZH : X → SphereSobolev (3/2:ℝ))
    (V : X → SphereSobolev (5/2:ℝ)) (a x : X) : ℝ :=
  -q x*(sphereSobolevDualPairing (1/2:ℝ) (fderiv ℝ Z x a-frameAngularConnectionHigherL d x a (ZH x))
      (C x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V x)))+
    sphereSobolevDualPairing (3/2:ℝ) (ZH x) (quadraticOperatorCovariantDerivativeL d C x a (V x)))-
  fderiv ℝ q x a*sphereSobolevDualPairing (1/2:ℝ) (Z x)
    (C x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (V x)))

/-- One genuine covariant Green operation for a complete two-angular-
order potential. The left source's higher lift is only a graph witness;
no chosen higher-family smoothness is assumed. All integrability precedes
integration, and all coefficient/connection terms are retained. -/
theorem quadratic_weak_mass_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hC : ContDiffOn ℝ ∞ C Y)
    (Z : X → SphereSobolev (1/2:ℝ)) (ZH : X → SphereSobolev (3/2:ℝ))
    (hZH : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (ZH x)=Z x)
    (V : X → SphereSobolev (5/2:ℝ)) (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hZ0 : ∀ x ∉ S,Z x=0) (hV0 : ∀ x ∉ S,V x=0) (a : X) :
    IntegrableOn (quadraticWeakMassDensity d q C Z V a) Y ∧
    IntegrableOn (quadraticWeakMassRemainder d q C Z ZH V a) Y ∧
    (∫ x in Y,quadraticWeakMassDensity d q C Z V a x)=
      ∫ x in Y,quadraticWeakMassRemainder d q C Z ZH V a x := by
  let T := quadraticWeakMassDensity d q C Z V a
  let R := quadraticWeakMassRemainder d q C Z ZH V a
  let G := quadraticWeakLeftPairDensity d q C Z ZH V a
  have hG := quadratic_weak_left_pair_weighted_data hY d q hq C hC Z ZH hZH V hZ hV S hS hSY hZ0 hV0 a
  change IntegrableOn G Y ∧ (∫ x in Y,G x)=0 at hG
  have hDV := contDiff_supported_five_half_covariant_derivative hY d hg hK he V hV S hS.isClosed hSY hV0 a
  have hTI : IntegrableOn T Y := by
    have hh := OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) q Z
      (fun x => fiveHalfSectionCovariantDerivativeL d V x a) C S hS
      (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx))) hZ hDV.1 hDV.2
      (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))
    exact hh.integrableOn
  have hR : R=fun x => T x-G x := by
    funext x
    dsimp only [R,T,G,quadraticWeakMassDensity,quadraticWeakMassRemainder,quadraticWeakLeftPairDensity]
    ring
  change IntegrableOn T Y ∧ IntegrableOn R Y ∧ (∫ x in Y,T x)=∫ x in Y,R x
  refine ⟨hTI,by rw [hR];exact hTI.sub hG.1,?_⟩
  rw [hR,integral_sub hTI hG.1,hG.2,sub_zero]

end ShrinkingSpheres.ParallelEnergy
