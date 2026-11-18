import Proof.ParallelNormAssemblyReservedHigherApply
import Proof.ParallelNormAssemblyReservedQuadraticGreen

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

def quadraticHigherPairDensity (d : Data) (q : X → ℝ)
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (a x : X) : ℝ :=
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let v := fiveHalfSectionCovariantDerivativeL d U x a
  q x*(sphereSobolevDualPairing (1/2:ℝ) (H x v) (C x u)+
    sphereSobolevDualPairing (1/2:ℝ) (H x u) (C x v))

def quadraticHigherPairRemainder (q : X → ℝ)
    (H N : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (C DQ : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U : X → SphereSobolev (5/2:ℝ)) (a x : X) : ℝ :=
  let u := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x);
  -q x*(sphereSobolevDualPairing (1/2:ℝ) (N x u) (C x u)+
    sphereSobolevDualPairing (1/2:ℝ) (H x u) (DQ x u))-
  fderiv ℝ q x a*sphereSobolevDualPairing (1/2:ℝ) (H x u) (C x u)

/-- Paired model/first versus potential leading Green operation. The two
horizontal orientations cancel before absolute values. Only FIRST genuine
HIGH coefficient jets are used; the higher left lift has no regularity premise. -/
theorem quadratic_higher_paired_mass_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) (a : X) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : X → ℝ) (hq : ContDiffOn ℝ ∞ q Y)
    (H : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (hH : ContDiffOn ℝ ∞ H Y)
    (C : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (hC : ContDiffOn ℝ ∞ C Y)
    (N : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (DQ : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hN : ∀ x ∈ Y,higherOperatorCovariantDerivativeL d H x a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        ((N x).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (hDQ : ∀ x ∈ Y,quadraticOperatorCovariantDerivativeL d C x a=
      (sphereSobolevInclusionL (-(1/2:ℝ)) (-(3/2:ℝ)) (by norm_num)).comp
        ((DQ x).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))))
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (ZH : X → SphereSobolev (3/2:ℝ))
    (hZH : ∀ x ∈ Y,sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (ZH x)=
      H x (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)))
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (quadraticHigherPairDensity d q H C U a) Y ∧
    IntegrableOn (quadraticHigherPairRemainder q H N C DQ U a) Y ∧
    (∫ x in Y,quadraticHigherPairDensity d q H C U a x)=
      ∫ x in Y,quadraticHigherPairRemainder q H N C DQ U a x := by
  let J := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let u := fun x => J (U x)
  let Z := fun x => H x (u x)
  let A := fun x => q x*sphereSobolevDualPairing (1/2:ℝ)
    (H x (fiveHalfSectionCovariantDerivativeL d U x a)) (C x (u x))
  have hu : ContDiff ℝ ∞ u := J.contDiff.comp hU
  have hu0 (x : X) (hx : x ∉ S) : u x=0 := by simp only [u,hU0 x hx,map_zero]
  have hZ : ContDiff ℝ ∞ Z := OperatorForms.contDiff_supported_operator_apply u H S hS.isClosed hu hu0
    (fun x hx => hH.contDiffAt (hY.mem_nhds (hSY hx)))
  have hZ0 (x : X) (hx : x ∉ S) : Z x=0 := by simp only [Z,hu0 x hx,map_zero]
  have hGreen := quadratic_weak_mass_reduction hY d hg hK he q hq C hC Z ZH hZH U hZ hU S hS hSY hZ0 hU0 a
  have hv := contDiff_supported_five_half_covariant_derivative hY d hg hK he U hU S hS.isClosed hSY hU0 a
  have hHv : ContDiff ℝ ∞ (fun x => H x (fiveHalfSectionCovariantDerivativeL d U x a)) :=
    OperatorForms.contDiff_supported_operator_apply _ H S hS.isClosed hv.1 hv.2
      (fun x hx => hH.contDiffAt (hY.mem_nhds (hSY hx)))
  have hAI : IntegrableOn A Y :=
    (OperatorForms.integrable_local_weighted_operator_pair (innerSL ℝ) q _ u C S hS
      (fun x hx => hq.contDiffAt (hY.mem_nhds (hSY hx))) hHv hu hu0
      (fun x hx => hC.contDiffAt (hY.mem_nhds (hSY hx)))).integrableOn
  have hEq : quadraticHigherPairRemainder q H N C DQ U a=ᵐ[volume.restrict Y]
      fun x => A x+quadraticWeakMassRemainder d q C Z ZH U a x := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have hApply := higher_covariant_apply_to_section d H U x a
      (hH.contDiffAt (hY.mem_nhds hx)) hU.contDiffAt (N x) (hN x hx) (ZH x) (hZH x hx)
    have hDP := DFunLike.congr_fun (hDQ x hx) (U x)
    simp only [ContinuousLinearMap.comp_apply] at hDP
    have hPair := quadratic_dual_inclusion_pair (ZH x) (DQ x (J (U x)))
    rw [hZH x hx] at hPair
    dsimp only [J] at hPair
    simp only [quadraticHigherPairRemainder,quadraticWeakMassRemainder,A,Z,u,J]
    rw [hApply,hDP,hPair]
    simp only [sphereSobolevDualPairing,inner_add_left]
    ring
  have hRI : IntegrableOn (quadraticHigherPairRemainder q H N C DQ U a) Y :=
    (hAI.add hGreen.2.1).congr hEq.symm
  have hDen : quadraticHigherPairDensity d q H C U a=
      fun x => A x+quadraticWeakMassDensity d q C Z U a x := by
    funext x
    simp only [quadraticHigherPairDensity,quadraticWeakMassDensity,A,Z,u,J]
    ring
  refine ⟨by rw [hDen];exact hAI.add hGreen.1,hRI,?_⟩
  rw [hDen,integral_add hAI hGreen.1,hGreen.2.2]
  exact (integral_add hAI hGreen.2.1).symm.trans (integral_congr_ae hEq).symm

end ShrinkingSpheres.ParallelEnergy
