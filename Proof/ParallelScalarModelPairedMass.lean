import Proof.ParallelScalarFirstMassReduction

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

def pairedHalfMassDensity (d : Data) (q : I → I → X → ℝ)
    (C0 C1 : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (U0 U1 : X → SphereSobolev (3/2:ℝ)) (H : I → X → SphereSobolev (3/2:ℝ)) (x : X) : ℝ :=
  ∑ a : I,∑ b : I,(halfCovariantSecondMassDensity d (q a b) C0 U0 (H b) (axis a) x-
    halfCovariantSecondMassDensity d (q a b) C1 U1 (H b) (axis a) x)

def pairedHalfMassRemainderTerm (d : Data) (q : X → ℝ)
    (C0 C1 : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch0 Ch1 : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U0 U1 V : X → SphereSobolev (3/2:ℝ)) (a x : X) : ℝ :=
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num);
  -q x*(sphereSobolevDualPairing (1/2:ℝ) (J (U0 x)) (halfOperatorCovariantDerivativeL d C0 Ch0 x a (V x))-
    sphereSobolevDualPairing (1/2:ℝ) (J (U1 x)) (halfOperatorCovariantDerivativeL d C1 Ch1 x a (V x)))-
  fderiv ℝ q x a*(sphereSobolevDualPairing (1/2:ℝ) (J (U0 x)) (C0 x (J (V x)))-
    sphereSobolevDualPairing (1/2:ℝ) (J (U1 x)) (C1 x (J (V x))))

def pairedHalfMassRemainder (d : Data) (q : I → I → X → ℝ)
    (C0 C1 : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch0 Ch1 : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (U0 U1 : X → SphereSobolev (3/2:ℝ)) (H : I → X → SphereSobolev (3/2:ℝ)) (x : X) : ℝ :=
  ∑ a : I,∑ b : I,pairedHalfMassRemainderTerm d (q a b) C0 C1 Ch0 Ch1 U0 U1 (H b) (axis a) x

/-- Two genuine Green operations preserve a scalar-weighted angular
pair. Only its contracted gradient cancellation is required; the output
contains first coefficient jets and scalar-weight derivatives. -/
theorem paired_half_mass_reduction {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (q : I → I → X → ℝ) (hq : ∀ a b,ContDiffOn ℝ ∞ (q a b) Y)
    (C0 C1 : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch0 Ch1 : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC0 : ContDiffOn ℝ ∞ C0 Y) (hC1 : ContDiffOn ℝ ∞ C1 Y)
    (hCh0 : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch0 x)=
      (C0 x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hCh1 : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch1 x)=
      (C1 x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (U0 U1 : X → SphereSobolev (3/2:ℝ)) (H : I → X → SphereSobolev (3/2:ℝ))
    (hU0 : ContDiff ℝ ∞ U0) (hU1 : ContDiff ℝ ∞ U1) (hH : ∀ b,ContDiff ℝ ∞ (H b))
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (hU00 : ∀ x ∉ S,U0 x=0) (hU10 : ∀ x ∉ S,U1 x=0) (hH0 : ∀ b x,x ∉ S → H b x=0)
    (hCancel : ∀ x ∈ Y,(∑ a : I,∑ b : I,q a b x*(
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U0 x (axis a))
        (C0 x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b x)))-
      sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U1 x (axis a))
        (C1 x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b x)))))=0) :
    IntegrableOn (pairedHalfMassDensity d q C0 C1 U0 U1 H) Y ∧
    IntegrableOn (pairedHalfMassRemainder d q C0 C1 Ch0 Ch1 U0 U1 H) Y ∧
    (∫ x in Y,pairedHalfMassDensity d q C0 C1 U0 U1 H x)=
      ∫ x in Y,pairedHalfMassRemainder d q C0 C1 Ch0 Ch1 U0 U1 H x := by
  let T0 := fun a b => halfCovariantSecondMassDensity d (q a b) C0 U0 (H b) (axis a)
  let T1 := fun a b => halfCovariantSecondMassDensity d (q a b) C1 U1 (H b) (axis a)
  let R0 := fun a b => halfCovariantSecondMassRemainder d (q a b) C0 Ch0 U0 (H b) (axis a)
  let R1 := fun a b => halfCovariantSecondMassRemainder d (q a b) C1 Ch1 U1 (H b) (axis a)
  have h0 (a b : I) := half_covariant_second_mass_reduction hY d hg hK he (q a b) (hq a b)
    C0 Ch0 hC0 hCh0 U0 (H b) hU0 (hH b) S hS hSY hU00 (hH0 b) (axis a)
  have h1 (a b : I) := half_covariant_second_mass_reduction hY d hg hK he (q a b) (hq a b)
    C1 Ch1 hC1 hCh1 U1 (H b) hU1 (hH b) S hS hSY hU10 (hH0 b) (axis a)
  have hTI : IntegrableOn (fun x => ∑ a : I,∑ b : I,(T0 a b x-T1 a b x)) Y :=
    integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (h0 a b).1.sub (h1 a b).1))
  have hRI : IntegrableOn (fun x => ∑ a : I,∑ b : I,(R0 a b x-R1 a b x)) Y :=
    integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (h0 a b).2.1.sub (h1 a b).2.1))
  have hPoint : pairedHalfMassRemainder d q C0 C1 Ch0 Ch1 U0 U1 H =ᵐ[volume.restrict Y]
      (fun x => ∑ a : I,∑ b : I,(R0 a b x-R1 a b x)) := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    have ht (a b : I) : pairedHalfMassRemainderTerm d (q a b) C0 C1 Ch0 Ch1 U0 U1 (H b) (axis a) x=
        R0 a b x-R1 a b x+q a b x*(
          sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U0 x (axis a))
            (C0 x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b x)))-
          sphereSobolevDualPairing (1/2:ℝ) (halfSectionCovariantDerivativeL d U1 x (axis a))
            (C1 x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H b x)))) := by
      dsimp only [R0,R1,pairedHalfMassRemainderTerm,halfCovariantSecondMassRemainder]
      ring
    dsimp only [pairedHalfMassRemainder]
    simp_rw [ht,Finset.sum_add_distrib]
    rw [hCancel x hx,add_zero]
  refine ⟨hTI,hRI.congr hPoint.symm,?_⟩
  rw [integral_congr_ae hPoint]
  change (∫ x in Y,∑ a : I,∑ b : I,(T0 a b x-T1 a b x))=_
  rw [integral_finsetSum Finset.univ (f:=fun a x => ∑ b : I,(T0 a b x-T1 a b x))
      (fun a _ => integrable_finsetSum Finset.univ (fun b _ => (h0 a b).1.sub (h1 a b).1)),
    integral_finsetSum Finset.univ (f:=fun a x => ∑ b : I,(R0 a b x-R1 a b x))
      (fun a _ => integrable_finsetSum Finset.univ (fun b _ => (h0 a b).2.1.sub (h1 a b).2.1))]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum Finset.univ (f:=fun b x => T0 a b x-T1 a b x) (fun b _ => (h0 a b).1.sub (h1 a b).1),
    integral_finsetSum Finset.univ (f:=fun b x => R0 a b x-R1 a b x) (fun b _ => (h0 a b).2.1.sub (h1 a b).2.1)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_sub (h0 a b).1 (h1 a b).1,integral_sub (h0 a b).2.1 (h1 a b).2.1,
    (h0 a b).2.2,(h1 a b).2.2]

end ShrinkingSpheres.ParallelEnergy
