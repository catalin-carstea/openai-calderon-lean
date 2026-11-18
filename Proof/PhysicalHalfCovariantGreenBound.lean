import Proof.PhysicalHalfCovariantFirstForm
import Proof.CovariantHalfOperatorGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma contDiffOn_halfCovariantFirstReducedDensity {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (U : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y) (hCh : ContDiffOn ℝ ∞ Ch Y) (i : I) :
    ContDiffOn ℝ ∞ (halfCovariantFirstReducedDensity d U C Ch i) Y := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hRH : ContDiffOn ℝ ∞ (fun x => frameAngularConnectionHalfL d x (axis i)) Y :=
    ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun k _ =>
      (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK d.frame he
        (fun _ => axis i) contDiffOn_const j k)).smul contDiffOn_const))
  have hR := contDiffOn_frameAngularConnectionHigherL hY d hg hK he (axis i)
  have hC0 : ContDiffOn ℝ ∞ (fun x => (C x).comp J) Y := hC.clm_comp contDiffOn_const
  have hDC0 : ContDiffOn ℝ ∞ (directionalFDeriv (axis i) (fun x => (C x).comp J)) Y :=
    (hC0.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hDC : ContDiffOn ℝ ∞ (fun x => halfOperatorCovariantDerivativeL d C Ch x (axis i)) Y :=
    (hDC0.sub (hRH.clm_comp hCh)).add (hC.clm_comp hR)
  have hJU : ContDiffOn ℝ ∞ (fun x => J (U x)) Y := J.contDiff.comp_contDiffOn hU.contDiffOn
  have hV : ContDiffOn ℝ ∞ (fun x => halfSectionCovariantDerivativeL d U x (axis i)) Y := by
    simp only [halfSectionCovariantDerivativeL_apply]
    exact (J.contDiff.comp_contDiffOn (contDiff_directionalFDeriv (axis i) U hU).contDiffOn).sub
      (hR.clm_apply hU.contDiffOn)
  have hmu := hg.contDiffOn_density hK
  have hdmu : ContDiffOn ℝ ∞ (directionalFDeriv (axis i) (metricDensity d.γ)) Y :=
    (hmu.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  exact ((hdmu.mul (hJU.inner ℝ (hC.clm_apply hJU))).add
    (hmu.mul (hV.inner ℝ (hC.clm_apply hJU)))).add
      (hmu.mul (hJU.inner ℝ (hDC.clm_apply hU.contDiffOn)))

def halfCovariantFirstDensity (d : Data) (U : X → SphereSobolev (3/2:ℝ))
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (i : I) (y : X) : ℝ :=
  metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
    (C y (halfSectionCovariantDerivativeL d U y (axis i)))

lemma contDiffOn_halfCovariantFirstDensity {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (U : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hC : ContDiffOn ℝ ∞ C Y) (i : I) :
    ContDiffOn ℝ ∞ (halfCovariantFirstDensity d U C i) Y := by
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hJU : ContDiffOn ℝ ∞ (fun x => J (U x)) Y := J.contDiff.comp_contDiffOn hU.contDiffOn
  have hR := contDiffOn_frameAngularConnectionHigherL hY d hg hK he (axis i)
  have hV : ContDiffOn ℝ ∞ (fun x => halfSectionCovariantDerivativeL d U x (axis i)) Y := by
    simp only [halfSectionCovariantDerivativeL_apply]
    exact (J.contDiff.comp_contDiffOn (contDiff_directionalFDeriv (axis i) U hU).contDiffOn).sub
      (hR.clm_apply hU.contDiffOn)
  exact (hg.contDiffOn_density hK).mul (hJU.inner ℝ (hC.clm_apply hV))

lemma integrableOn_local_continuous_supported {Y S : Set X} (hS : IsCompact S) (hSY : S ⊆ Y)
    (f : X → ℝ) (hf : ContinuousOn f Y) (h0 : ∀ x ∉ S,f x=0) : IntegrableOn f Y := by
  have hsupp : Function.support f ⊆ S := by
    intro x hx
    by_contra hn
    exact hx (h0 x hn)
  exact ((integrableOn_iff_integrable_of_support_subset hsupp).mp
    ((hf.mono hSY).integrableOn_compact hS)).integrableOn

namespace AngularModelData
variable {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}

def halfCovariantFirstDensity (_D : AngularModelData E d.radius)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (i : I) (y : X) : ℝ :=
  ShrinkingSpheres.halfCovariantFirstDensity d (E.realSobolevSection (3/2:ℝ) (by norm_num)) C i y+
    ShrinkingSpheres.halfCovariantFirstDensity d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) C i y

/-- A quantitative physical first-form estimate after genuine covariant
    integration by parts. The same endpoints, density, test and frozen energy
    are used throughout; only coefficient norm bounds remain as inputs. -/
theorem integral_half_covariant_first_form_bound (D : AngularModelData E d.radius)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hfloor : 1 ≤ floor) (hφ : Test Y d.γ d.frame φ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hCS : ContDiffOn ℝ ∞ C Y) (hChS : ContDiffOn ℝ ∞ Ch Y)
    (hPair : ∀ y ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (Ch y)=
      (C y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (i : I) {Q M eps : ℝ} (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hC : ∀ y ∈ Y,‖C y‖ ≤ Q*eps/beta d.γ d.radius y)
    (hDC : ∀ y ∈ Y,‖halfOperatorCovariantDerivativeL d C Ch y (axis i)‖ ≤ Q*eps)
    (hmu : ∀ y ∈ Y,|directionalFDeriv (axis i) (metricDensity d.γ) y| ≤ M*metricDensity d.γ y) :
    |∫ y in Y,D.halfCovariantFirstDensity C i y| ≤
      (halfDualPairingNorm*Q*(M+3)*eps*(3*K^2+1))*energySq Y d.γ d.frame d.radius φ := by
  let Ur := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let Ui := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  have hK0 := zero_lt_one.trans_le hK
  have hRS := contDiffOn_halfCovariantFirstReducedDensity hY d hg hK0 he Ur
    (E.contDiff_realSobolevSection _ _) C Ch hCS hChS i
  have hIS := contDiffOn_halfCovariantFirstReducedDensity hY d hg hK0 he Ui
    (E.contDiff_imagSobolevSection _ _) C Ch hCS hChS i
  have hmeas : AEStronglyMeasurable (D.halfCovariantFirstReducedDensity C Ch i) (volume.restrict Y) :=
    (hRS.continuousOn.add hIS.continuousOn).aestronglyMeasurable hY.measurableSet
  obtain ⟨hInt,hBound⟩ := D.integral_half_covariant_first_reduced_density_bound
    hY hg hK he hFrame hp hfloor hφ C Ch i hQ hM heps hC hDC hmu hmeas
  have hGreen (U : X → SphereSobolev (3/2:ℝ)) (hU : ContDiff ℝ ∞ U)
      (hU0 : ∀ x ∉ E.supportSet,U x=0) :
      (∫ y in Y,ShrinkingSpheres.halfCovariantFirstDensity d U C i y)=
        -(∫ y in Y,ShrinkingSpheres.halfCovariantFirstReducedDensity d U C Ch i y) := by
    simpa only [ShrinkingSpheres.halfCovariantFirstDensity,ShrinkingSpheres.halfCovariantFirstReducedDensity,
      halfSectionCovariantDerivativeL_apply,directionalFDeriv] using
        covariant_half_operator_green hY d hg hK0 he U hU E.supportSet E.compactSupportSet
          E.supportSubset hU0 C Ch hCS hPair (axis i)
  have hRGreen := hGreen Ur (E.contDiff_realSobolevSection _ _) (fun x hx => E.realSobolevSection_zero _ _ hx)
  have hIGreen := hGreen Ui (E.contDiff_imagSobolevSection _ _) (fun x hx => E.imagSobolevSection_zero _ _ hx)
  have hRInt : IntegrableOn (ShrinkingSpheres.halfCovariantFirstReducedDensity d Ur C Ch i) Y := by
    apply integrableOn_local_continuous_supported E.compactSupportSet E.supportSubset _ hRS.continuousOn
    intro x hx
    simp only [ShrinkingSpheres.halfCovariantFirstReducedDensity,Ur,E.realSobolevSection_zero _ _ hx,
      map_zero,sphereSobolevDualPairing,inner_zero_left,inner_zero_right,mul_zero,add_zero]
  have hIInt : IntegrableOn (ShrinkingSpheres.halfCovariantFirstReducedDensity d Ui C Ch i) Y := by
    apply integrableOn_local_continuous_supported E.compactSupportSet E.supportSubset _ hIS.continuousOn
    intro x hx
    simp only [ShrinkingSpheres.halfCovariantFirstReducedDensity,Ui,E.imagSobolevSection_zero _ _ hx,
      map_zero,sphereSobolevDualPairing,inner_zero_left,inner_zero_right,mul_zero,add_zero]
  have hRFInt : IntegrableOn (ShrinkingSpheres.halfCovariantFirstDensity d Ur C i) Y := by
    apply integrableOn_local_continuous_supported E.compactSupportSet E.supportSubset _
      (contDiffOn_halfCovariantFirstDensity hY d hg hK0 he Ur (E.contDiff_realSobolevSection _ _) C hCS i).continuousOn
    intro x hx
    simp only [ShrinkingSpheres.halfCovariantFirstDensity,Ur,E.realSobolevSection_zero _ _ hx,
      map_zero,sphereSobolevDualPairing,inner_zero_left,mul_zero]
  have hIFInt : IntegrableOn (ShrinkingSpheres.halfCovariantFirstDensity d Ui C i) Y := by
    apply integrableOn_local_continuous_supported E.compactSupportSet E.supportSubset _
      (contDiffOn_halfCovariantFirstDensity hY d hg hK0 he Ui (E.contDiff_imagSobolevSection _ _) C hCS i).continuousOn
    intro x hx
    simp only [ShrinkingSpheres.halfCovariantFirstDensity,Ui,E.imagSobolevSection_zero _ _ hx,
      map_zero,sphereSobolevDualPairing,inner_zero_left,mul_zero]
  change |∫ y in Y,ShrinkingSpheres.halfCovariantFirstDensity d Ur C i y+
    ShrinkingSpheres.halfCovariantFirstDensity d Ui C i y| ≤ _
  rw [integral_add hRFInt hIFInt,hRGreen,hIGreen,← neg_add,← integral_add hRInt hIInt,abs_neg]
  exact hBound
end AngularModelData
end ShrinkingSpheres
