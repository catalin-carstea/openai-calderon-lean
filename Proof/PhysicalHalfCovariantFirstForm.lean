import Proof.HalfCovariantFirstFormPointBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

def halfCovariantFirstReducedDensity (d : Data) (U : X → SphereSobolev (3/2:ℝ))
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (i : I) (y : X) : ℝ :=
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let V := halfSectionCovariantDerivativeL d U y (axis i)
  directionalFDeriv (axis i) (metricDensity d.γ) y*
      sphereSobolevDualPairing (1/2:ℝ) (J (U y)) (C y (J (U y)))+
    metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) V (C y (J (U y)))+
    metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ) (J (U y))
      (halfOperatorCovariantDerivativeL d C Ch y (axis i) (U y))

namespace AngularModelData
variable {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}

def halfCovariantFirstReducedDensity (_D : AngularModelData E d.radius)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (i : I) (y : X) : ℝ :=
  ShrinkingSpheres.halfCovariantFirstReducedDensity d
      (E.realSobolevSection (3/2:ℝ) (by norm_num)) C Ch i y+
    ShrinkingSpheres.halfCovariantFirstReducedDensity d
      (E.imagSobolevSection (3/2:ℝ) (by norm_num)) C Ch i y

/-- Actual canonical real and imaginary components share the frozen physical
    energy. Only the displayed coefficient estimates remain conditional. -/
theorem half_covariant_first_reduced_density_bound (D : AngularModelData E d.radius)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ))
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    {y : X} (hy : y ∈ Y) (i : I) {Q M eps : ℝ} (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hβ : 1 ≤ beta d.γ d.radius y)
    (hC : ‖C y‖ ≤ Q*eps/beta d.γ d.radius y)
    (hDC : ‖halfOperatorCovariantDerivativeL d C Ch y (axis i)‖ ≤ Q*eps)
    (hmu : |directionalFDeriv (axis i) (metricDensity d.γ) y| ≤ M*metricDensity d.γ y) :
    |D.halfCovariantFirstReducedDensity C Ch i y| ≤
      (halfDualPairingNorm*Q*(M+3)*eps*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let Ur := E.realSobolevSection (3/2:ℝ) (by norm_num)
  let Ui := E.imagSobolevSection (3/2:ℝ) (by norm_num)
  let A := halfDualPairingNorm*Q*(M+3)*eps
  have hA : 0 ≤ A := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hQ) (by linarith)) heps
  have hr := half_covariant_first_integrand_bound d Ur y (axis i) C Ch
    (metricDensity d.γ y) (directionalFDeriv (axis i) (metricDensity d.γ) y)
    (beta d.γ d.radius y) Q M eps (Real.sqrt_nonneg _) hβ hQ hM heps hC hDC hmu
  have hi := half_covariant_first_integrand_bound d Ui y (axis i) C Ch
    (metricDensity d.γ y) (directionalFDeriv (axis i) (metricDensity d.γ) y)
    (beta d.γ d.radius y) Q M eps (Real.sqrt_nonneg _) hβ hQ hM heps hC hDC hmu
  have hEnergy := D.half_covariant_direction_energy_le hY hg hK he hFrame hφ hy i
  change |ShrinkingSpheres.halfCovariantFirstReducedDensity d Ur C Ch i y+
    ShrinkingSpheres.halfCovariantFirstReducedDensity d Ui C Ch i y| ≤ _
  calc
    _ ≤ |ShrinkingSpheres.halfCovariantFirstReducedDensity d Ur C Ch i y|+
        |ShrinkingSpheres.halfCovariantFirstReducedDensity d Ui C Ch i y| := abs_add_le _ _
    _ ≤ A*(metricDensity d.γ y*halfCovariantDirectionEnergy d Ur y (beta d.γ d.radius y) (axis i))+
        A*(metricDensity d.γ y*halfCovariantDirectionEnergy d Ui y (beta d.γ d.radius y) (axis i)) := add_le_add hr hi
    _ = A*(metricDensity d.γ y*(halfCovariantDirectionEnergy d Ur y (beta d.γ d.radius y) (axis i)+
        halfCovariantDirectionEnergy d Ui y (beta d.γ d.radius y) (axis i))) := by ring
    _ ≤ A*((3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y) :=
      mul_le_mul_of_nonneg_left hEnergy hA
    _ = _ := by ring

theorem integral_half_covariant_first_reduced_density_bound (D : AngularModelData E d.radius)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hfloor : 1 ≤ floor) (hφ : Test Y d.γ d.frame φ)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Ch : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (i : I) {Q M eps : ℝ} (hQ : 0 ≤ Q) (hM : 0 ≤ M) (heps : 0 ≤ eps)
    (hC : ∀ y ∈ Y,‖C y‖ ≤ Q*eps/beta d.γ d.radius y)
    (hDC : ∀ y ∈ Y,‖halfOperatorCovariantDerivativeL d C Ch y (axis i)‖ ≤ Q*eps)
    (hmu : ∀ y ∈ Y,|directionalFDeriv (axis i) (metricDensity d.γ) y| ≤ M*metricDensity d.γ y)
    (hform : AEStronglyMeasurable (D.halfCovariantFirstReducedDensity C Ch i) (volume.restrict Y)) :
    IntegrableOn (D.halfCovariantFirstReducedDensity C Ch i) Y ∧
      |∫ y in Y,D.halfCovariantFirstReducedDensity C Ch i y| ≤
        (halfDualPairingNorm*Q*(M+3)*eps*(3*K^2+1))*energySq Y d.γ d.frame d.radius φ := by
  let q := halfDualPairingNorm*Q*(M+3)*eps*(3*K^2+1)
  have hbound : ∀ᵐ y ∂volume.restrict Y,‖D.halfCovariantFirstReducedDensity C Ch i y‖ ≤
      q*physicalEnergyDensity d.γ d.frame d.radius φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact D.half_covariant_first_reduced_density_bound hY hg hK he hFrame hφ.1 C Ch hy i hQ hM heps
      (hfloor.trans (hp.2 y hy).2.1) (hC y hy) (hDC y hy) (hmu y hy)
  have hdom := (hp.integrableOn_physicalEnergyDensity hY hg (zero_lt_one.trans_le hK)
    d.frame he hFrame hfloor hφ).const_mul q
  refine ⟨hdom.mono' hform hbound,?_⟩
  have ht := norm_integral_le_of_norm_le hdom hbound
  simpa only [Real.norm_eq_abs,integral_const_mul,← energySq_eq_integral_density] using ht

end AngularModelData
end ShrinkingSpheres
