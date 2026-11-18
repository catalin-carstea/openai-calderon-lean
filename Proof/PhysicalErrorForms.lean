import Proof.WeightedErrorForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

namespace AngularModelData
variable {Y : Set X} {g : MetricField} {e : Frame} {φ : Field} {E : HarmonicTestExpansion Y g e φ} {r : X → ℝ}

def realErrorHorizontal (D : AngularModelData E r) (y : X) (i : I) : SphereL2 :=
  D.realComponent.horizontalBessel i (1/2) (by norm_num) y

def imagErrorHorizontal (D : AngularModelData E r) (y : X) (i : I) : SphereL2 :=
  D.imagComponent.horizontalBessel i (1/2) (by norm_num) y

def realErrorMass (_D : AngularModelData E r) (y : X) : SphereL2 := E.realBessel (3/2) (by norm_num) y

def imagErrorMass (_D : AngularModelData E r) (y : X) : SphereL2 := E.imagBessel (3/2) (by norm_num) y

lemma errorEnergy_components_le (D : AngularModelData E r)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {y : X} (hy : y ∈ Y) :
    metricDensity g y*(errorEnergy (beta g r y) (D.realErrorHorizontal y) (D.realErrorMass y)+
      errorEnergy (beta g r y) (D.imagErrorHorizontal y) (D.imagErrorMass y)) ≤ physicalEnergyDensity g e r φ y := by
  have hsum : (∑ i,(‖D.realErrorHorizontal y i‖^2+‖D.imagErrorHorizontal y i‖^2)) =
      ∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (D.horizontal_sobolev_eq hframe i (1/2) (by norm_num) hy).symm
  have hmass : ‖D.realErrorMass y‖^2+‖D.imagErrorMass y‖^2 = sobolevSq g e (3/2) y (fun w => φ (y,w)) :=
    (E.sobolev_eq_besselSquare hframe (3/2) (by norm_num) hy).symm
  have heq : errorEnergy (beta g r y) (D.realErrorHorizontal y) (D.realErrorMass y)+
      errorEnergy (beta g r y) (D.imagErrorHorizontal y) (D.imagErrorMass y) =
      (beta g r y)⁻¹*(∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
        beta g r y*sobolevSq g e (3/2) y (fun w => φ (y,w)) := by
    unfold errorEnergy
    rw [← hsum,← hmass,Finset.sum_add_distrib]
    ring
  rw [heq]
  have hH : 0 ≤ ∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)) := Finset.sum_nonneg (fun _ _ => fiberSq_nonneg e y _)
  have hmass1 := mul_nonneg (sq_nonneg (beta g r y)) (sobolevSq_nonneg g e 1 y (fun w => φ (y,w)))
  have hinside : (beta g r y)⁻¹*(∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
        beta g r y*sobolevSq g e (3/2) y (fun w => φ (y,w)) ≤
      (∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)))+
        (beta g r y)^2*sobolevSq g e 1 y (fun w => φ (y,w))+
        (beta g r y)⁻¹*(∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
        beta g r y*sobolevSq g e (3/2) y (fun w => φ (y,w)) := by linarith
  exact mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg _)

def errorDensity (D : AngularModelData E r)
    (B : X → I → I → SphereL2 →L[ℝ] SphereL2) (C : X → I → SphereL2 →L[ℝ] SphereL2)
    (Z : X → SphereL2 →L[ℝ] SphereL2) (y : X) : ℝ :=
  metricDensity g y*(weightedErrorForm (beta g r y) (D.realErrorHorizontal y) (D.realErrorMass y) (B y) (C y) (Z y)+
    weightedErrorForm (beta g r y) (D.imagErrorHorizontal y) (D.imagErrorMass y) (B y) (C y) (Z y))

lemma errorDensity_bound (D : AngularModelData E r)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (B : X → I → I → SphereL2 →L[ℝ] SphereL2) (C : X → I → SphereL2 →L[ℝ] SphereL2)
    (Z : X → SphereL2 →L[ℝ] SphereL2) {q : ℝ} (hq : 0 ≤ q) {y : X} (hy : y ∈ Y)
    (hβ : 0 < beta g r y) (hB : ∀ i j,‖B y i j‖ ≤ q) (hC : ∀ i,‖C y i‖ ≤ q) (hZ : ‖Z y‖ ≤ q) :
    |D.errorDensity B C Z y| ≤ 13*q*physicalEnergyDensity g e r φ y := by
  have hr := weightedErrorForm_bound _ hβ (D.realErrorHorizontal y) (D.realErrorMass y) (B y) (C y) (Z y) hq hB hC hZ
  have hi := weightedErrorForm_bound _ hβ (D.imagErrorHorizontal y) (D.imagErrorMass y) (B y) (C y) (Z y) hq hB hC hZ
  have hs := (abs_add_le _ _).trans (add_le_add hr hi)
  have hρ : 0 ≤ metricDensity g y := Real.sqrt_nonneg _
  have ht := mul_le_mul_of_nonneg_left hs hρ
  have he := mul_le_mul_of_nonneg_left (D.errorEnergy_components_le hframe hy) (show 0 ≤ 13*q by positivity)
  unfold errorDensity
  rw [abs_mul,abs_of_nonneg hρ]
  nlinarith only [ht,he]

/-- Once the commutator is represented by bounded balanced coefficients, the actual
    frozen smooth energy gives its complete uniform quadratic-form estimate. -/
theorem integral_errorDensity_bound (D : AngularModelData E r)
    (hY : IsOpen Y) {K : ℝ} (h : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 1 ≤ floor)
    (hφ : Test Y g e φ)
    (B : X → I → I → SphereL2 →L[ℝ] SphereL2) (C : X → I → SphereL2 →L[ℝ] SphereL2)
    (Z : X → SphereL2 →L[ℝ] SphereL2) {q : ℝ} (hq : 0 ≤ q)
    (hB : ∀ y ∈ Y,∀ i j,‖B y i j‖ ≤ q) (hC : ∀ y ∈ Y,∀ i,‖C y i‖ ≤ q) (hZ : ∀ y ∈ Y,‖Z y‖ ≤ q)
    (hform : AEStronglyMeasurable (D.errorDensity B C Z) (volume.restrict Y)) :
    IntegrableOn (D.errorDensity B C Z) Y ∧
      |∫ y in Y,D.errorDensity B C Z y| ≤ 13*q*energySq Y g e r φ := by
  have hbound : ∀ᵐ y ∂volume.restrict Y,‖D.errorDensity B C Z y‖ ≤ 13*q*physicalEnergyDensity g e r φ y := by
    filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
    rw [Real.norm_eq_abs]
    exact D.errorDensity_bound hframe B C Z hq hy ((zero_lt_one.trans_le hfloor).trans_le (hp.2 y hy).2.1)
      (hB y hy) (hC y hy) (hZ y hy)
  have hdom := (hp.integrableOn_physicalEnergyDensity hY h hK e he hframe hfloor hφ).const_mul (13*q)
  refine ⟨hdom.mono' hform hbound,?_⟩
  have ht := norm_integral_le_of_norm_le hdom hbound
  simpa only [Real.norm_eq_abs,integral_const_mul,← energySq_eq_integral_density] using ht

end AngularModelData
end ShrinkingSpheres
