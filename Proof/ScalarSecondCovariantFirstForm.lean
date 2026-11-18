import Proof.CoarseCovariantDistributionDerivative
import Proof.PhysicalFirstCommutatorDensity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma abs_small_scalar_second_jet_product_le (a z A C ε β x y : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (ha : |a| ≤ A*ε/β^2) (hz : |z| ≤ C*ε*β*x*y) :
    |a*z| ≤ A*C*ε^2*(β⁻¹*x^2+β*y^2) := by
  have hβpos : 0 < β := zero_lt_one.trans_le hβ
  have hQ : 0 ≤ A*C*ε^2 := by positivity
  have hxy : 0 ≤ x*y := mul_nonneg hx hy
  rw [abs_mul]
  calc
    _ ≤ (A*ε/β^2)*(C*ε*β*x*y) := mul_le_mul ha hz (abs_nonneg _) (by positivity)
    _ = (A*C*ε^2/β)*(x*y) := by field_simp
    _ ≤ (A*C*ε^2)*(x*y) := mul_le_mul_of_nonneg_right (div_le_self hQ hβ) hxy
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_product_le x y β hβpos) hQ

def AngularComponentData.scalarSecondCovariantFirstForm {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) (F : SphereSobolev 2 →L[ℝ] SphereSobolev (-1))
    (j : I) (y : X) : ℝ :=
  sphereSobolevDualPairing 1
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (Q.horizontalThreeHalfSection j y))
    (F (ambientSobolevSection 2 (by norm_num) (fun p => L (E.representative p))
      (L.contDiff.comp E.representativeSmooth) y))

lemma AngularComponentData.abs_scalarSecondCovariantFirstForm_le {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L) (F : SphereSobolev 2 →L[ℝ] SphereSobolev (-1))
    (j : I) (y : X) (a A C ε β : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hβ : 1 ≤ β)
    (ha : |a| ≤ A*ε/β^2)
    (hF : ∀ u : SphereSobolev 1,∀ v : SphereSobolev 2,
      |sphereSobolevDualPairing 1 u (F v)| ≤ C*ε*β*
        ‖sphereSobolevInclusionL 1 0 (by norm_num) u‖*‖sphereSobolevInclusionL 2 1 (by norm_num) v‖) :
    |a*Q.scalarSecondCovariantFirstForm F j y| ≤ A*C*ε^2*
      (β⁻¹*(∑ k : I,‖Q.horizontalHalfSection k y‖^2)+β*
        ‖ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
          (L.contDiff.comp E.representativeSmooth) y‖^2) := by
  let U2 := ambientSobolevSection 2 (by norm_num) (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth) y
  let UH := ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth) y
  let H := Q.horizontalThreeHalfSection j y
  have hInclusion {s t : ℝ} (hst : t ≤ s) (u : SphereSobolev s) :
      ‖sphereSobolevInclusionL s t hst u‖ ≤ ‖u‖ :=
    ((sphereSobolevInclusionL s t hst).le_opNorm u).trans
      ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le s t hst) (norm_nonneg u)).trans_eq (one_mul _))
  have hHorEq : sphereSobolevInclusionL 1 0 (by norm_num)
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) H)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) (Q.horizontalHalfSection j y) := by
    rw [←Q.horizontalThreeHalfSection_inclusion j y]
    simp only [sphereSobolevInclusionL_trans_apply,H]
  have hHN : ‖sphereSobolevInclusionL 1 0 (by norm_num)
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) H)‖ ≤ ‖Q.horizontalHalfSection j y‖ := by
    rw [hHorEq]
    exact hInclusion (by norm_num) _
  have hMass : sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) U2=UH :=
    ambientSobolevSection_inclusion 2 (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num) _ _ y
  have hMN : ‖sphereSobolevInclusionL 2 1 (by norm_num) U2‖ ≤ ‖UH‖ := by
    have hEq : sphereSobolevInclusionL 2 1 (by norm_num) U2=
        sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) UH := by
      rw [←hMass,sphereSobolevInclusionL_trans_apply]
    rw [hEq]
    exact hInclusion (by norm_num) _
  have hF0 := hF (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) H) U2
  have hCoef : 0 ≤ C*ε*β := by positivity
  have hFBound : |Q.scalarSecondCovariantFirstForm F j y| ≤ C*ε*β*‖Q.horizontalHalfSection j y‖*‖UH‖ :=
    hF0.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul hHN hMN (norm_nonneg _) (norm_nonneg _)) hCoef)
  have hOne := abs_small_scalar_second_jet_product_le a (Q.scalarSecondCovariantFirstForm F j y)
    A C ε β ‖Q.horizontalHalfSection j y‖ ‖UH‖ hA hC hε hβ (norm_nonneg _) (norm_nonneg _) ha hFBound
  have hSingle := Finset.single_le_sum (f:=fun k : I => ‖Q.horizontalHalfSection k y‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  exact hOne.trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hSingle (inv_nonneg.mpr (zero_le_one.trans hβ))) le_rfl)
    (by positivity))

def AngularModelData.scalarSecondCovariantFirstDensity {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (w : X → ℝ) (F : X → SphereSobolev 2 →L[ℝ] SphereSobolev (-1)) (j : I) (y : X) : ℝ :=
  metricDensity d.γ y*(w y*D.realComponent.scalarSecondCovariantFirstForm (F y) j y+
    w y*D.imagComponent.scalarSecondCovariantFirstForm (F y) j y)

lemma AngularModelData.abs_scalarSecondCovariantFirstDensity_le {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (w : X → ℝ) (F : X → SphereSobolev 2 →L[ℝ] SphereSobolev (-1)) (j : I)
    {y : X} (hy : y ∈ Y) {A C ε : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hβ : 1 ≤ beta d.γ d.radius y) (hw : |w y| ≤ A*ε/(beta d.γ d.radius y)^2)
    (hF : ∀ u : SphereSobolev 1,∀ v : SphereSobolev 2,
      |sphereSobolevDualPairing 1 u (F y v)| ≤ C*ε*beta d.γ d.radius y*
        ‖sphereSobolevInclusionL 1 0 (by norm_num) u‖*‖sphereSobolevInclusionL 2 1 (by norm_num) v‖) :
    |D.scalarSecondCovariantFirstDensity w F j y| ≤ (A*C*ε^2)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hR := D.realComponent.abs_scalarSecondCovariantFirstForm_le (F y) j y (w y) A C ε _ hA hC hε hβ hw hF
  have hI := D.imagComponent.abs_scalarSecondCovariantFirstForm_le (F y) j y (w y) A C ε _ hA hC hε hβ hw hF
  simp_rw [D.realComponent.norm_horizontalHalfSection] at hR
  simp_rw [D.imagComponent.norm_horizontalHalfSection] at hI
  have hMR : ‖ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => Complex.reCLM (E.representative p))
      (Complex.reCLM.contDiff.comp E.representativeSmooth) y‖=‖D.realErrorMass y‖ := norm_ambientSobolevSection _ _ _ _ _
  have hMI : ‖ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => Complex.imCLM (E.representative p))
      (Complex.imCLM.contDiff.comp E.representativeSmooth) y‖=‖D.imagErrorMass y‖ := norm_ambientSobolevSection _ _ _ _ _
  rw [hMR] at hR
  rw [hMI] at hI
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  change |metricDensity d.γ y*(_+_)| ≤ _
  rw [abs_mul,abs_of_nonneg hμ]
  have hSum := mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hR hI)) hμ
  have hEnergy := mul_le_mul_of_nonneg_left (D.errorEnergy_components_le hFrame hy)
    (by positivity : 0 ≤ A*C*ε^2)
  apply hSum.trans
  convert hEnergy using 1 <;> simp only [errorEnergy,AngularModelData.realErrorHorizontal,
    AngularModelData.imagErrorHorizontal] <;> ring

end ShrinkingSpheres
