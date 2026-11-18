import Proof.UniformPhysicalFirstAdjointDerivativePair
import Proof.PhysicalFirstCommutatorDensity
import Proof.PhysicalHalfCovariantGreenBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

lemma contDiffOn_halfOperatorCovariantDerivativeL {Y : Set X} (hY : IsOpen Y)
    (d : Data) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y) (hA : ContDiffOn ℝ ∞ A Y) (i : I) :
    ContDiffOn ℝ ∞ (fun x => halfOperatorCovariantDerivativeL d C A x (axis i)) Y := by
  have hRH : ContDiffOn ℝ ∞ (fun x => frameAngularConnectionHalfL d x (axis i)) Y :=
    ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun k _ =>
      (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK d.frame he
        (fun _ => axis i) contDiffOn_const j k)).smul contDiffOn_const))
  have hR := contDiffOn_frameAngularConnectionHigherL hY d hg hK he (axis i)
  have hC0 := hC.clm_comp (contDiffOn_const
    (c:=sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
  have hDC0 : ContDiffOn ℝ ∞ (directionalFDeriv (axis i)
      (fun x => (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))) Y :=
    (hC0.fderiv_of_isOpen hY (by simp)).clm_apply (contDiffOn_const (c:=axis i))
  exact (hDC0.sub (hRH.clm_comp hA)).add (hC.clm_comp hR)

def AngularComponentData.adjointDerivativeFirstForm {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L)
    (F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (j : I) (y : X) : ℝ :=
  sphereSobolevDualPairing (1/2:ℝ)
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
      (ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
        (L.contDiff.comp E.representativeSmooth) y)) (F (Q.horizontalThreeHalfSection j y))

lemma AngularComponentData.abs_adjointDerivativeFirstForm_le {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} {L : ℂ →L[ℝ] ℝ}
    (Q : AngularComponentData E d.radius L)
    (F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (j : I) (y : X)
    {CE ε β : ℝ} (hCE : 0 ≤ CE) (hε : 0 ≤ ε) (hβ : 0 < β)
    (hF : ∀ u v : SphereSobolev (3/2:ℝ),
      |sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (F v)| ≤
        CE*ε*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖*‖u‖) :
    |Q.adjointDerivativeFirstForm F j y| ≤ (CE*ε)*
      (β⁻¹*(∑ k : I,‖Q.horizontalHalfSection k y‖^2)+β*
        ‖ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
          (L.contDiff.comp E.representativeSmooth) y‖^2) := by
  let U := ambientSobolevSection (3/2:ℝ) (by norm_num) (fun p => L (E.representative p))
    (L.contDiff.comp E.representativeSmooth) y
  have h := hF U (Q.horizontalThreeHalfSection j y)
  rw [Q.horizontalThreeHalfSection_inclusion] at h
  have hProd := weighted_product_le ‖Q.horizontalHalfSection j y‖ ‖U‖ β hβ
  have hSingle := Finset.single_le_sum (f:=fun k : I => ‖Q.horizontalHalfSection k y‖^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hProd' := hProd.trans (add_le_add (mul_le_mul_of_nonneg_left hSingle (inv_nonneg.mpr hβ.le)) le_rfl)
  exact h.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hProd' (mul_nonneg hCE hε))

def AngularModelData.adjointDerivativeFirstDensity {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (F : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (j : I) (y : X) : ℝ :=
  metricDensity d.γ y*(D.realComponent.adjointDerivativeFirstForm (F y) j y+
    D.imagComponent.adjointDerivativeFirstForm (F y) j y)

lemma AngularModelData.abs_adjointDerivativeFirstDensity_le {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (F : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (j : I)
    {y : X} (hy : y ∈ Y) {CE ε : ℝ} (hCE : 0 ≤ CE) (hε : 0 ≤ ε) (hβ : 0 < beta d.γ d.radius y)
    (hF : ∀ u v : SphereSobolev (3/2:ℝ),
      |sphereSobolevDualPairing (1/2:ℝ) (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u) (F y v)| ≤
        CE*ε*‖sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) v‖*‖u‖) :
    |D.adjointDerivativeFirstDensity F j y| ≤ (CE*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  have hR := D.realComponent.abs_adjointDerivativeFirstForm_le (F y) j y hCE hε hβ hF
  have hI := D.imagComponent.abs_adjointDerivativeFirstForm_le (F y) j y hCE hε hβ hF
  have hNR (k : I) : ‖D.realComponent.horizontalHalfSection k y‖=‖D.realErrorHorizontal y k‖ :=
    D.realComponent.norm_horizontalHalfSection k y
  have hNI (k : I) : ‖D.imagComponent.horizontalHalfSection k y‖=‖D.imagErrorHorizontal y k‖ :=
    D.imagComponent.norm_horizontalHalfSection k y
  simp_rw [hNR] at hR
  simp_rw [hNI] at hI
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
  have hEnergy := mul_le_mul_of_nonneg_left (D.errorEnergy_components_le hFrame hy) (mul_nonneg hCE hε)
  change _ ≤ _
  apply hSum.trans
  convert hEnergy using 1 <;> simp only [errorEnergy] <;> ring

lemma AngularModelData.adjointDerivativeFirstDensity_aestronglyMeasurable {Y : Set X} {d : Data}
    {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ} (D : AngularModelData E d.radius)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (F : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hF : ContDiffOn ℝ ∞ F Y) (j : I) :
    AEStronglyMeasurable (D.adjointDerivativeFirstDensity F j) (volume.restrict Y) := by
  have hForm {L : ℂ →L[ℝ] ℝ} (Q : AngularComponentData E d.radius L) :
      ContDiffOn ℝ ∞ (fun y => Q.adjointDerivativeFirstForm (F y) j y) Y :=
    ((sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)).contDiff.comp_contDiffOn
      (contDiff_ambientSobolevSection _ _ _ _).contDiffOn).inner ℝ
        (hF.clm_apply (contDiff_ambientSobolevSection _ _ _ _).contDiffOn)
  exact ((hg.contDiffOn_density hK).mul ((hForm D.realComponent).add
    (hForm D.imagComponent))).continuousOn.aestronglyMeasurable hY.measurableSet
end ShrinkingSpheres
