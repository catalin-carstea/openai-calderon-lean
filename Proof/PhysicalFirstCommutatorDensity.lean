import Proof.FirstCommutatorFormBound
import Proof.HalfCanonicalCovariantSection
import Proof.PhysicalErrorForms
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace AngularComponentData
variable {Y : Set X} {d : Data} {φ : Field} {L : ℂ →L[ℝ] ℝ}
  {E : HarmonicTestExpansion Y d.γ d.frame φ}

def horizontalHalfSection (Q : AngularComponentData E d.radius L) (i : I) : X → SphereSobolev (1/2:ℝ) :=
  ambientSobolevSection (1/2:ℝ) (by norm_num) (Q.horizontalRepresentative i) (Q.horizontalSmooth i)
def horizontalThreeHalfSection (Q : AngularComponentData E d.radius L) (i : I) : X → SphereSobolev (3/2:ℝ) :=
  ambientSobolevSection (3/2:ℝ) (by norm_num) (Q.horizontalRepresentative i) (Q.horizontalSmooth i)

lemma horizontalThreeHalfSection_inclusion (Q : AngularComponentData E d.radius L) (i : I) (y : X) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (Q.horizontalThreeHalfSection i y)=
      Q.horizontalHalfSection i y := ambientSobolevSection_inclusion (3/2:ℝ) (1/2:ℝ)
        (by norm_num) (by norm_num) (by norm_num) _ _ y
lemma norm_horizontalHalfSection (Q : AngularComponentData E d.radius L) (i : I) (y : X) :
    ‖Q.horizontalHalfSection i y‖=‖Q.horizontalBessel i (1/2:ℝ) (by norm_num) y‖ :=
  norm_ambientSobolevSection _ _ _ _ _
end AngularComponentData

namespace AngularModelData
variable {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}

def firstCommutatorDensity (D : AngularModelData E d.radius)
    (S : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) (y : X) : ℝ :=
  metricDensity d.γ y*(firstCommutatorForm (fun i j => S i j y) (fun i => D.realComponent.horizontalHalfSection i y)+
    firstCommutatorForm (fun i j => S i j y) (fun i => D.imagComponent.horizontalHalfSection i y))

lemma abs_firstCommutatorDensity_le (D : AngularModelData E d.radius)
    (hFrame : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (S : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    (hβ : 1 ≤ beta d.γ d.radius y)
    (hS : ∀ i j,‖S i j y‖ ≤ C*(ε/beta d.γ d.radius y)^2) :
    |D.firstCommutatorDensity S y| ≤ (9*C*ε)*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let β := beta d.γ d.radius y
  let Vr := fun i => D.realComponent.horizontalHalfSection i y
  let Vi := fun i => D.imagComponent.horizontalHalfSection i y
  have hR := abs_firstCommutatorForm_le (fun i j => S i j y) Vr hC hε hε1 hβ hS
  have hI := abs_firstCommutatorForm_le (fun i j => S i j y) Vi hC hε hε1 hβ hS
  have hRN (i : I) : ‖Vr i‖=‖D.realErrorHorizontal y i‖ := D.realComponent.norm_horizontalHalfSection i y
  have hIN (i : I) : ‖Vi i‖=‖D.imagErrorHorizontal y i‖ := D.imagComponent.norm_horizontalHalfSection i y
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := zero_le_one.trans hβ
  have hMassR := mul_nonneg hβ0 (sq_nonneg ‖D.realErrorMass y‖)
  have hMassI := mul_nonneg hβ0 (sq_nonneg ‖D.imagErrorMass y‖)
  have hInside : β⁻¹*(∑ i : I,‖Vr i‖^2)+β⁻¹*(∑ i : I,‖Vi i‖^2) ≤
      errorEnergy β (D.realErrorHorizontal y) (D.realErrorMass y)+
        errorEnergy β (D.imagErrorHorizontal y) (D.imagErrorMass y) := by
    simp_rw [hRN,hIN]
    unfold errorEnergy
    linarith only [hMassR,hMassI]
  have hEnergy := (mul_le_mul_of_nonneg_left hInside hμ).trans (D.errorEnergy_components_le hFrame hy)
  change |metricDensity d.γ y*(firstCommutatorForm _ Vr+firstCommutatorForm _ Vi)| ≤ _
  rw [abs_mul,abs_of_nonneg hμ]
  calc
    _ ≤ metricDensity d.γ y*(|firstCommutatorForm _ Vr|+|firstCommutatorForm _ Vi|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hμ
    _ ≤ metricDensity d.γ y*((9*C*ε)*(β⁻¹*(∑ i : I,‖Vr i‖^2))+
        (9*C*ε)*(β⁻¹*(∑ i : I,‖Vi i‖^2))) := mul_le_mul_of_nonneg_left (add_le_add hR hI) hμ
    _ = (9*C*ε)*(metricDensity d.γ y*(β⁻¹*(∑ i : I,‖Vr i‖^2)+β⁻¹*(∑ i : I,‖Vi i‖^2))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hEnergy (by positivity)
end AngularModelData
end ShrinkingSpheres
