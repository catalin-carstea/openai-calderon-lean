import Proof.BackgroundScalarCurvatureTripleBound
import Proof.HalfCovariantEnergyControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_sphereSobolevInclusionL_apply_le (s t : ℝ) (hst : t ≤ s) (u : SphereSobolev s) :
    ‖sphereSobolevInclusionL s t hst u‖ ≤ ‖u‖ :=
  ((sphereSobolevInclusionL s t hst).le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le s t hst) (norm_nonneg u)).trans_eq (one_mul _))

/-- Canonical section inclusions compare the actual coarse covariant
energy to the genuine half derivative energy; no carrier equality is used. -/
lemma canonical_coarse_direction_energy_le_half (d : Data) (G : X × X → ℝ)
    (hG : ContDiff ℝ ∞ G) (y a : X) (β : ℝ) (hβ : 0 ≤ β) :
    β⁻¹*‖sphereSobolevInclusionL 1 0 (by norm_num)
      (highSectionCovariantDerivative d (ambientSobolevSection 2 (by norm_num) G hG) y a)‖^2+
      β*‖sphereSobolevInclusionL 2 1 (by norm_num) (ambientSobolevSection 2 (by norm_num) G hG y)‖^2 ≤
    halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y β a := by
  let U2 := ambientSobolevSection 2 (by norm_num) G hG
  let UH := ambientSobolevSection (3/2:ℝ) (by norm_num) G hG
  have hDE : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (halfSectionCovariantDerivativeL d UH y a)=
      sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U2 y a) := by
    have hh := congrArg (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num))
      (canonical_half_covariant_section_eq d G hG y a)
    simpa only [UH,U2,sphereSobolevInclusionL_trans_apply] using hh
  have hDN : ‖sphereSobolevInclusionL 1 0 (by norm_num) (highSectionCovariantDerivative d U2 y a)‖ ≤
      ‖halfSectionCovariantDerivativeL d UH y a‖ := by
    rw [←hDE]
    exact norm_sphereSobolevInclusionL_apply_le _ _ (by norm_num) _
  have hME : sphereSobolevInclusionL 2 1 (by norm_num) (U2 y)=
      sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) (UH y) := by
    have hh := congrArg (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
      (ambientSobolevSection_inclusion 2 (3/2:ℝ) (by norm_num) (by norm_num) (by norm_num) G hG y)
    simpa only [U2,UH,sphereSobolevInclusionL_trans_apply] using hh
  have hMN : ‖sphereSobolevInclusionL 2 1 (by norm_num) (U2 y)‖ ≤ ‖UH y‖ := by
    rw [hME]
    exact norm_sphereSobolevInclusionL_apply_le _ _ (by norm_num) _
  exact add_le_add
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hDN) (inv_nonneg.mpr hβ))
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hMN) hβ)

lemma canonical_coarse_triple_energy_le_half_sum (d : Data) (G : X × X → ℝ)
    (hG : ContDiff ℝ ∞ G) (y a b c : X) (β : ℝ) (hβ : 0 ≤ β) :
    coarseCovariantTripleEnergy d (ambientSobolevSection 2 (by norm_num) G hG) y β a b c ≤
      halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y β a+
      halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y β b+
      halfCovariantDirectionEnergy d (ambientSobolevSection (3/2:ℝ) (by norm_num) G hG) y β c := by
  have ha := canonical_coarse_direction_energy_le_half d G hG y a β hβ
  have hb := canonical_coarse_direction_energy_le_half d G hG y b β hβ
  have hc := canonical_coarse_direction_energy_le_half d G hG y c β hβ
  have hMass : 0 ≤ β*‖sphereSobolevInclusionL 2 1 (by norm_num)
      (ambientSobolevSection 2 (by norm_num) G hG y)‖^2 := mul_nonneg hβ (sq_nonneg _)
  dsimp only [coarseCovariantTripleEnergy]
  nlinarith only [ha,hb,hc,hMass]

/-- The SAME canonical coarse energy in the scalar curvature estimate is
bounded by the original physical energy, uniformly over arbitrary frames. -/
theorem AngularModelData.coarse_covariant_triple_energy_le
    {Y : Set X} {d : Data} {φ : Field} {E : HarmonicTestExpansion Y d.γ d.frame φ}
    (D : AngularModelData E d.radius) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 1 ≤ K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y)
    (hFrame : ∀ x ∈ Y,∀ j k,metricPair d.γ x (d.frame x j) (d.frame x k)=if j=k then 1 else 0)
    (hφ : smoothNear φ (bundle Y d.γ)) {y : X} (hy : y ∈ Y) (a b c : I) :
    metricDensity d.γ y*(
      coarseCovariantTripleEnergy d (E.realSobolevSection 2 (by norm_num)) y (beta d.γ d.radius y) (axis a) (axis b) (axis c)+
      coarseCovariantTripleEnergy d (E.imagSobolevSection 2 (by norm_num)) y (beta d.γ d.radius y) (axis a) (axis b) (axis c)) ≤
      (3*(3*K^2+1))*physicalEnergyDensity d.γ d.frame d.radius φ y := by
  let β := beta d.γ d.radius y
  let ER := fun i => halfCovariantDirectionEnergy d (E.realSobolevSection (3/2:ℝ) (by norm_num)) y β (axis i)
  let EI := fun i => halfCovariantDirectionEnergy d (E.imagSobolevSection (3/2:ℝ) (by norm_num)) y β (axis i)
  have hR : coarseCovariantTripleEnergy d (E.realSobolevSection 2 (by norm_num)) y β (axis a) (axis b) (axis c) ≤
      ER a+ER b+ER c :=
    canonical_coarse_triple_energy_le_half_sum d _ _ y (axis a) (axis b) (axis c) β (Real.sqrt_nonneg _)
  have hI : coarseCovariantTripleEnergy d (E.imagSobolevSection 2 (by norm_num)) y β (axis a) (axis b) (axis c) ≤
      EI a+EI b+EI c :=
    canonical_coarse_triple_energy_le_half_sum d _ _ y (axis a) (axis b) (axis c) β (Real.sqrt_nonneg _)
  have hPer (i : I) : metricDensity d.γ y*(ER i+EI i) ≤
      (3*K^2+1)*physicalEnergyDensity d.γ d.frame d.radius φ y :=
    D.half_covariant_direction_energy_le hY hg hK he hFrame hφ hy i
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  have hSum := mul_le_mul_of_nonneg_left (add_le_add hR hI) hμ
  have hA := hPer a
  have hB := hPer b
  have hC := hPer c
  dsimp only [β] at hSum
  linarith only [hSum,hA,hB,hC]

end ShrinkingSpheres
