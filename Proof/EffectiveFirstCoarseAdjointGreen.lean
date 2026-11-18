import Proof.EffectiveFirstAdjointCoreGreen

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

lemma halfSectionCovariantDerivative_of_two (d : Data)
    (Ψ : X → SphereSobolev 2) {y : X} (hΨ : DifferentiableAt ℝ Ψ y) (a : X) :
    halfSectionCovariantDerivativeL d
      (fun x => sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (Ψ x)) y a=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d Ψ y a) := by
  have hh := gradedSphereSectionCovariantDerivative_inclusion 2 (3/2:ℝ) (by norm_num) d Ψ y a hΨ
  have hI : sphereSobolevInclusionL ((2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simpa only [gradedSphereSectionCovariantDerivative_two,
    gradedSphereSectionCovariantDerivative_threeHalf,hI] using hh.symm

/-- The same density core transposes the actual coarse first coefficient,
on the genuine common H2/H5/2 domain. -/
theorem PhysicalPrincipalData.firstAdjointDensityCoreRow_coarse_green
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (Ψ : X → SphereSobolev 2)
    (hU : ContDiff ℝ ∞ U) (hΨ : ContDiff ℝ ∞ Ψ)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y)
    (h0U : ∀ x ∉ S,U x=0) (h0Ψ : ∀ x ∉ S,Ψ x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    (∫ y in Y,metricDensity d.γ y*⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),
      P.firstCovariantCoordinateCoarseL b y (highSectionCovariantDerivative d Ψ y (axis b))⟫_ℝ)=
      -(∫ y in Y,⟪sphereSobolevInclusionL 2 0 (by norm_num) (Ψ y),
        sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
          (P.firstAdjointDensityCoreRow WF WQ U b y)⟫_ℝ) := by
  let Ψh := fun y => sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (Ψ y)
  have hΨh : ContDiff ℝ ∞ Ψh :=
    (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num)).contDiff.comp hΨ
  have h0Ψh (y) (hy : y ∉ S) : Ψh y=0 := by simp only [Ψh,h0Ψ y hy,map_zero]
  have hGreen := (P.firstAdjointDensityCoreRow_green hY hΩ hSub hd hK WF WQ U Ψh hU hΨh
    S hS hSY h0U h0Ψh b hw).2
  have hPoint (y : X) (hy : y ∈ Y) :
      ⟪sphereSobolevInclusionL (5/2:ℝ) 0 (by norm_num) (U y),
        P.firstCovariantCoordinateCoarseL b y (highSectionCovariantDerivative d Ψ y (axis b))⟫_ℝ=
      sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
        (P.firstCovariantCoordinateHalfL b y (halfSectionCovariantDerivativeL d Ψh y (axis b))) := by
    have hg := DFunLike.congr_fun (P.firstCovariantCoordinate_coarse_half_compatible hd hY hy b)
      (highSectionCovariantDerivative d Ψ y (axis b))
    simp only [ContinuousLinearMap.comp_apply] at hg
    have hp := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num)
      (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
      (P.firstCovariantCoordinateCoarseL b y (highSectionCovariantDerivative d Ψ y (axis b)))
    rw [hg] at hp
    rw [halfSectionCovariantDerivative_of_two d Ψ (hΨ.differentiable (by simp) y)]
    simpa only [sphereSobolevInclusionL_trans_apply] using hp.symm
  calc
    _ = ∫ y in Y,metricDensity d.γ y*sphereSobolevDualPairing (1/2:ℝ)
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))
        (P.firstCovariantCoordinateHalfL b y (halfSectionCovariantDerivativeL d Ψh y (axis b))) :=
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
        exact congrArg (fun z => metricDensity d.γ y*z) (hPoint y hy))
    _ = _ := by simpa only [Ψh,sphereSobolevInclusionL_trans_apply] using hGreen

end ShrinkingSpheres
