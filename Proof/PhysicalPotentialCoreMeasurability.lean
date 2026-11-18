import Proof.PhysicalPotentialCoreCoefficients
import Proof.PhysicalPotentialQuadraticSmooth
import Proof.SobolevCoefficientMeasurability
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT CG CK : ℝ}

def potentialQuadraticCoreSection (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (U : X → SphereSobolev (5/2:ℝ)) : X → SphereSobolev 0 := by
  classical
  exact fun y => if hy : y ∈ Y then P.potentialQuadraticCoreL (W y hy) (U y) else 0

def potentialQuadraticAdjointCoreSection (P : PhysicalPrincipalData Y d CF CT)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (U : X → SphereSobolev (5/2:ℝ)) : X → SphereSobolev 0 := by
  classical
  exact fun y => if hy : y ∈ Y then P.potentialQuadraticAdjointCoreL (W y hy) (U y) else 0

lemma potentialQuadraticCoreSection_aestronglyMeasurable {Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) :
    AEStronglyMeasurable (P.potentialQuadraticCoreSection W U) (volume.restrict Y) := by
  have hQ := P.potentialQuadraticHalfL_smooth hY hSub hd hK
  have hInput := (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp hU
  apply aestronglyMeasurable_sphereSobolev_of_coefficients 0
  intro k
  have hFormula := (sphereSobolevCoefficientL (-(1/2:ℝ)) k).contDiff.comp_contDiffOn
    (hQ.clm_apply hInput.contDiffOn)
  apply hFormula.continuousOn.aestronglyMeasurable hY.measurableSet |>.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  dsimp only [potentialQuadraticCoreSection]
  rw [dite_eq_left hy]
  exact (P.potentialQuadraticCoreL_coefficient hy (W y hy) (U y) k).symm

/-- A chosen genuine higher adjoint family is strongly measurable because
its actual harmonic coefficients are determined by the smooth LOW physical
coefficient and true adjunction. Pointwise choice is not assumed smooth. -/
lemma potentialQuadraticAdjointCoreSection_aestronglyMeasurable {Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) :
    AEStronglyMeasurable (P.potentialQuadraticAdjointCoreSection W U) (volume.restrict Y) := by
  have hQ := P.potentialQuadraticHalfL_smooth hY hSub hd hK
  have hInput := (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num)).contDiff.comp hU
  apply aestronglyMeasurable_sphereSobolev_of_coefficients 0
  intro k
  let Adj : (harmonicSphereSubspace k →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] harmonicSphereSubspace k) :=
    (ContinuousLinearMap.adjoint : (harmonicSphereSubspace k →L[ℝ] SphereSobolev (-(1/2:ℝ))) ≃ₗᵢ[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] harmonicSphereSubspace k)).toContinuousLinearEquiv.toContinuousLinearMap
  have hAdj := Adj.contDiff.comp_contDiffOn (hQ.clm_comp
    (contDiffOn_const (c:=sphereSobolevSingleL (3/2:ℝ) k)))
  have hFormula := hAdj.clm_apply hInput.contDiffOn
  apply hFormula.continuousOn.aestronglyMeasurable hY.measurableSet |>.congr
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  dsimp only [potentialQuadraticAdjointCoreSection]
  rw [dite_eq_left hy]
  exact (P.potentialQuadraticAdjointCoreL_coefficient hy (W y hy) (U y) k).symm
end PhysicalPrincipalData
end ShrinkingSpheres
