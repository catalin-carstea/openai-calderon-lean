import Proof.ScalarCovariantSelfSquareIdentity
import Proof.PhysicalScalarAdjointDefectPoint
import Proof.PhysicalScalarThirdCrossIntegral
import Proof.PhysicalScalarSecondZeroIntegral

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

def scalarSelfNormDifferenceDensity {Y : Set X} (d : Data) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let mu := metricDensity d.γ
  mu y*((‖scalarCovariantSecondSection d A (E.realSobolevSection 2 (by norm_num)) y‖^2-
    ‖scalarCovariantSecondTransposeSection d mu A (E.realSobolevSection 2 (by norm_num)) y‖^2)+
    (‖scalarCovariantSecondSection d A (E.imagSobolevSection 2 (by norm_num)) y‖^2-
    ‖scalarCovariantSecondTransposeSection d mu A (E.imagSobolevSection 2 (by norm_num)) y‖^2))

theorem physical_scalar_self_square_identity {Y Ω : Set X}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} (hK : 0 < K)
    (d : Data) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {φ : Field}
    (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) :
    scalarSelfNormDifferenceDensity d E y=
      -2*(∑ i : I,∑ j : I,∑ l : I,
        scalarThirdCrossDensity d E (scalarAdjointProductWeight d.γ d.g₂ d.radius i j l) i j l y)-
      2*(∑ i : I,∑ j : I,
        scalarSecondZeroDensity d E (scalarAdjointZeroProductWeight d.γ d.g₂ d.radius i j) i j y)-
      scalarAdjointDefectSquareDensity d E y := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let mu := metricDensity d.γ
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun i j => (hd.1.2.2.1.1 i j).mono hSub,fun x hx => hd.1.2.2.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have haS (i j : I) : ContDiffOn ℝ ∞ (fun x => A x i j) Y := by
    simpa only [A,scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using
      hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hK i j)
  have hSym (x : X) (hx : x ∈ Y) : (A x).IsHermitian :=
    (hd.principal_properties hK (hSub hx)).1.isHermitian.smul (by simp [isSelfAdjoint_iff])
  have hmu := hg.contDiffOn_density hK
  have hmu0 : mu y ≠ 0 := (metricDensity_pos hg hK hy).ne'
  have hR := scalar_covariant_self_square_identity hY d hg hK he mu hmu A haS hSym
    (E.realSobolevSection 2 (by norm_num)) (E.contDiff_realSobolevSection 2 (by norm_num)).contDiffOn hy hmu0
  have hI := scalar_covariant_self_square_identity hY d hg hK he mu hmu A haS hSym
    (E.imagSobolevSection 2 (by norm_num)) (E.contDiff_imagSobolevSection 2 (by norm_num)).contDiffOn hy hmu0
  simp only [scalarSelfNormDifferenceDensity,scalarThirdCrossDensity,scalarSecondZeroDensity,
    scalarAdjointDefectSquareDensity,Finset.sum_add_distrib]
  unfold scalarAdjointProductWeight scalarAdjointZeroProductWeight
  dsimp only [A,mu] at hR hI
  linear_combination hR+hI

end ShrinkingSpheres
