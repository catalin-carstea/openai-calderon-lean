import Proof.ParallelScalarFirstLeadingSum
import Proof.ParallelScalarFirstDefectCross

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma scalar_leading_contraction_algebra {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (mu : ℝ) (A : I → I → ℝ) (H : I → I → E) (B : I → E →L[ℝ] E) (V : I → E) :
    2*mu*(∑ k : I,⟪∑ a : I,∑ b : I,A a b • H a b,B k (V k)⟫_ℝ)=
      2*(∑ a : I,∑ b : I,∑ k : I,mu*⟪H a b,A a b • B k (V k)⟫_ℝ) := by
  simp only [inner_add_left,real_inner_smul_left,real_inner_smul_right,Fin.sum_univ_three]
  ring

def scalarFirstLeadingDensity {Y : Set X} {d : Data} {CF CT : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*(∑ a : I,∑ b : I,∑ k : I,
    halfCovariantThirdDensity d (metricDensity d.γ)
      (scalarFirstSymmetricCoefficient P (fun x => scalarPrincipalMatrix d.γ d.g₂ d.radius x a b) k)
      (fiveHalfCovariantDerivative d U) (axis a) (axis b) (axis k) y)

def scalarFirstJetDensity {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let S := scalarFiveHalfSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y
  let L := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)
  let U0 := sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y)
  2*(∑ b : I,sphereSobolevDualPairing (1/2:ℝ) S
    (metricDensity d.γ y • WF.covariantCoordinateAdjointDerivative b b y L+
      fderiv ℝ (metricDensity d.γ) y (axis b) • (P.firstCovariantCoordinateHalfL b y).adjoint U0))

def scalarFirstJetComplexDensity {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  scalarFirstJetDensity P WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    scalarFirstJetDensity P WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

theorem scalarFirstDensity_decomposition
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U) {y : X} (hy : y ∈ Y) :
    scalarFirstDensity P WF W U y=scalarFirstLeadingDensity P U y+
      scalarFirstJetDensity P WF U y+scalarFirstDefectDensity P WF W U y := by
  let A := scalarPrincipalMatrix d.γ d.g₂ d.radius
  let S := scalarFiveHalfSecondSection d A U y
  let F := scalarFiveHalfDefectSection d (metricDensity d.γ) A U y
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let V := fun k => J (fiveHalfCovariantDerivative d U (axis k) y)
  let B := fun k => P.firstCovariantCoordinateHalfL k y+(P.firstCovariantCoordinateHalfL k y).adjoint
  let Lead := metricDensity d.γ y*(∑ k : I,sphereSobolevDualPairing (1/2:ℝ) S (B k (V k)))
  have hExp : scalarFirstDensity P WF W U y=
      2*Lead+scalarFirstJetDensity P WF U y+scalarFirstDefectDensity P WF W U y := by
    have hh := scalarFirstDensity_symmetric_expansion hY hΩ hSub hd hK P WF W U hU hy
    change scalarFirstDensity P WF W U y=2*(Lead+_+_) at hh
    change scalarFirstDensity P WF W U y=2*Lead+2*_+2*_
    linarith only [hh]
  have hLeading : 2*Lead=scalarFirstLeadingDensity P U y := by
    have hh := scalar_leading_contraction_algebra (metricDensity d.γ y) (fun a b => A y a b)
      (fun a b => halfSectionCovariantDerivativeL d (fiveHalfCovariantDerivative d U (axis b)) y (axis a)) B V
    simpa only [Lead,scalarFirstLeadingDensity,halfCovariantThirdDensity,scalarFirstSymmetricCoefficient,
      sphereSobolevDualPairing,_root_.smul_apply,S,scalarFiveHalfSecondSection,A,B,V,J,mul_assoc] using hh
  rw [hExp,hLeading]

theorem scalarFirstComplexDensity_decomposition
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y) :
    scalarFirstComplexDensity P WF W E y=scalarFirstLeadingComplexDensity P E y+
      scalarFirstJetComplexDensity P WF E y+scalarFirstDefectComplexDensity P WF W E y := by
  have hr := scalarFirstDensity_decomposition hY hΩ hSub hd hK P WF W
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _) hy
  have hi := scalarFirstDensity_decomposition hY hΩ hSub hd hK P WF W
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _) hy
  have hLead : scalarFirstLeadingDensity P (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
      scalarFirstLeadingDensity P (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y=
      scalarFirstLeadingComplexDensity P E y := by
    simp only [scalarFirstLeadingDensity,scalarFirstLeadingComplexDensity,scalarFirstLeadingTermComplexDensity,
      Finset.sum_add_distrib,mul_add]
  change scalarFirstDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
      scalarFirstDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y=_
  rw [hr,hi]
  dsimp only [scalarFirstJetComplexDensity,scalarFirstDefectComplexDensity]
  linarith only [hLead]

end ShrinkingSpheres.ParallelEnergy
