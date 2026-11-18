import Proof.ParallelNormAssembly
import Proof.ParallelFirstSelfCoreSplitIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OperatorForms

variable {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
  {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}

def firstPotentialDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*metricDensity d.γ y*(⟪P.firstCovariantCoreSection (fiveHalfToTwoSection U) y,P.potentialQuadraticCoreSection W U y⟫_ℝ-
    ⟪P.firstFormalAdjointCore WF W U y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ)

def firstPotentialLeadingDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*metricDensity d.γ y*(⟪P.firstCovariantCoreSection (fiveHalfToTwoSection U) y,P.potentialQuadraticCoreSection W U y⟫_ℝ-
    ⟪firstAdjointLeadingCoreSection WF U y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ)

def firstPotentialDefectDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*metricDensity d.γ y*⟪firstAdjointDefectCoreSection P WF W U y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ

def firstPotentialComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstPotentialDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstPotentialDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstPotentialDefectComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstPotentialDefectDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstPotentialDefectDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

lemma component_five_eq_firstPotentialDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (T L : X → SphereL2) (y : X) :
    componentSectorDensity P WF W U T L 5 y=firstPotentialDensity P WF W U y := rfl

lemma sector_five_eq_firstPotentialComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) (y : X) :
    sectorComplexDensity P WF W E D 5 y=firstPotentialComplexDensity P WF W E y := by
  exact (sectorComplexDensity_eq_components P WF W E D 5 y).trans
    (congrArg₂ (·+·)
      (component_five_eq_firstPotentialDensity P WF W _ _ _ y)
      (component_five_eq_firstPotentialDensity P WF W _ _ _ y))


lemma firstPotentialDensity_eq_leading_sub_defect (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    firstPotentialDensity P WF W U y=firstPotentialLeadingDensity P WF W U y-firstPotentialDefectDensity P WF W U y := by
  have hA : P.firstFormalAdjointCore WF W U y=firstAdjointLeadingCoreSection WF U y+
      firstAdjointDefectCoreSection P WF W U y := by unfold firstAdjointDefectCoreSection;abel
  unfold firstPotentialDensity firstPotentialLeadingDensity firstPotentialDefectDensity
  rw [hA,inner_add_left]
  ring

lemma firstPotentialLeadingDensity_eq_positive_rows (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    firstPotentialLeadingDensity P WF W U y=2*metricDensity d.γ y*(
      ⟪P.firstCovariantCoreSection (fiveHalfToTwoSection U) y,P.potentialQuadraticCoreSection W U y⟫_ℝ+
      ∑ b : I,⟪sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
        (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis b))),
        P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ) := by
  unfold firstPotentialLeadingDensity firstAdjointLeadingCoreSection firstAdjointLeadingCoreRow
  simp only [sum_inner,inner_neg_left,Finset.sum_neg_distrib,sub_neg_eq_add]

/-- Literal raw5 is qualitatively integrable before any Green split. -/
theorem firstPotentialComplexDensity_integrable
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (D : AngularModelData E d.radius) :
    IntegrableOn (firstPotentialComplexDensity P WF W E) Y :=
  (sectorComplexDensity_integrable P hY hΩ hSub hd hK WF W hCG hCK E D 5).congr
    (Eventually.of_forall (sector_five_eq_firstPotentialComplexDensity P WF W E D))

/-- The complete actual first-adjoint defect/potential pairing is
integrable on the common core, before its quantitative endpoint bound. -/
theorem firstPotentialDefectDensity_integrable
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (firstPotentialDefectDensity P WF W U) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK
  have hA := P.firstFormalAdjointCore_memLp hY hΩ hSub hd hK WF W hCG hCK U hU S hS hSY hU0 hw 2
  have hL := firstAdjointLeadingCoreSection_memLp hY hSub hd hK WF U hU S hS hSY hU0 2
  have hD : MemLp (firstAdjointDefectCoreSection P WF W U) 2 (volume.restrict Y) := hA.sub hL
  have hVA := P.potentialQuadraticAdjointCoreSection_memLp hY hSub hd hK W hCG hCK U hU S hS hSY hU0 2
  have hD0 (y : X) (hy : y ∉ S) : firstAdjointDefectCoreSection P WF W U y=0 := by
    unfold firstAdjointDefectCoreSection
    rw [P.firstFormalAdjointCore_zero_off hY hd WF W U hU S hS.isClosed hSY hU0 hw hy]
    have hL0 : firstAdjointLeadingCoreSection WF U y=0 := by
      unfold firstAdjointLeadingCoreSection
      exact Finset.sum_eq_zero (fun b _ =>
        (firstAdjointLeadingCoreRow_supported hY hSub hd hK WF U hU S hS.isClosed hSY hU0 b).2 y hy)
    rw [hL0,sub_self]
  have hCross := integrableOn_local_weighted_inner_of_memLp hY.measurableSet hS hSY _ _ hD hVA
    (fun y _ hy => hD0 y hy) (metricDensity d.γ) (hg.contDiffOn_density hK).continuousOn
  change Integrable (fun y => 2*metricDensity d.γ y*
    ⟪firstAdjointDefectCoreSection P WF W U y,P.potentialQuadraticAdjointCoreSection W U y⟫_ℝ) (volume.restrict Y)
  simpa only [mul_assoc] using hCross.const_mul 2

end ShrinkingSpheres.ParallelEnergy
