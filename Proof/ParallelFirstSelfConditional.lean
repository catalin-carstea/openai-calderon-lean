import Proof.ParallelFirstSelfCoreSplitIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstSelfLeadingDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y*(‖P.firstCovariantCoreSection (fiveHalfToTwoSection U) y‖^2-
    ‖firstAdjointLeadingCoreSection WF U y‖^2)

def firstSelfDefectCrossDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  2*metricDensity d.γ y*⟪firstAdjointLeadingCoreSection WF U y,firstAdjointDefectCoreSection P WF W U y⟫_ℝ

def firstSelfDefectSquareDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y*‖firstAdjointDefectCoreSection P WF W U y‖^2

def firstSelfLeadingComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfLeadingDensity P WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfLeadingDensity P WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstSelfDefectCrossComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfDefectCrossDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfDefectCrossDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstSelfDefectSquareComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfDefectSquareDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfDefectSquareDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

lemma firstSelfComplexDensity_eq_core_split
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) :
    firstSelfComplexDensity P WF W E y=firstSelfLeadingComplexDensity P WF E y-
      firstSelfDefectCrossComplexDensity P WF W E y-firstSelfDefectSquareComplexDensity P WF W E y := by
  unfold firstSelfComplexDensity
  rw [firstSelfDensity_core_split,firstSelfDensity_core_split]
  unfold firstSelfLeadingComplexDensity firstSelfDefectCrossComplexDensity firstSelfDefectSquareComplexDensity
    firstSelfLeadingDensity firstSelfDefectCrossDensity firstSelfDefectSquareDensity
  ring

/-- Complete qualitative integral reduction of the SAME first-self sector.
The subsequent quantitative paired cancellation remains an explicit task. -/
theorem firstSelf_complex_core_split_integrableOn
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    IntegrableOn (firstSelfLeadingComplexDensity P WF E) Y ∧
      IntegrableOn (firstSelfDefectCrossComplexDensity P WF W E) Y ∧
      IntegrableOn (firstSelfDefectSquareComplexDensity P WF W E) Y := by
  have hR := firstSelf_core_split_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_realHigherSobolevSection (5/2:ℝ) (by norm_num)) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)
  have hI := firstSelf_core_split_integrableOn hY hΩ hSub hd hK P WF W hCG hCK
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))
    (E.contDiff_imagHigherSobolevSection (5/2:ℝ) (by norm_num)) E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)
  have hRL : IntegrableOn (firstSelfLeadingDensity P WF
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))) Y := hR.1
  have hIL : IntegrableOn (firstSelfLeadingDensity P WF
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))) Y := hI.1
  have hRC : IntegrableOn (firstSelfDefectCrossDensity P WF W
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))) Y := hR.2.1
  have hIC : IntegrableOn (firstSelfDefectCrossDensity P WF W
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))) Y := hI.2.1
  have hRD : IntegrableOn (firstSelfDefectSquareDensity P WF W
      (E.realHigherSobolevSection (5/2:ℝ) (by norm_num))) Y := hR.2.2
  have hID : IntegrableOn (firstSelfDefectSquareDensity P WF W
      (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num))) Y := hI.2.2
  exact ⟨hRL.add hIL,hRC.add hIC,hRD.add hID⟩

/-- Checked conditional caller for the remaining three concrete physical
integrals. Its premises are estimates, rather than new geometric assumptions. -/
theorem firstSelfComplexDensity_integral_bound_of_core_split
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ)
    (hL : IntegrableOn (firstSelfLeadingComplexDensity P WF E) Y)
    (hC : IntegrableOn (firstSelfDefectCrossComplexDensity P WF W E) Y)
    (hD : IntegrableOn (firstSelfDefectSquareComplexDensity P WF W E) Y)
    (CL CC CD : ℝ)
    (hLB : |∫ y in Y,firstSelfLeadingComplexDensity P WF E y| ≤ CL*ε*energySq Y d.γ d.frame d.radius φ)
    (hCB : |∫ y in Y,firstSelfDefectCrossComplexDensity P WF W E y| ≤ CC*ε*energySq Y d.γ d.frame d.radius φ)
    (hDB : |∫ y in Y,firstSelfDefectSquareComplexDensity P WF W E y| ≤ CD*ε*energySq Y d.γ d.frame d.radius φ) :
    IntegrableOn (firstSelfComplexDensity P WF W E) Y ∧
      |∫ y in Y,firstSelfComplexDensity P WF W E y| ≤ (CL+CC+CD)*ε*energySq Y d.γ d.frame d.radius φ := by
  have hEq : firstSelfComplexDensity P WF W E=
      (fun y => firstSelfLeadingComplexDensity P WF E y-firstSelfDefectCrossComplexDensity P WF W E y-
        firstSelfDefectSquareComplexDensity P WF W E y) :=
    funext (firstSelfComplexDensity_eq_core_split P WF W E)
  rw [hEq]
  refine ⟨(hL.sub hC).sub hD,?_⟩
  change |∫ y in Y,(firstSelfLeadingComplexDensity P WF E-
    firstSelfDefectCrossComplexDensity P WF W E-firstSelfDefectSquareComplexDensity P WF W E) y| ≤ _
  have hInt : (∫ y in Y,(firstSelfLeadingComplexDensity P WF E-
      firstSelfDefectCrossComplexDensity P WF W E-firstSelfDefectSquareComplexDensity P WF W E) y)=
      (∫ y in Y,firstSelfLeadingComplexDensity P WF E y)-
      (∫ y in Y,firstSelfDefectCrossComplexDensity P WF W E y)-
      (∫ y in Y,firstSelfDefectSquareComplexDensity P WF W E y) :=
    (integral_sub (hL.sub hC) hD).trans
      (congrArg (fun t => t-∫ y in Y,firstSelfDefectSquareComplexDensity P WF W E y) (integral_sub hL hC))
  have hTriangle (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le a 0 b
  calc
    _ = |(∫ y in Y,firstSelfLeadingComplexDensity P WF E y)-
        (∫ y in Y,firstSelfDefectCrossComplexDensity P WF W E y)-
        (∫ y in Y,firstSelfDefectSquareComplexDensity P WF W E y)| := congrArg abs hInt
    _ ≤ _ := ((hTriangle _ _).trans (add_le_add (hTriangle _ _) le_rfl)).trans
      ((add_le_add (add_le_add hLB hCB) hDB).trans_eq (by ring))

end ShrinkingSpheres.ParallelEnergy
