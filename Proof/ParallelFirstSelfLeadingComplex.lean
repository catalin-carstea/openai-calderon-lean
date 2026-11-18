import Proof.ParallelFirstSelfActualHodgeIntegral
import Proof.ParallelFirstSelfAngularIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def firstSelfAdjointSourceHodgeComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfAdjointSourceHodgeDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfAdjointSourceHodgeDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstSelfAdjointSourceHodgeComplexRemainder {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfAdjointSourceHodgeRemainder WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y+
    firstSelfAdjointSourceHodgeRemainder WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y

def firstSelfLeadingPerturbationComplexDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) : ℝ :=
  firstSelfLeadingComplexDensity P WF E y-firstSelfAngularComplexDensity WF E y-
    firstSelfAdjointSourceHodgeComplexDensity P WF W E y

lemma firstSelfLeadingComplexDensity_eq_hodge_split (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) (y : X) :
    firstSelfLeadingComplexDensity P WF E y=firstSelfAngularComplexDensity WF E y+
      firstSelfAdjointSourceHodgeComplexDensity P WF W E y+firstSelfLeadingPerturbationComplexDensity P WF W E y := by
  unfold firstSelfLeadingPerturbationComplexDensity
  ring

lemma firstSelfLeadingPerturbationComplexDensity_eq_exchange
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) {y : X} (hy : y ∈ Y)
    (hRaw : ∀ b,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (P.firstDerivativeCoordinateHigherL y b)=
      (P.firstDerivativeCoordinateHalfL y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    firstSelfLeadingPerturbationComplexDensity P WF W E y=
      (firstSelfExchangeDensity WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y-
        firstSelfAdjointSourceHodgeDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y)+
      (firstSelfExchangeDensity WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y-
        firstSelfAdjointSourceHodgeDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y) := by
  have hR := firstSelfLeadingDensity_eq_angular_exchange hY hd P WF
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) hy
    ((E.contDiff_realHigherSobolevSection _ _).differentiable (by simp) y) hRaw
  have hI := firstSelfLeadingDensity_eq_angular_exchange hY hd P WF
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) hy
    ((E.contDiff_imagHigherSobolevSection _ _).differentiable (by simp) y) hRaw
  unfold firstSelfLeadingPerturbationComplexDensity firstSelfLeadingComplexDensity
    firstSelfAngularComplexDensity firstSelfAdjointSourceHodgeComplexDensity
  rw [hR,hI]
  ring

/-- Both common real/imaginary actual Hodge contractions are integrable
and have the exact curvature/density integral, for the SAME W. -/
theorem first_self_actual_adjoint_hodge_complex_integral
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    {φ : Field} (E : HarmonicTestExpansion Y d.γ d.frame φ) :
    IntegrableOn (firstSelfAdjointSourceHodgeComplexDensity P WF W E) Y ∧
      IntegrableOn (firstSelfAdjointSourceHodgeComplexRemainder WF E) Y ∧
      (∫ y in Y,firstSelfAdjointSourceHodgeComplexDensity P WF W E y)=
        ∫ y in Y,firstSelfAdjointSourceHodgeComplexRemainder WF E y := by
  have hR := first_self_actual_adjoint_hodge_integral hY hSub hd hK P WF W
    (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_realHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.realHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)
  have hI := first_self_actual_adjoint_hodge_integral hY hSub hd hK P WF W
    (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) (E.contDiff_imagHigherSobolevSection _ _)
    E.supportSet E.compactSupportSet E.supportSubset
    (fun x hx => E.imagHigherSobolevSection_zero (5/2:ℝ) (by norm_num) (by norm_num) hx)
  refine ⟨hR.1.add hI.1,hR.2.1.add hI.2.1,?_⟩
  calc
    _ = (∫ y in Y,firstSelfAdjointSourceHodgeDensity P WF W (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y)+
        ∫ y in Y,firstSelfAdjointSourceHodgeDensity P WF W (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y := integral_add hR.1 hI.1
    _ = (∫ y in Y,firstSelfAdjointSourceHodgeRemainder WF (E.realHigherSobolevSection (5/2:ℝ) (by norm_num)) y)+
        ∫ y in Y,firstSelfAdjointSourceHodgeRemainder WF (E.imagHigherSobolevSection (5/2:ℝ) (by norm_num)) y := congrArg₂ (·+·) hR.2.2 hI.2.2
    _ = _ := (integral_add hR.2.1 hI.2.1).symm

end ShrinkingSpheres.ParallelEnergy
