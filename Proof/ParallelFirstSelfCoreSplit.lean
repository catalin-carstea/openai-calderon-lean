import Proof.ParallelFirstSelfAdjointNormalForm
import Proof.SupportedHalfCovariantSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Genuine H5/2 to H3/2 covariant derivative of the common source. -/
def firstSelfSourceDerivative (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (y a : X) :
    SphereSobolev (3/2:ℝ) :=
  gradedSphereSectionCovariantDerivative (5/2:ℝ) d U y a

lemma firstSelfSourceDerivative_inclusion (d : Data)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hU : DifferentiableAt ℝ U y) (a : X) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (firstSelfSourceDerivative d U y a)=
      halfSectionCovariantDerivativeL d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y a := by
  have h := gradedSphereSectionCovariantDerivative_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) d U y a hU
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simpa only [hI,gradedSphereSectionCovariantDerivative_threeHalf,firstSelfSourceDerivative] using h

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

/-- The first-base part of the actual physical adjoint in fibre L2. -/
def firstAdjointLeadingCoreRow {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev 0 :=
  -sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    (WF.covariantCoordinateAdjointHigher b y (firstSelfSourceDerivative d U y (axis b)))

def firstAdjointLeadingCoreSection {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev 0 :=
  ∑ b : I,firstAdjointLeadingCoreRow WF U b y

/-- The actual remainder after removing the adjoint first-base term. -/
def firstAdjointDefectCoreSection (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : SphereSobolev 0 :=
  P.firstFormalAdjointCore WF W U y-firstAdjointLeadingCoreSection WF U y

lemma firstAdjointLeadingCoreRow_graph {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (hU : DifferentiableAt ℝ U y) (b : I) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (firstAdjointLeadingCoreRow WF U b y)=firstAdjointLeadingWeakRow P U b y := by
  have hB := DFunLike.congr_fun (WF.covariantCoordinateAdjointHigher_balanced b hy)
    (firstSelfSourceDerivative d U y (axis b))
  simp only [ContinuousLinearMap.comp_apply] at hB
  simp only [firstAdjointLeadingCoreRow,firstAdjointLeadingWeakRow,map_neg,
    sphereSobolevInclusionL_trans_apply,hB,firstSelfSourceDerivative_inclusion d U hU]

lemma firstAdjointDefectCoreSection_graph
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (firstAdjointDefectCoreSection P WF W U y)=
        ∑ b : I,firstAdjointDefectWeakRow P WF U b y := by
  unfold firstAdjointDefectCoreSection
  rw [map_sub,firstFormalAdjointCore_weak_normal_form hY hΩ hSub hd hK P WF W U hU hy]
  have hL : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (firstAdjointLeadingCoreSection WF U y)=∑ b : I,firstAdjointLeadingWeakRow P U b y := by
    unfold firstAdjointLeadingCoreSection
    rw [map_sum]
    exact Finset.sum_congr rfl (fun b _ => firstAdjointLeadingCoreRow_graph WF U hy
      ((hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) b)
  rw [hL]
  abel

/-- Pointwise square expansion with the complete lower adjoint defect
still present. Bounds for these terms remain a separate mathematical step. -/
lemma firstSelfDensity_core_split
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    firstSelfDensity P WF W U y=
      metricDensity d.γ y*(
        ‖P.firstCovariantCoreSection (fiveHalfToTwoSection U) y‖^2-
        ‖firstAdjointLeadingCoreSection WF U y‖^2-
        2*⟪firstAdjointLeadingCoreSection WF U y,firstAdjointDefectCoreSection P WF W U y⟫_ℝ-
        ‖firstAdjointDefectCoreSection P WF W U y‖^2) := by
  have hA : P.firstFormalAdjointCore WF W U y=
      firstAdjointLeadingCoreSection WF U y+firstAdjointDefectCoreSection P WF W U y := by
    unfold firstAdjointDefectCoreSection
    abel
  unfold firstSelfDensity
  rw [hA,norm_add_sq_real]
  ring

end ShrinkingSpheres.ParallelEnergy
