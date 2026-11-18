import Proof.ParallelFirstSelfWitnessIndependence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

variable {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ}

/-- First-base part of the true adjoint at its genuine weak endpoint. -/
def firstAdjointLeadingWeakRow (P : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev (-(1/2:ℝ)) :=
  -(P.firstCovariantCoordinateHalfL b y).adjoint
    (halfSectionCovariantDerivativeL d
      (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (axis b))

/-- The covariant coefficient derivative and physical density defect are
kept together. No ordinary frame derivative is estimated separately. -/
def firstAdjointDefectWeakRow (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (U : X → SphereSobolev (5/2:ℝ)) (b : I) (y : X) : SphereSobolev (-(1/2:ℝ)) :=
  -WF.covariantCoordinateAdjointDerivative b b y
      (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y))-
    ((metricDensity d.γ y)⁻¹*fderiv ℝ (metricDensity d.γ) y (axis b)) •
      (P.firstCovariantCoordinateHalfL b y).adjoint
        (sphereSobolevInclusionL (5/2:ℝ) (1/2:ℝ) (by norm_num) (U y))

/-- Exact physical adjoint normal form on the selected common core. The
real L2 output is identified through the genuine negative inclusion. -/
lemma firstFormalAdjointCoreRow_weak_normal_form
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    (b : I) {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.firstFormalAdjointCoreRow WF W U b y)=
      firstAdjointLeadingWeakRow P U b y+firstAdjointDefectWeakRow P WF U b y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hμ : metricDensity d.γ y ≠ 0 := (metricDensity_pos hg hK hy).ne'
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b
  have hGraph := P.firstAdjointDensityCoreRow_balanced_graph hY hΩ hd hK WF W U hU b hw hy
  unfold PhysicalPrincipalData.firstFormalAdjointCoreRow
  rw [map_smul,sphereSobolevInclusionL_trans_apply,hGraph]
  unfold PhysicalPrincipalData.firstAdjointBalancedDensityRow firstAdjointLeadingWeakRow firstAdjointDefectWeakRow
  simp only [smul_add,smul_smul,neg_mul,inv_mul_cancel₀ hμ,neg_one_smul]
  module

lemma firstFormalAdjointCore_weak_normal_form
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) :
    sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (P.firstFormalAdjointCore WF W U y)=
      (∑ b : I,firstAdjointLeadingWeakRow P U b y)+
        ∑ b : I,firstAdjointDefectWeakRow P WF U b y := by
  unfold PhysicalPrincipalData.firstFormalAdjointCore
  rw [map_sum,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun b _ =>
    firstFormalAdjointCoreRow_weak_normal_form hY hΩ hSub hd hK P WF W U hU b hy)

end ShrinkingSpheres.ParallelEnergy
