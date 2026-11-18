import Proof.ParallelModelFirstZeroJet
import Proof.ParallelModelFirstWeights
import Proof.ParallelFirstSelfCompleteAdjointJet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma norm_modelFirstShiftedDegreeHigh_le_three : ‖modelFirstShiftedDegreeHigh‖ ≤ 3 :=
  (norm_sub_le _ _).trans ((add_le_add norm_degreeHigherL_le_two (norm_sphereSobolevInclusionL_le _ _ _)).trans_eq (by norm_num))

lemma model_first_zero_adjoint_norm_bounds (d : Data) (c i : I) (y : X) (Q : ℝ) (hQ : 0 ≤ Q)
    (hR : ‖framedRaisingHalfL d y (axis c)‖ ≤ Q) (hD : ‖framedRaisingFirstHalfJet d i c y‖ ≤ Q) :
    ‖modelFirstZeroAdjointWeakL d c y‖ ≤ 3*Q ∧ ‖modelFirstZeroAdjointWeakJet d c i y‖ ≤ 3*Q := by
  constructor
  · exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hR) norm_modelFirstShiftedDegreeHigh_le_three (norm_nonneg _) hQ)).trans_eq (mul_comm _ _)
  · exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hD) norm_modelFirstShiftedDegreeHigh_le_three (norm_nonneg _) hQ)).trans_eq (mul_comm _ _)

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε CE : ℝ}

/-- One coefficient first-jet family is selected from the already fixed
actual WF BEFORE source sections. It is never differentiated. -/
def modelFirstChosenAdjointJet {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (hJ : FirstSelfCompleteAdjointJetBound WF CE)
    (b i : I) (y : X) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := by
  classical
  exact if hy : y ∈ Y then Classical.choose (hJ.jet b i y hy) else 0

lemma modelFirstChosenAdjointJet_spec {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (hJ : FirstSelfCompleteAdjointJetBound WF CE)
    (b i : I) {y : X} (hy : y ∈ Y) :
    WF.effectiveAdjointCovariantDerivative b i y=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelFirstChosenAdjointJet WF hJ b i y) ∧
      ‖modelFirstChosenAdjointJet WF hJ b i y‖ ≤ CE*ε := by
  simpa only [modelFirstChosenAdjointJet,dite_eq_left hy] using Classical.choose_spec (hJ.jet b i y hy)

lemma modelFirstChosenAdjointJet_higher_graph
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (hJ : FirstSelfCompleteAdjointJetBound WF CE) (b i : I) {y : X} (hy : y ∈ Y) :
    higherOperatorCovariantDerivativeL d (WF.covariantCoordinateAdjointHigher b) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
        ((modelFirstChosenAdjointJet WF hJ b i y).comp (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num))) := by
  have hw := hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b
  have hC := (P.firstCovariantCoordinateAdjoint_smooth hd hY hΩ hK b hw).contDiffAt (hY.mem_nhds hy)
  have hH := (WF.covariantCoordinateAdjointHigher_smooth hd b hw).contDiffAt (hY.mem_nhds hy)
  have hNear : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (WF.covariantCoordinateAdjointHigher b x)=
      (P.firstCovariantCoordinateHalfL b x).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact WF.covariantCoordinateAdjointHigher_balanced b hx
  rw [higher_covariant_derivative_eq_half d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
    (WF.covariantCoordinateAdjointHigher b) y (axis i) hC hH hNear]
  have hHalf : halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
      (WF.covariantCoordinateAdjointHigher b) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelFirstChosenAdjointJet WF hJ b i y) :=
    (modelFirstChosenAdjointJet_spec WF hJ b i hy).1
  rw [hHalf,ContinuousLinearMap.comp_assoc]

def modelFirstZeroPairedDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ k : I,∑ c : I,∑ b : I,quadraticHigherPairDensity d (modelFirstZeroWeight d k c)
    (WF.covariantCoordinateAdjointHigher b) (modelFirstZeroAdjointWeakL d c) U (axis b) y

def modelFirstZeroPairedRemainder {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (hJ : FirstSelfCompleteAdjointJetBound WF CE)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  ∑ k : I,∑ c : I,∑ b : I,quadraticHigherPairRemainder (modelFirstZeroWeight d k c)
    (WF.covariantCoordinateAdjointHigher b) (modelFirstChosenAdjointJet WF hJ b b)
    (modelFirstZeroAdjointWeakL d c) (modelFirstZeroAdjointWeakJet d c b) U (axis b) y

/-- Exact paired zero-model Green reduction through the imported generic
quadratic interface. The SAME actual complete B† HIGH and genuine H5/2
source are used, with only FIRST HIGH and first quadratic coefficient jets. -/
theorem model_first_zero_paired_integral_reduction
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hJ : FirstSelfCompleteAdjointJetBound WF CE)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (hU0 : ∀ x ∉ S,U x=0) :
    IntegrableOn (modelFirstZeroPairedDensity P WF U) Y ∧ IntegrableOn (modelFirstZeroPairedRemainder WF hJ U) Y ∧
      (∫ y in Y,modelFirstZeroPairedDensity P WF U y)=∫ y in Y,modelFirstZeroPairedRemainder WF hJ U y := by
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hLog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y :=
    hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
  have hq (k c : I) : ContDiffOn ℝ ∞ (modelFirstZeroWeight d k c) Y :=
    ((hg.contDiffOn_density hK).mul (hg.contDiffOn_inverse_entry hK k c)).mul (contDiffOn_coordDeriv hY hLog k)
  have hH (b : I) := WF.covariantCoordinateAdjointHigher_smooth hd b
    (hd.contDiffOn_scalarPrincipalConnectionWeight hY hSub hK b)
  have hC (c : I) : ContDiffOn ℝ ∞ (modelFirstZeroAdjointWeakL d c) Y :=
    (scalarModelRaisingAdjoint_smooth hd c).clm_comp contDiffOn_const
  have hEach (k c b : I) := quadratic_higher_paired_mass_reduction hY d (axis b) hg hK he
    (modelFirstZeroWeight d k c) (hq k c) (WF.covariantCoordinateAdjointHigher b) (hH b)
    (modelFirstZeroAdjointWeakL d c) (hC c) (modelFirstChosenAdjointJet WF hJ b b) (modelFirstZeroAdjointWeakJet d c b)
    (fun x hx => modelFirstChosenAdjointJet_higher_graph hY hΩ hSub hd hK P WF hJ b b hx)
    (fun x hx => model_first_zero_adjoint_weak_jet_graph hY hΩ hd hK hx c b)
    U hU (P.firstCovariantAdjointFiveHalfSection W U b)
    (fun x hx => firstSelfAdjointSource_higher_graph P WF W U b hx) S hS hSY hU0
  exact model_first_finite_green_family Y _ _ (fun k =>
    model_first_finite_green_family Y _ _ (fun c => model_first_finite_green_family Y _ _ (hEach k c)))

end ShrinkingSpheres.ParallelEnergy
