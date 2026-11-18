import Proof.ParallelModelFirstNormalForm
import Proof.ParallelModelFirstHodgeIntegral
import Proof.ParallelModelFirstHodgePoint
import Proof.ParallelFirstSelfAdjointSourcePoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma model_first_component_energy_controls (d : Data) (V : X → SphereSobolev (3/2:ℝ))
    (y : X) (β : ℝ) (hβ : 1 ≤ β) :
    β*‖V y‖^2 ≤ ∑ i : I,halfCovariantDirectionEnergy d V y β (axis i) ∧
    ∀ i : I,β⁻¹*‖halfSectionCovariantDerivativeL d V y (axis i)‖^2 ≤
      ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j) := by
  have hβ0 := zero_le_one.trans hβ
  have hDir (i : I) : 0 ≤ halfCovariantDirectionEnergy d V y β (axis i) := by
    dsimp only [halfCovariantDirectionEnergy];positivity
  have hLe (i : I) := Finset.single_le_sum (f:=fun j : I => halfCovariantDirectionEnergy d V y β (axis j))
    (fun j _ => hDir j) (Finset.mem_univ i)
  constructor
  · exact (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d V y (axis 0)‖^2)).trans (hLe 0)
  · intro i
    exact (le_add_of_nonneg_right (mul_nonneg hβ0 (sq_nonneg ‖V y‖))).trans (hLe i)

variable {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}

def modelFirstAngularCommutatorDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
  metricDensity d.γ y*∑ k : I,∑ c : I,∑ b : I,(d.γ y)⁻¹ k c*(
    ⟪Z (framedRaisingHigherL d y (axis c) (fiveHalfCovariantDerivative d U (axis k) y)),
      Z (P.firstCovariantCoordinateHigherL b y (fiveHalfCovariantDerivative d U (axis b) y))⟫_ℝ-
    ⟪Z (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y (fiveHalfCovariantDerivative d U (axis b) y)),
      Z (WF.covariantCoordinateAdjointHigher b y (fiveHalfCovariantDerivative d U (axis k) y))⟫_ℝ)

def modelFirstCrossedDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num);
  metricDensity d.γ y*∑ k : I,∑ c : I,∑ b : I,(d.γ y)⁻¹ k c*(
    ⟪Z (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y (fiveHalfCovariantDerivative d U (axis b) y)),
      Z (WF.covariantCoordinateAdjointHigher b y (fiveHalfCovariantDerivative d U (axis k) y))⟫_ℝ-
    ⟪Z (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y (fiveHalfCovariantDerivative d U (axis k) y)),
      Z (WF.covariantCoordinateAdjointHigher b y (fiveHalfCovariantDerivative d U (axis b) y))⟫_ℝ)

def modelFirstJetDensity (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  modelFirstCrossedDensity P WF U y-modelFirstHodgeDensity P WF W U y

lemma modelFirstLeadingDensity_hodge_split (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) :
    modelFirstLeadingDensity P WF U y=modelFirstAngularCommutatorDensity P WF U y+
      modelFirstHodgeDensity P WF W U y+modelFirstJetDensity P WF W U y := by
  unfold modelFirstJetDensity
  have hTerm : modelFirstLeadingDensity P WF U y=
      modelFirstAngularCommutatorDensity P WF U y+modelFirstCrossedDensity P WF U y := by
    unfold modelFirstLeadingDensity modelFirstAngularCommutatorDensity modelFirstCrossedDensity
    dsimp only
    rw [←mul_add,←Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  linarith only [hTerm]

/-- The actual angular commutator density is bounded without assigning
any measurability or regularity to a selected pointwise low extension. -/
theorem model_first_actual_commutator_point_bound
    {Ω : Set X} {m : ℕ} {K ρ c₀ floor Q : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hQ : 0 ≤ Q) (hε : 0 ≤ ε) (P : PhysicalPrincipalData Y d CF CT)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (U : X → SphereSobolev (5/2:ℝ))
    {y : X} (hy : y ∈ Y) (hU : DifferentiableAt ℝ U y)
    (hC : ∀ c b,∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (framedRaisingHalfL d y (axis c)).adjoint.comp (P.firstCovariantCoordinateHigherL b y)-
        (P.firstCovariantCoordinateHalfL b y).comp
          (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y)=
        S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖S‖ ≤ Q*ε/beta d.γ d.radius y) :
    |modelFirstAngularCommutatorDensity P WF U y| ≤ 54*K*Q*ε*metricDensity d.γ y*
      ∑ i : I,halfCovariantDirectionEnergy d
        (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y (beta d.γ d.radius y) (axis i) := by
  choose C hC hCN using hC
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let H := fun k : I => fiveHalfCovariantDerivative d U (axis k) y
  let V := fun k : I => J (H k)
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let β := beta d.γ d.radius y
  let En := ∑ i : I,halfCovariantDirectionEnergy d U3 y β (axis i)
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hV (i : I) : V i=halfSectionCovariantDerivativeL d U3 y (axis i) := fiveHalfCovariantDerivative_half_inclusion d U y (axis i) hU
  have hRow (k c b : I) := first_leading_row_commutator_identity (framedRaisingHalfL d y (axis c))
    (P.firstCovariantCoordinateHalfL b y) (framedRaisingHigherL d y (axis c)) (P.firstCovariantCoordinateHigherL b y)
    (scalarModelRaisingAdjointHigher modelFirstFlatAdjointHigher d c y) (WF.covariantCoordinateAdjointHigher b y) (C c b)
    (framedRaisingHalf_balanced d y (axis c)) (WF.covariantCoordinateAdjointHigher_balanced b hy) (hC c b) (H k) (H b)
  have hEq : modelFirstAngularCommutatorDensity P WF U y=
      metricDensity d.γ y*∑ k : I,∑ c : I,∑ b : I,(d.γ y)⁻¹ k c*sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b)) := by
    unfold modelFirstAngularCommutatorDensity
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    have hr := hRow k c b
    exact congrArg (fun t : ℝ => (d.γ y)⁻¹ k c*t) (by linarith only [hr])
  have hGrad (i : I) : β⁻¹*‖V i‖^2 ≤ En := by
    rw [hV]
    exact (model_first_component_energy_controls d U3 y β hβ).2 i
  rw [hEq]
  have hSwap : (∑ k : I,∑ c : I,∑ b : I,(d.γ y)⁻¹ k c*sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b)))=
      ∑ k : I,∑ b : I,∑ c : I,(d.γ y)⁻¹ k c*sphereSobolevDualPairing (1/2:ℝ) (V k) (C c b (V b)) := by
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_comm)
  rw [hSwap]
  exact model_first_leading_commutator_point_bound C V (fun k c => (d.γ y)⁻¹ k c) K Q ε β (metricDensity d.γ y) En
    (zero_le_one.trans hK) hQ hε (zero_lt_one.trans_le hβ) (Real.sqrt_nonneg _) hCN
    (fun k c => hd.1.1.inverse_entry_bound (zero_lt_one.trans_le hK) (hd.2.1.center_mem hy) k c) hGrad

end ShrinkingSpheres.ParallelEnergy
