import Proof.ParallelFirstSelfAdjointSourcePoint
import Proof.ParallelFirstSelfDefectSquareIntegral
import Proof.HalfScalarTransposeCompatibility

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma first_self_inclusion_norm_le (s t : ℝ) (hst : t ≤ s) (u : SphereSobolev s) :
    ‖sphereSobolevInclusionL s t hst u‖ ≤ ‖u‖ :=
  ((sphereSobolevInclusionL s t hst).le_opNorm u).trans
    ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg u)).trans_eq (one_mul _))

lemma first_self_direction_energy_nonneg (d : Data) (V : X → SphereSobolev (3/2:ℝ))
    (y a : X) {β : ℝ} (hβ : 1 ≤ β) : 0 ≤ halfCovariantDirectionEnergy d V y β a := by
  unfold halfCovariantDirectionEnergy
  exact add_nonneg (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hβ)) (sq_nonneg _))
    (mul_nonneg (zero_le_one.trans hβ) (sq_nonneg _))

lemma first_self_direction_energy_le_total (d : Data) (V : X → SphereSobolev (3/2:ℝ))
    (y : X) {β : ℝ} (hβ : 1 ≤ β) (i : I) :
    halfCovariantDirectionEnergy d V y β (axis i) ≤ ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j) :=
  Finset.single_le_sum (fun j _ => first_self_direction_energy_nonneg d V y (axis j) hβ) (Finset.mem_univ i)

lemma first_self_mass_sq_le_total (d : Data) (V : X → SphereSobolev (3/2:ℝ))
    (y : X) {β : ℝ} (hβ : 1 ≤ β) :
    ‖V y‖^2 ≤ ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j) :=
  (half_mass_sq_le_direction_energy d V y (axis 0) hβ).trans
    (first_self_direction_energy_le_total d V y hβ 0)

lemma first_self_mass_gradient_le_total (d : Data) (V : X → SphereSobolev (3/2:ℝ))
    (y : X) {β : ℝ} (hβ : 1 ≤ β) (i : I) :
    ‖V y‖*‖halfSectionCovariantDerivativeL d V y (axis i)‖ ≤
      ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j) := by
  have h := weighted_product_le ‖halfSectionCovariantDerivativeL d V y (axis i)‖ ‖V y‖ β (zero_lt_one.trans_le hβ)
  rw [mul_comm] at h
  exact h.trans (first_self_direction_energy_le_total d V y hβ i)

/-- Jet/source and jet/jet physical pairings retain the weak orientation
which is controlled by the original H1/2 gradient energy. -/
theorem first_self_adjoint_source_error_pair_bounds
    {Y : Set X} {d : Data} {CF CT CB CS CG CK ε CA CL CJ β : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) {y : X} (hy : y ∈ Y)
    (hPoint : FirstSelfAdjointSourcePointBounds P WF W U y CA CL CJ)
    (hCL : 0 ≤ CL) (hCJ : 0 ≤ CJ) (hε : 0 ≤ ε) (hβ : 1 ≤ β) :
    let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
    let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
    let B := (CJ*(CL+CJ))*ε^2*∑ j : I,halfCovariantDirectionEnergy d V y β (axis j)
    (∀ b i c j,|⟪Z (firstSelfAdjointSourceJetError P WF W U b i y),
      Z (firstSelfAdjointSourceDerivative P WF W U c j y)⟫_ℝ| ≤ B) ∧
    (∀ b i c j,|⟪Z (firstSelfAdjointSourceJetError P WF W U b i y),
      Z (firstSelfAdjointSourceJetError P WF W U c j y)⟫_ℝ| ≤ B) := by
  dsimp only
  let V := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let E := ∑ j : I,halfCovariantDirectionEnergy d V y β (axis j)
  let T := fun b i => firstSelfAdjointSourceJetError P WF W U b i y
  let G := fun b i => firstSelfAdjointSourceDerivative P WF W U b i y
  let R := fun c j => weakHalfSourceCovariantDerivative d (WF.covariantAdjointLowSection U c) y (axis j)
  let Z := sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
  have hm : ‖V y‖^2 ≤ E := first_self_mass_sq_le_total d V y hβ
  have hmg (j : I) : ‖V y‖*‖halfSectionCovariantDerivativeL d V y (axis j)‖ ≤ E :=
    first_self_mass_gradient_le_total d V y hβ j
  have hPair (b i c j : I) : ⟪Z (T b i),Z (G c j)⟫_ℝ=sphereSobolevDualPairing (1/2:ℝ) (T b i) (R c j) := by
    have h := half_dual_pairing_inclusion (T b i) (G c j)
    have hGraph : sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num) (G c j)=R c j :=
      firstSelfAdjointSourceDerivative_weak_graph P WF W U c j hy
    rw [hGraph] at h
    exact h.symm
  constructor
  · intro b i c j
    change |⟪Z (T b i),Z (G c j)⟫_ℝ| ≤ (CJ*(CL+CJ))*ε^2*E
    rw [hPair]
    calc
      _ ≤ ‖T b i‖*‖R c j‖ := abs_sphereSobolevDualPairing_le _ _ _
      _ ≤ (CJ*ε*‖V y‖)*(ε*(CL*‖halfSectionCovariantDerivativeL d V y (axis j)‖+CJ*‖V y‖)) :=
        mul_le_mul (hPoint.error b i) (hPoint.weak c j) (norm_nonneg _) (by positivity)
      _ = (CJ*CL*ε^2)*(‖V y‖*‖halfSectionCovariantDerivativeL d V y (axis j)‖)+
          (CJ^2*ε^2)*‖V y‖^2 := by ring
      _ ≤ (CJ*CL*ε^2)*E+(CJ^2*ε^2)*E := add_le_add
        (mul_le_mul_of_nonneg_left (hmg j) (by positivity)) (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = _ := by ring
  · intro b i c j
    change |⟪Z (T b i),Z (T c j)⟫_ℝ| ≤ (CJ*(CL+CJ))*ε^2*E
    have hTN (b i : I) : ‖Z (T b i)‖ ≤ CJ*ε*‖V y‖ :=
      (first_self_inclusion_norm_le (1/2:ℝ) 0 (by norm_num) (T b i)).trans (hPoint.error b i)
    calc
      _ ≤ ‖Z (T b i)‖*‖Z (T c j)‖ := abs_real_inner_le_norm _ _
      _ ≤ (CJ*ε*‖V y‖)*(CJ*ε*‖V y‖) := mul_le_mul (hTN b i) (hTN c j) (norm_nonneg _) (by positivity)
      _ = (CJ^2*ε^2)*‖V y‖^2 := by ring
      _ ≤ (CJ^2*ε^2)*E := mul_le_mul_of_nonneg_left hm (by positivity)
      _ ≤ (CJ*(CL+CJ)*ε^2)*E := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg hCJ hCL] : CJ^2 ≤ CJ*(CL+CJ)) (sq_nonneg ε))
        (Finset.sum_nonneg (fun j _ => first_self_direction_energy_nonneg d V y (axis j) hβ))

end ShrinkingSpheres.ParallelEnergy
