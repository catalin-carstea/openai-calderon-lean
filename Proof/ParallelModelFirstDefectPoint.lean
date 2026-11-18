import Proof.ParallelModelFirstIntegrability
import Proof.ParallelFirstSelfDefectHigherBound
import Proof.ParallelScalarModelDefectPoint
import Proof.ConstantBoundaryCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.NativeHarmonicHalfCoarseDualPairing

def modelFirstDefectDensity {Y : Set X} {d : Data} {CF CT CB CS CG CK ε : ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK)
    (U : X → SphereSobolev (5/2:ℝ)) (y : X) : ℝ :=
  metricDensity d.γ y*⟪modelLoweringSection d (fiveHalfToTwoSection U) y-
    modelAdjointDefectSection d (fiveHalfToTwoSection U) y,firstAdjointDefectCoreSection P WF W U y⟫_ℝ

/-- The COMPLETE actual first-adjoint defect pairs with the corrected
model through its genuine positive-half representative, at linear epsilon
in the original half-gradient / H3/2-mass energy. -/
theorem uniform_model_first_defect_component_point_bound {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CB : ℝ) (hCB : 0 ≤ CB) (RB : ScalarModelRaisingBudget Y Ω m K ρ c₀ M Cj) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT CS CG CK : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,
      ∀ W : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK,
      ∀ U : X → SphereSobolev (5/2:ℝ),ContDiff ℝ ∞ U → ∀ y ∈ Y,
      |modelFirstDefectDensity P WF W U y| ≤ C*ε*metricDensity d.γ y*
        ∑ i : I,halfCovariantDirectionEnergy d
          (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)) y
          (beta d.γ d.radius y) (axis i) := by
  obtain ⟨η,CR,hη,hη1,hCR,hDef⟩ := uniform_first_adjoint_defect_higher_bound hY hΩ hSub hm K ρ c₀ M Cj hK hρ CB hCB
  let Q := 3*K*RB.bound
  let R := 27*K^2*RB.bound
  let C := 4*CR*Q+CR*R
  have hQ : 0 ≤ Q := by dsimp only [Q];exact mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hK)) RB.nonneg
  have hR : 0 ≤ R := by dsimp only [R];exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) RB.nonneg
  refine ⟨η,C,hη,hη1,by dsimp only [C];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT CS CG CK P WF W U hU y hy
  obtain ⟨δ,hδ,hδN⟩ := hDef floor hf ε hε hSmall d hd CF CT CS CG CK P WF W U hU.contDiffOn y hy
  obtain ⟨Qunit,hQunit⟩ := exists_unit_boundary_coefficient
  let J := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let U3 := fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)
  let V := fun i : I => J (fiveHalfCovariantDerivative d U (axis i) y)
  let s := ∑ i : I,‖V i‖
  let β := beta d.γ d.radius y
  let En := ∑ i : I,halfCovariantDirectionEnergy d U3 y β (axis i)
  have hβ : 1 ≤ β := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hKp := zero_lt_one.trans_le hK
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hV (i : I) : V i=halfSectionCovariantDerivativeL d U3 y (axis i) :=
    fiveHalfCovariantDerivative_half_inclusion d U y (axis i) (hU.differentiable (by simp) y)
  have hJU : ‖J (U3 y)‖ ≤ ‖U3 y‖ := (J.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (one_mul _))
  have hDU : ‖degreeHigherL (U3 y)‖ ≤ 2*‖U3 y‖ := (degreeHigherL.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right norm_degreeHigherL_le_two (norm_nonneg _))
  have hShift : ‖degreeHigherL (U3 y)-J (U3 y)‖ ≤ 3*‖U3 y‖ :=
    (norm_sub_le _ _).trans ((add_le_add hDU hJU).trans_eq (by ring))
  have hMN : ‖scalarModelAdjointWeakSection d U y‖ ≤ Q*s+R*β*‖U3 y‖ := by
    rw [scalarModelAdjointWeakSection_coordinate d U y hFrame]
    have hM := scalar_model_adjoint_sum_norm_bound (fun k c => (d.γ y)⁻¹ k c)
      (fun k => coordDeriv k (fun x => Real.log (d.radius x)) y) (fun c => framedRaisingHalfL d y (axis c)) V
      (degreeHigherL (U3 y)-J (U3 y)) K RB.bound β ‖U3 y‖ (zero_le_one.trans hK) RB.nonneg hβp.le (norm_nonneg _)
      (fun k c => hd.1.1.inverse_entry_bound hKp (hSub hy) k c)
      (fun k => hg.coord_logRadius_bound hK d.frame d.radius hy hFrame k)
      (fun c => (RB.actual floor ε d hd y hy 0 c).1) hShift
    simpa only [U3,J,sphereSobolevInclusionL_trans_apply,Q,R,s,V] using hM
  have hGrad : β⁻¹*(∑ i : I,‖V i‖^2) ≤ En := by
    simp only [hV,En,halfCovariantDirectionEnergy,Fin.sum_univ_three]
    nlinarith only [mul_nonneg hβp.le (sq_nonneg ‖U3 y‖)]
  have hS : s^2 ≤ 3*(∑ i : I,‖V i‖^2) := by
    simp only [s,Fin.sum_univ_three]
    nlinarith only [sq_nonneg (‖V 0‖-‖V 1‖),sq_nonneg (‖V 0‖-‖V 2‖),sq_nonneg (‖V 1‖-‖V 2‖)]
  have hGradS : β⁻¹*s^2 ≤ 3*En := by
    have hh := mul_le_mul_of_nonneg_left hS (inv_nonneg.mpr hβp.le)
    nlinarith only [hh,hGrad]
  have hMass : β*‖U3 y‖^2 ≤ En := by
    have hDir (i : I) : 0 ≤ halfCovariantDirectionEnergy d U3 y β (axis i) := by
      dsimp only [halfCovariantDirectionEnergy];positivity
    have hh := Finset.single_le_sum (f:=fun i : I => halfCovariantDirectionEnergy d U3 y β (axis i))
      (fun i _ => hDir i) (Finset.mem_univ 0)
    exact (le_add_of_nonneg_left (by positivity : 0 ≤ β⁻¹*‖halfSectionCovariantDerivativeL d U3 y (axis 0)‖^2)).trans hh
  have hPair := scalar_model_defect_pair_bound δ (scalarModelAdjointWeakSection d U y) s ‖U3 y‖
    0 CR Q R ε β En (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)
    (by norm_num) hCR hQ hR hε hβp (by simpa only [zero_mul,zero_div,zero_add] using hδN) hMN hGradS hMass
  have hWeak := scalar_model_corrected_lowering_weak_graph Qunit hQunit d U y (hU.differentiable (by simp) y)
  have hInner := sphereSobolevDualPairing_zero_inclusion (1/2:ℝ) (by norm_num) δ
    (modelLoweringSection d (fiveHalfToTwoSection U) y-modelAdjointDefectSection d (fiveHalfToTwoSection U) y)
  rw [hWeak] at hInner
  rw [real_inner_comm] at hInner
  have hμ : 0 ≤ metricDensity d.γ y := Real.sqrt_nonneg _
  change |metricDensity d.γ y*_| ≤ _
  rw [hδ,←hInner,abs_mul,abs_of_nonneg hμ]
  exact (mul_le_mul_of_nonneg_left hPair hμ).trans_eq (by dsimp only [C,En,U3,β];ring)

end ShrinkingSpheres.ParallelEnergy
