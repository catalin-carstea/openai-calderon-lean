import Proof.UniformFullFirstRaisingAdjointCross
import Proof.ParallelScalarModelRaising
import Proof.GradedWeightedCombinationAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Scalar drift in the complete right coefficient cancels exactly
against the genuine adjoint HIGH graph of the left coefficient. -/
lemma model_first_right_scalar_drift_commutator {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T A B : E →L[ℝ] E) (J AH BH : H →L[ℝ] E) (w : ℝ)
    (hA : T.comp AH=A.comp J) :
    A.comp (BH-w • J)-(B-w • T).comp AH=A.comp BH-B.comp AH := by
  rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp,hA]
  module

lemma model_first_weighted_commutator_graph {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : E →L[ℝ] E) (J : H →L[ℝ] E)
    (A B : I → E →L[ℝ] E) (AH BH : I → H →L[ℝ] E)
    (S : I → I → E →L[ℝ] E) (a b : I → ℝ) (w : ℝ)
    (hA : ∀ i,T.comp (AH i)=(A i).comp J)
    (hS : ∀ i j,(A i).comp (BH j)-(B j).comp (AH i)=(S i j).comp J) :
    (∑ i : I,a i • A i).comp ((∑ j : I,b j • BH j)-w • J)-
      ((∑ j : I,b j • B j)-w • T).comp (∑ i : I,a i • AH i)=
      (∑ i : I,a i • (∑ j : I,b j • S i j)).comp J := by
  have hAS : T.comp (∑ i : I,a i • AH i)=(∑ i : I,a i • A i).comp J := by
    apply ContinuousLinearMap.ext
    intro u
    have ha (i : I) := DFunLike.congr_fun (hA i) u
    simp only [ContinuousLinearMap.comp_apply] at ha
    simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,ha]
  rw [model_first_right_scalar_drift_commutator _ _ _ _ _ _ _ hAS,
    finite_real_combination_commutator_expansion]
  simp only [hS]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,Finset.smul_sum,smul_smul]

/-- The checkpoint's native raising/full-first commutator is transported
to the actual coordinate coefficient INCLUDING scalar connection drift.
The arbitrary genuine adjoint HIGH family is kept fixed. -/
theorem model_first_coordinate_raising_commutator_point
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CS : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hCS : 0 ≤ CS) (hε : 0 ≤ ε) (P : PhysicalPrincipalData Y d CF CT)
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    {y : X} (hy : y ∈ Y)
    (hCross : FullFirstRaisingAdjointCrossData P y (CS*(ε/beta d.γ d.radius y))) (b c : I) :
    ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (framedRaisingHalfL d y (axis c)).adjoint.comp (P.firstCovariantCoordinateHigherL b y)-
        (P.firstCovariantCoordinateHalfL b y).comp (scalarModelRaisingAdjointHigher A d c y)=
        S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖S‖ ≤ (9*K^2*CS)*ε/beta d.γ d.radius y := by
  have hRows (i j : I) : ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      (flatHalfRaisingL i).adjoint.comp (P.firstDerivativeHigherL y j)-
        (P.firstDerivativeHalfL y j).comp (A i)=
        S.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
        ‖S‖ ≤ CS*(ε/beta d.γ d.radius y) := (hCross.2.2 i j).1 (A i) (hA i)
  choose S hS hSN using hRows
  let a := fun i : I => frameCoordinateLinear d.γ d.frame y i (axis c)
  let e := fun j : I => d.frame y j b
  let C := ∑ i : I,a i • (∑ j : I,e j • S i j)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have ha (i : I) : |a i| ≤ K := by
    dsimp [a]
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hd.2.1.center_mem hy) hFrame c i
  have he (j : I) : |e j| ≤ K := hd.1.1.frame_component_abs_le hK d.frame (hd.2.1.center_mem hy) hFrame j b
  have hβ : 0 < beta d.γ d.radius y := zero_lt_one.trans_le (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hC : ‖C‖ ≤ 3*K*(3*K*(CS*(ε/beta d.γ d.radius y))) :=
    norm_weighted_sum_three_le a (fun i => ∑ j : I,e j • S i j) K _ (zero_le_one.trans hK) ha
      (fun i => norm_weighted_sum_three_le e (S i) K _ (zero_le_one.trans hK) he (hSN i))
  refine ⟨C,?_,hC.trans_eq (by ring)⟩
  have hRA : (framedRaisingHalfL d y (axis c)).adjoint=∑ i : I,a i • (flatHalfRaisingL i).adjoint := by
    simp only [framedRaisingHalfL,map_sum,map_smul,a]
  rw [hRA]
  exact model_first_weighted_commutator_graph
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
    (fun i => (flatHalfRaisingL i).adjoint) (P.firstDerivativeHalfL y)
    A (P.firstDerivativeHigherL y) S a e (scalarPrincipalConnectionWeight d b y) hA hS

end ShrinkingSpheres.ParallelEnergy
