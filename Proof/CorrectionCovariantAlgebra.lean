import Proof.ScaledFrameLogRadius
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Abel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace ShrinkingSpheres

theorem fderiv_operator_comp_add_smul {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : P → E →L[ℝ] E) (t : P → ℝ) (N : E →L[ℝ] E) (y a : P)
    (hB : DifferentiableAt ℝ B y) (ht : DifferentiableAt ℝ t y) :
    fderiv ℝ (fun x => (B x).comp N+t x • B x) y a =
      (fderiv ℝ B y a).comp N+t y • fderiv ℝ B y a+fderiv ℝ t y a • B y := by
  have hComp := hB.hasFDerivAt.clm_comp (hasFDerivAt_const (𝕜:=ℝ) N y)
  have hScale := ht.hasFDerivAt.smul hB.hasFDerivAt
  have hSum := hComp.add hScale
  have hField : (fun x => (B x).comp N+t x • B x) =
      (fun x => (B x).comp N)+t • B := by
    funext x
    rfl
  rw [hField,hSum.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_zero,zero_add]
  abel

/-- The first-correction commutator is a product commutator plus the
    covariant derivative of its scalar coefficient. All frame rows cancel. -/
theorem correction_covariant_algebra {E1 E0 : Type*}
    [NormedAddCommGroup E1] [NormedSpace ℝ E1] [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    (I0 L : E1 →L[ℝ] E0) (B1 : E1 →L[ℝ] E1) (B0 DB J : E0 →L[ℝ] E0)
    (M1 : I → E1 →L[ℝ] E1) (M0 : I → E0 →L[ℝ] E0)
    (A : I → I → ℝ) (t : I → ℝ) (i : I) (dt : ℝ)
    (hMI : ∀ v,I0 (M1 i v) = M0 i (I0 v))
    (hB : ∀ v,DB (I0 v)+L (B1 v)-B0 (L v) = J (I0 v))
    (hM : ∀ v,L (M1 i v)-M0 i (L v) = (∑ k : I,A i k • M0 k) (I0 v)) (u : E1) :
    (DB (M0 i (I0 u))+t i • DB (I0 u)+dt • B0 (I0 u))+
      L (B1 (M1 i u)+t i • B1 u)-
      (B0 (M0 i (L u))+t i • B0 (L u))-
      (∑ k : I,A i k • (B0 (M0 k (I0 u))+t k • B0 (I0 u))) =
    J (M0 i (I0 u))+t i • J (I0 u)+(dt-∑ k : I,A i k*t k) • B0 (I0 u) := by
  have hSum : (∑ k : I,A i k • (B0 (M0 k (I0 u))+t k • B0 (I0 u))) =
      B0 ((∑ k : I,A i k • M0 k) (I0 u))+(∑ k : I,A i k*t k) • B0 (I0 u) := by
    simp only [smul_add,smul_smul,Finset.sum_add_distrib,_root_.sum_apply,_root_.smul_apply,
      map_sum,map_smul,Finset.sum_smul]
  have hM' := sub_eq_iff_eq_add.mp (hM u)
  have hBx := hB (M1 i u)
  rw [hMI u,hM',map_add] at hBx
  have hL : L (B1 (M1 i u)) = J (M0 i (I0 u))-DB (M0 i (I0 u))+
      B0 ((∑ k : I,A i k • M0 k) (I0 u))+B0 (M0 i (L u)) := by
    calc
      _ = (DB (M0 i (I0 u))+L (B1 (M1 i u)))-DB (M0 i (I0 u)) := by abel
      _ = (J (M0 i (I0 u))+(B0 ((∑ k : I,A i k • M0 k) (I0 u))+B0 (M0 i (L u))))-
          DB (M0 i (I0 u)) := congrArg (fun z : E0 => z-DB (M0 i (I0 u))) (sub_eq_iff_eq_add.mp hBx)
      _ = _ := by abel
  have hBu : L (B1 u) = J (I0 u)-DB (I0 u)+B0 (L u) := by
    calc
      _ = (DB (I0 u)+L (B1 u))-DB (I0 u) := by abel
      _ = (J (I0 u)+B0 (L u))-DB (I0 u) :=
        congrArg (fun z : E0 => z-DB (I0 u)) (sub_eq_iff_eq_add.mp (hB u))
      _ = _ := by abel
  simp only [map_add,map_smul]
  rw [hL,hBu,hSum]
  simp only [smul_add,smul_sub,sub_smul]
  abel

end ShrinkingSpheres
