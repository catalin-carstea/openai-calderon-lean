module

public import Proof.CalderonN.CoordinateTraceDivergence
public import Proof.CalderonN.WeightedCoordinateTracePairing

import Mathlib.Tactic

/-! After one integration by parts, the coordinate commutators are
pairings of regular coefficients applied to at most one base
derivative of either test factor. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

namespace RegularTraceFiberFamily

@[expose] def comm (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) : RegularTraceFiberFamily Y :=
  (F.mul hY G).sub (G.mul hY F)

theorem action_comm (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) :
    (F.comm hY G).action hY = F.action hY*G.action hY-G.action hY*F.action hY := by
  simp only [comm,action_sub,action_mul]

end RegularTraceFiberFamily

private theorem comm_sum_left {R ι : Type*} [Ring R] [Fintype ι] (P : ι → R) (Q A : R) :
    ((∑ k,P k)+Q)*A-A*((∑ k,P k)+Q) = (∑ k,(P k*A-A*P k))+(Q*A-A*Q) := by
  rw [Finset.sum_sub_distrib (fun k => P k*A) (fun k => A*P k)]
  simp only [add_mul,mul_add,Finset.mul_sum,Finset.sum_mul]
  abel

private theorem comm_sum_right {R ι : Type*} [Ring R] [Fintype ι] (P : ι → R) (Q A : R) :
    A*((∑ k,P k)+Q)-((∑ k,P k)+Q)*A = (∑ k,(A*P k-P k*A))+(A*Q-Q*A) := by
  rw [Finset.sum_sub_distrib (fun k => A*P k) (fun k => P k*A)]
  simp only [add_mul,mul_add,Finset.mul_sum,Finset.sum_mul]
  abel

namespace CoordinateTraceFirstOrder

@[expose] def coordinateDerivative (hY : IsOpen Y) (j : I dim) (S : CoordinateTraceFirstOrder Y) :
    CoordinateTraceFirstOrder Y :=
  ⟨fun i => (S.first i).derivative hY (axis j),S.zero.derivative hY (axis j)⟩

theorem coordinateDerivative_action (hY : IsOpen Y) (j : I dim) (S : CoordinateTraceFirstOrder Y) :
    (S.coordinateDerivative hY j).action hY =
      smoothSupportedTraceBaseDiff (axis j)*S.action hY-S.action hY*smoothSupportedTraceBaseDiff (axis j) := by
  let D₀ := smoothSupportedTraceBaseDiff (Y:=Y) (axis j)
  let P (i : I dim) := (S.first i).action hY
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let Q := S.zero.action hY
  change (∑ i,((S.first i).derivative hY (axis j)).action hY*D i)+(S.zero.derivative hY (axis j)).action hY =
    D₀*((∑ i,P i*D i)+Q)-((∑ i,P i*D i)+Q)*D₀
  rw [comm_sum_right (fun k => P k*D k) Q D₀]
  simp only [RegularTraceFiberFamily.action_derivative]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have h := commutator_base_first_differentiation (P i) 0 (D i) D₀ (smoothSupportedTraceBaseDiff_comm _ _)
    simpa only [add_zero,mul_zero,zero_mul,sub_self] using h.symm

theorem comm_scalar_action (hY : IsOpen Y) (S : CoordinateTraceFirstOrder Y) (a : RegularTraceFiberFamily Y)
    (hA : ∀ F : RegularTraceFiberFamily Y,F.action hY*a.action hY = a.action hY*F.action hY) :
    S.action hY*a.action hY-a.action hY*S.action hY =
      ∑ k,((S.first k).mul hY (a.derivative hY (axis k))).action hY := by
  let A₀ := a.action hY
  let P (k : I dim) := (S.first k).action hY
  let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
  have h (k : I dim) : (P k*D k)*A₀-A₀*(P k*D k) = P k*(D k*A₀-A₀*D k) := by
    have h' := commutator_base_first_scalar (P k) 0 A₀ (D k) (hA (S.first k)) (by rw [zero_mul,mul_zero])
    simpa only [add_zero] using h'
  change ((∑ k,P k*D k)+S.zero.action hY)*A₀-A₀*((∑ k,P k*D k)+S.zero.action hY) = _
  rw [comm_sum_left (fun k => P k*D k) (S.zero.action hY) A₀,hA S.zero,sub_self,add_zero]
  simp only [RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_derivative]
  exact Finset.sum_congr rfl (fun k _ => h k)

end CoordinateTraceFirstOrder

section Pairings

variable (B : SmoothSupportedTraceSection Y →ₗ[ℝ] SmoothSupportedTraceSection Y →ₗ[ℝ] ℝ)
variable (hY : IsOpen Y)

@[expose] def coordinateCoefficientPair
    (P Q : RegularTraceFiberFamily Y) (i j : Option (I dim)) (u : SmoothSupportedTraceSection Y) : ℝ :=
  B (P.action hY (traceCoordinateTest u i)) (Q.action hY (traceCoordinateTest u j))

theorem paired_coordinate_comm_divergence
    (S Sd : CoordinateTraceFirstOrder Y) (a : RegularTraceFiberFamily Y) (Dd : Module.End ℝ (SmoothSupportedTraceSection Y))
    (i j : I dim) (u : SmoothSupportedTraceSection Y)
    (hSym : ∀ u v,B u v = B v u) (hS : PairedAdjoint B (S.action hY) (Sd.action hY))
    (hD : PairedAdjoint B (smoothSupportedTraceBaseDiff (axis i)) Dd)
    (ha : ∀ F : RegularTraceFiberFamily Y,F.action hY*a.action hY = a.action hY*F.action hY) :
    let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
    let A := Dd*a.action hY*D j
    let I₀ := (RegularTraceFiberFamily.scalar hY (fun _ => 1) contDiffOn_const)
    let p (P Q : RegularTraceFiberFamily Y) (i j : Option (I dim)) := coordinateCoefficientPair B hY P Q i j u
    B ((S.action hY*A-A*S.action hY) u) u =
      (∑ k,(p a ((Sd.first k).derivative hY (axis i)) (some j) (some k)+
        p ((S.first k).mul hY (a.derivative hY (axis k))) I₀ (some j) (some i)-
        p (a.mul hY ((S.first k).derivative hY (axis j))) I₀ (some k) (some i)))+
      p a (Sd.zero.derivative hY (axis i)) (some j) none-
      p (a.mul hY (S.zero.derivative hY (axis j))) I₀ none (some i) := by
  dsimp only
  rw [paired_commutator_divergence_form _ _ _ _ _ _ hSym hS hD u,
    ← Sd.coordinateDerivative_action,S.comm_scalar_action hY a ha,
    show S.action hY*smoothSupportedTraceBaseDiff (axis j)-smoothSupportedTraceBaseDiff (axis j)*S.action hY =
      -(S.coordinateDerivative hY j).action hY by rw [S.coordinateDerivative_action]; abel]
  have hId : (RegularTraceFiberFamily.scalar hY (fun _ => 1) contDiffOn_const).action hY =
      (1 : Module.End ℝ (SmoothSupportedTraceSection Y)) := by
    ext w : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x _
    simp only [RegularTraceFiberFamily.action_fiber,RegularTraceFiberFamily.scalar,one_smul,Module.End.one_apply]
  simp only [CoordinateTraceFirstOrder.action,CoordinateTraceFirstOrder.coordinateDerivative,coordinateCoefficientPair,
    traceCoordinateTest,hId,Module.End.one_apply,LinearMap.add_apply,LinearMap.neg_apply,Module.End.mul_apply,
    LinearMap.sum_apply,map_neg,map_sum,map_add,LinearMap.sum_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    RegularTraceFiberFamily.action_mul]
  ring

theorem paired_coordinate_comm_first
    (S : CoordinateTraceFirstOrder Y) (b : RegularTraceFiberFamily Y) (density : I dim → RegularTraceFiberFamily Y)
    (Dd : I dim → Module.End ℝ (SmoothSupportedTraceSection Y))
    (j : I dim) (u : SmoothSupportedTraceSection Y)
    (hSym : ∀ u v,B u v = B v u)
    (hD : ∀ i,PairedAdjoint B (smoothSupportedTraceBaseDiff (axis i)) (Dd i))
    (hDd : ∀ i,Dd i = -smoothSupportedTraceBaseDiff (axis i)-(density i).action hY) :
    let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
    let P (k : I dim) := (S.first k).action hY
    let A := b.action hY*D j
    let C (k : I dim) := (S.first k).comm hY b
    B ((S.action hY*A-A*S.action hY) u) u =
      (∑ k,(-B ((C k).action hY (D j u)) (D k u)+
        B ((((S.first k).mul hY (b.derivative hY (axis k))).sub
          (((C k).derivative hY (axis k)).add ((density k).mul hY (C k)))).action hY (D j u)) u-
        B ((b.mul hY ((S.first k).derivative hY (axis j))).action hY (D k u)) u))+
      B ((S.zero.comm hY b).action hY (D j u)) u-B ((b.mul hY (S.zero.derivative hY (axis j))).action hY u) u := by
  dsimp only
  let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
  let P (k : I dim) := (S.first k).action hY
  let Q := S.zero.action hY
  let A := b.action hY*D j
  let C (k : I dim) := (S.first k).comm hY b
  have h (k : I dim) :
      B (((P k*D k)*A-A*(P k*D k)) u) u =
        -B ((C k).action hY (D j u)) (D k u)+
        B ((((S.first k).mul hY (b.derivative hY (axis k))).sub
          (((C k).derivative hY (axis k)).add ((density k).mul hY (C k)))).action hY (D j u)) u-
        B ((b.mul hY ((S.first k).derivative hY (axis j))).action hY (D k u)) u := by
    simpa only [A,C,P,D,RegularTraceFiberFamily.action_comm,RegularTraceFiberFamily.action_sub,
      RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_mul,RegularTraceFiberFamily.action_derivative,
      Module.End.mul_apply] using paired_commutator_base_one_one (B:=B)
      (P k) (b.action hY) (D k) (D j) (Dd k) ((density k).action hY)
      (smoothSupportedTraceBaseDiff_comm _ _) (hDd k) hSym (hD k) u
  have hEq : S.action hY*A-A*S.action hY =
      (∑ k,((P k*D k)*A-A*(P k*D k)))+(Q*A-A*Q) :=
    comm_sum_left (fun k => P k*D k) Q A
  rw [hEq]
  simp only [LinearMap.add_apply,LinearMap.sum_apply,map_add,map_sum]
  have hb : Q*A-A*Q = (Q*b.action hY-b.action hY*Q)*D j-b.action hY*(D j*Q-Q*D j) :=
    commutator_base_zero_one Q (b.action hY) (D j)
  simp only [h,hb]
  simp only [C,D,P,Q,RegularTraceFiberFamily.action_comm,RegularTraceFiberFamily.action_mul,
    RegularTraceFiberFamily.action_derivative,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  ring

theorem paired_coordinate_comm_zero
    (S : CoordinateTraceFirstOrder Y) (c : RegularTraceFiberFamily Y) (u : SmoothSupportedTraceSection Y) :
    let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
    let A := c.action hY
    B ((S.action hY*A-A*S.action hY) u) u =
      (∑ k,(B (((S.first k).comm hY c).action hY (D k u)) u+
        B (((S.first k).mul hY (c.derivative hY (axis k))).action hY u) u))+
      B ((S.zero.comm hY c).action hY u) u := by
  dsimp only
  let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
  let P (k : I dim) := (S.first k).action hY
  let Q := S.zero.action hY
  let A := c.action hY
  have hEq : S.action hY*A-A*S.action hY =
      (∑ k,((P k*D k)*A-A*(P k*D k)))+(Q*A-A*Q) :=
    comm_sum_left (fun k => P k*D k) Q A
  rw [hEq]
  have h (k : I dim) : (P k*D k)*A-A*(P k*D k) =
      (P k*A-A*P k)*D k+P k*(D k*A-A*D k) := by
    have h' := commutator_first_zero_normal (P k) 0 A (D k)
    simpa only [add_zero,zero_mul,mul_zero,sub_self] using h'
  simp only [h,D,P,Q,A,RegularTraceFiberFamily.action_comm,RegularTraceFiberFamily.action_mul,
    RegularTraceFiberFamily.action_derivative,LinearMap.add_apply,LinearMap.sum_apply,map_add,map_sum,
    Module.End.mul_apply]

end Pairings

end CalderonN
