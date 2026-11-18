import Proof.CoordinateSecondJetCalculus
import Proof.HessianDifferential
import Proof.MetricSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma covJet_three (g : MetricField) (f : X → ℝ) (y : X) (i j k : I) :
    covJet g f 3 y ![i,j,k] = coordDeriv i (fun x => covJet g f 2 x ![j,k]) y-
      (∑ l,christoffel g y l i j*covJet g f 2 y ![l,k])-
      (∑ l,christoffel g y l i k*covJet g f 2 y ![j,l]) := by
  have hTail : Fin.tail ![i,j,k] = ![j,k] := rfl
  have hU0 (l : I) : Function.update ![j,k] (0:Fin 2) l = ![l,k] := by
    ext t
    fin_cases t <;> simp
  have hU1 (l : I) : Function.update ![j,k] (1:Fin 2) l = ![j,l] := by
    ext t
    fin_cases t <;> simp
  change coordDeriv i (fun x => covJet g f 2 x (Fin.tail ![i,j,k])) y-
    (∑ t : Fin 2,∑ l,christoffel g y l i (![i,j,k] t.succ)*
      covJet g f 2 y (Function.update (Fin.tail ![i,j,k]) t l)) = _
  rw [hTail,Fin.sum_univ_two]
  simp only [hU0,hU1,show (0:Fin 2).succ = (1:Fin 3) from rfl,
    show (1:Fin 2).succ = (2:Fin 3) from rfl,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring

/-- Exact conversion of a scalar third covariant jet to coordinates. The
connection corrections are explicit, so all profile constants stay tied to
the actual metric rather than to derivatives of a chosen frame. -/
theorem coordinate_third_of_covJet {Y : Set X} (hY : IsOpen Y) (g : MetricField) (f : X → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y)
    (hΓ : ∀ a b c : I,ContDiffOn ℝ ∞ (fun x => christoffel g x a b c) Y)
    {y : X} (hy : y ∈ Y) (i j k : I) :
    coordDeriv i (coordDeriv j (coordDeriv k f)) y = covJet g f 3 y ![i,j,k]+
      (∑ l,((coordDeriv i (fun x => christoffel g x l j k) y)*coordDeriv l f y+
        christoffel g y l j k*coordDeriv i (coordDeriv l f) y))+
      (∑ l,christoffel g y l i j*covJet g f 2 y ![l,k])+
      (∑ l,christoffel g y l i k*covJet g f 2 y ![j,l]) := by
  let F := fun l (x : X) => christoffel g x l j k*coordDeriv l f x
  have hDF (l : I) : DifferentiableAt ℝ (F l) y :=
    ((hΓ l j k).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp) |>.fun_mul
      (((contDiffOn_coordDeriv hY hf l).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
  have hDSum : HasFDerivAt (fun x => ∑ l,F l x) (∑ l,fderiv ℝ (F l) y) y :=
    HasFDerivAt.fun_sum (fun l _ => (hDF l).hasFDerivAt)
  have hD2 : DifferentiableAt ℝ (coordDeriv j (coordDeriv k f)) y :=
    ((contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY hf k) j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hEq : (fun x => covJet g f 2 x ![j,k]) =ᶠ[𝓝 y]
      (fun x => coordDeriv j (coordDeriv k f) x-∑ l,F l x) :=
    Filter.Eventually.of_forall (fun x => covJet_two g f x j k)
  have hH : coordDeriv i (fun x => covJet g f 2 x ![j,k]) y =
      coordDeriv i (coordDeriv j (coordDeriv k f)) y-
      (∑ l,((coordDeriv i (fun x => christoffel g x l j k) y)*coordDeriv l f y+
        christoffel g y l j k*coordDeriv i (coordDeriv l f) y)) := by
    change fderiv ℝ (fun x => covJet g f 2 x ![j,k]) y (axis i) = _
    rw [hEq.fderiv_eq,fderiv_fun_sub hD2 hDSum.differentiableAt,hDSum.fderiv]
    simp only [_root_.sub_apply,_root_.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have hDL := ((contDiffOn_coordDeriv hY hf l).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    have hDG := ((hΓ l j k).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
    rw [hDG.hasFDerivAt.fun_mul hDL.hasFDerivAt |>.fderiv]
    simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,coordDeriv]
    ring
  have hC := covJet_three g f y i j k
  rw [hH] at hC
  linarith only [hC]

end ShrinkingSpheres
