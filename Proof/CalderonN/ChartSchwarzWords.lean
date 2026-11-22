module

public import Proof.CalderonN.SmallJetBounds
public import Proof.CalderonN.ChartMultilinearBound

import Proof.CalderonN.LocalMixedParameterJetCalculus
import Mathlib.Tactic

/-! A mixed derivative evaluated on chart axes depends only on the
coordinate multiplicities. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ}

@[expose] def chartDerivativeWord (L : List (I dim)) (f : X dim → ℝ) : X dim → ℝ :=
  L.foldr coordDeriv f

theorem contDiff_chartDerivativeWord (L : List (I dim)) {f : X dim → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (chartDerivativeWord L f) := by
  induction L with
  | nil => exact hf
  | cons i L ih =>
    exact (ih.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

private theorem coordDeriv_commute {f : X dim → ℝ} (hf : ContDiff ℝ ∞ f) (i j : I dim) :
    coordDeriv i (coordDeriv j f) = coordDeriv j (coordDeriv i f) := by
  funext x
  have hD := (hf.fderiv_right (m:=∞) (by simp)).differentiable (by simp) x
  change fderiv ℝ (fun y => fderiv ℝ f y (axis j)) x (axis i) =
    fderiv ℝ (fun y => fderiv ℝ f y (axis i)) x (axis j)
  rw [fderiv_clm_apply hD (differentiableAt_const (axis j)),
    fderiv_clm_apply hD (differentiableAt_const (axis i))]
  simpa only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply]
    using (hf.contDiffAt (x:=x)).isSymmSndFDerivAt (by simp) |>.eq (axis i) (axis j)

theorem chartDerivativeWord_perm {L W : List (I dim)} (h : L.Perm W)
    {f : X dim → ℝ} (hf : ContDiff ℝ ∞ f) : chartDerivativeWord L f = chartDerivativeWord W f := by
  induction h with
  | nil => rfl
  | cons a h ih => exact congrArg (coordDeriv a) ih
  | swap i j L => exact coordDeriv_commute (contDiff_chartDerivativeWord L hf) j i
  | trans h h' ih ih' => exact ih.trans ih'

theorem chartDerivativeWord_ofFn (n : ℕ) (idx : Fin n → I dim)
    {f : X dim → ℝ} (hf : ContDiff ℝ ∞ f) :
    chartDerivativeWord (List.ofFn idx) f = fun x => iteratedFDeriv ℝ n f x (fun j => axis (idx j)) := by
  induction n with
  | zero => funext x; exact (iteratedFDeriv_zero_apply _).symm
  | succ n ih =>
    rw [List.ofFn_succ]
    change coordDeriv (idx 0) (chartDerivativeWord (List.ofFn (fun j => idx j.succ)) f) = _
    rw [ih]
    funext x
    have hD := (hf.iteratedFDeriv_right (m:=∞) (by simp) (i:=n)).differentiable (by simp) x
    exact (hD.iteratedFDeriv_succ_apply_left' (m:=fun j => axis (idx j))).symm

@[expose] def sortedChartWord (a : I dim → ℕ) : List (I dim) :=
  (List.ofFn (fun i : I dim => i)).flatMap (fun i => List.replicate (a i) i)

theorem chartDerivativeWord_sorted (a : I dim → ℕ) (f : X dim → ℝ) :
    chartDerivativeWord (sortedChartWord a) f = chartPartial a f := by
  unfold sortedChartWord chartPartial chartDerivativeWord
  have hRep (k : ℕ) (i : I dim) (u : X dim → ℝ) :
      (List.replicate k i).foldr coordDeriv u = (coordDeriv i)^[k] u := by
    induction k with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ,List.foldr_cons,ih,Function.iterate_succ_apply']
  let L := List.ofFn (fun i : I dim => i)
  have hGen (u : List (I dim)) :
      (u.flatMap (fun i => List.replicate (a i) i)).foldr coordDeriv f =
        u.foldr (fun i g => (coordDeriv i)^[a i] g) f := by
    induction u with
    | nil => rfl
    | cons i u ih =>
      rw [List.flatMap_cons,List.foldr_append,List.foldr_cons,hRep,ih]
  rw [hGen]
  have hM : (List.ofFn (fun i : I dim => i)).map (fun i => (coordDeriv (E:=ℝ) i)^[a i]) =
      List.ofFn (fun i : I dim => (coordDeriv (E:=ℝ) i)^[a i]) := by simp [Function.comp_def]
  rw [← hM,List.foldr_map]

private theorem sortedChartWord_count_aux (a : I dim → ℕ) (W : List (I dim)) (j : I dim) :
    (W.flatMap (fun i => List.replicate (a i) i)).count j = W.count j*a j := by
  induction W with
  | nil => simp
  | cons i W ih =>
    rw [List.flatMap_cons,List.count_append,ih]
    by_cases h : i=j
    · subst i
      simp only [List.count_replicate,List.count_cons,beq_self_eq_true,ite_true,Nat.add_mul,one_mul]
      omega
    · have hj : j ≠ i := Ne.symm h
      simp [List.count_replicate,List.count_cons,h,hj]

theorem sortedChartWord_count (a : I dim → ℕ) (j : I dim) :
    (sortedChartWord a).count j = a j := by
  rw [sortedChartWord,sortedChartWord_count_aux]
  have hN : (List.ofFn (fun i : I dim => i)).Nodup :=
    List.nodup_ofFn.2 Function.injective_id
  have hM : j ∈ List.ofFn (fun i : I dim => i) := List.mem_ofFn.2 ⟨j,rfl⟩
  have h1 : (List.ofFn (fun i : I dim => i)).count j = 1 :=
    List.count_eq_one_of_mem hN hM
  rw [h1,one_mul]

theorem iteratedFDeriv_chart_axes_eq_chartPartial {f : X dim → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (I : Fin n → I dim) (x : X dim) :
    iteratedFDeriv ℝ n f x (fun j => axis (I j)) =
      chartPartial (fun i => (List.ofFn I).count i) f x := by
  have hP : (List.ofFn I).Perm (sortedChartWord (fun i => (List.ofFn I).count i)) :=
    List.perm_iff_count.2 fun j => (sortedChartWord_count (fun i => (List.ofFn I).count i) j).symm
  exact congrFun ((chartDerivativeWord_ofFn n I hf).symm.trans
    ((chartDerivativeWord_perm hP hf).trans (chartDerivativeWord_sorted _ _))) x

end CalderonN
