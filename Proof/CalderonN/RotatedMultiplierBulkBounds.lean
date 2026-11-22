module

public import Proof.CalderonN.DirichletMultiplierForcingBudget
public import Proof.CalderonN.LinearizedMultiplierDefect

import Proof.CalderonN.SmoothMultiplierCommutatorCompletion
import Mathlib.Tactic

/-! Strong bulk bounds for the ordinary and varied multiplication defects.
The commutator gains one derivative because its source has only one
derivative of the uncorrected Dirichlet lift. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem smoothCoefficientC1Bound_flat (G : ℝ) (hG : 1 ≤ G) :
    SmoothCoefficientC1Bound (fun _ : X dim => (1 : Mat dim)) G := by
  intro z _
  refine ⟨(Matrix.norm_le_iff (zero_le_one.trans hG)).mpr ?_,?_⟩
  · intro i j
    classical
    by_cases hij : i = j <;> simp [Matrix.one_apply,hij, hG,zero_le_one.trans hG]
  · simp [fderiv_fun_const,zero_le_one.trans hG]

theorem smoothBallSobolev_norm_le_add_sub (k : ℕ) (u v : SmoothData dim) :
    ‖smoothBallSobolev k u‖ ≤ ‖smoothBallSobolev k v‖ + ‖smoothBallSobolev k (smoothSubtractData u v)‖ := by
  let U : smoothBallDataSubmodule dim := ⟨u.1,u.2⟩
  let V : smoothBallDataSubmodule dim := ⟨v.1,v.2⟩
  let L := smoothBallSobolevLinear dim k
  change ‖L U‖ ≤ ‖L V‖ + ‖L (U-V)‖
  rw [map_sub]
  have h := norm_add_le (L V) (L U-L V)
  rwa [show L V+(L U-L V) = L U by abel] at h

theorem multiplier_defect_difference_equation
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (m u u₀ w w₀ : SmoothData dim) (z : X dim)
    (hw : negativeBallDivergence A w.1 z = -greenSourceCutoffError A m.1 u.1 z)
    (hw₀ : negativeBallDivergence (fun _ => (1 : Mat dim)) w₀.1 z =
      -greenSourceCutoffError (fun _ => (1 : Mat dim)) m.1 u₀.1 z) :
    let A₀ : X dim → Mat dim := fun _ => 1
    negativeBallDivergence A (w.1-w₀.1) z =
      -negativeBallDivergence (A-A₀) w₀.1 z -
      greenSourceCutoffError (A-A₀) m.1 u₀.1 z -
      greenSourceCutoffError A m.1 (u.1-u₀.1) z := by
  dsimp only
  let A₀ : X dim → Mat dim := fun _ => 1
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  change _ = -negativeBallDivergence (A-A₀) w₀.1 z -
    greenSourceCutoffError (A-A₀) m.1 u₀.1 z - greenSourceCutoffError A m.1 (u.1-u₀.1) z
  change negativeBallDivergence A₀ w₀.1 z = -greenSourceCutoffError A₀ m.1 u₀.1 z at hw₀
  rw [negativeBallDivergence_sub_solution hA w w₀,hw,
    negativeBallDivergence_sub_coefficient hA hA₀,
    multiplierForcing_sub_coefficients hA hA₀,multiplierForcing_sub_solution A m u u₀,hw₀]
  ring

theorem norm_rotated_multiplier_bulk_of_weak
    {A B L : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hL : ContDiff ℝ ∞ L)
    (m u u₀ p p₁ w w₀ t t₁ : SmoothData dim)
    (r C G H J : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (hC : 0 ≤ C) (hG : 1 ≤ G) (hH : 0 ≤ H) (hJ : 0 ≤ J) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let D := A-A₀
    let R := B-r • L
    let du := smoothSubtractData u u₀
    let dw := smoothSubtractData w w₀
    let e := smoothSubtractData t ⟨r • t₁.1,t₁.2.const_smul r⟩
    let ep := smoothSubtractData p ⟨r • p₁.1,p₁.2.const_smul r⟩
    let N := ‖smoothSobolev u₀‖
    let W := C*G
    let T := W*(W+1+H)
    let C_e := W*(W+3*T+4*H)
    SmoothCoefficientC1Bound A G → SmoothCoefficientC1Bound D (G*r) →
    SmoothCoefficientC1Bound R (G*r^2) → SmoothCoefficientC1Bound L G →
    DirichletMultiplierForcingBudget A₀ m J C → DirichletMultiplierForcingBudget A m J C →
    ‖smoothSobolev u‖ ≤ H*N → ‖smoothSobolev du‖ ≤ H*r*N →
    ‖smoothSobolev p₁‖ ≤ H*N → ‖smoothSobolev ep‖ ≤ H*r^2*N →
    EqOn w.1 0 (standardSphere dim) → EqOn w₀.1 0 (standardSphere dim) →
    EqOn t.1 0 (standardSphere dim) → EqOn t₁.1 0 (standardSphere dim) →
    EqOn (negativeBallDivergence A w.1) (fun z => -greenSourceCutoffError A m.1 u.1 z)
      (ball (0:X dim) 1) →
    EqOn (negativeBallDivergence A₀ w₀.1) (fun z => -greenSourceCutoffError A₀ m.1 u₀.1 z)
      (ball (0:X dim) 1) →
    EqOn (negativeBallDivergence A t.1)
      (fun z => -negativeBallDivergence B w.1 z-greenSourceCutoffError B m.1 u.1 z
        -greenSourceCutoffError A m.1 p.1 z) (ball (0:X dim) 1) →
    EqOn (negativeBallDivergence A₀ t₁.1)
      (fun z => -negativeBallDivergence L w₀.1 z-greenSourceCutoffError L m.1 u₀.1 z
        -greenSourceCutoffError A₀ m.1 p₁.1 z) (ball (0:X dim) 1) →
    ‖smoothBallSobolev 2 w₀‖ ≤ W*J*N ∧ ‖smoothBallSobolev 2 dw‖ ≤ T*J*r*N ∧
      ‖smoothBallSobolev 2 t₁‖ ≤ T*J*N ∧ ‖smoothBallSobolev 2 e‖ ≤ C_e*J*r^2*N := by
  dsimp only
  intro hCa hCd hCr hCl hI₀ hI hu hdu hp₁ hep hwT hw₀T htT ht₁T hw hw₀ ht ht₁
  let A₀ : X dim → Mat dim := fun _ => 1
  let D := A-A₀
  let R := B-r • L
  let du := smoothSubtractData u u₀
  let dw := smoothSubtractData w w₀
  let e := smoothSubtractData t ⟨r • t₁.1,t₁.2.const_smul r⟩
  let ep := smoothSubtractData p ⟨r • p₁.1,p₁.2.const_smul r⟩
  let N := ‖smoothSobolev u₀‖
  let W := C*G
  let T := W*(W+1+H)
  let C_e := W*(W+3*T+4*H)
  have hG₀ : 0 ≤ G := zero_le_one.trans hG
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hD : ContDiff ℝ ∞ D := hA.sub hA₀
  have hR : ContDiff ℝ ∞ R := hB.sub (hL.const_smul r)
  have hC₀ : SmoothCoefficientC1Bound A₀ G := smoothCoefficientC1Bound_flat G hG
  have dwT : EqOn dw.1 0 (standardSphere dim) := fun z hz => by
    change w.1 z-w₀.1 z = 0
    rw [show w.1 z = 0 from hwT hz,show w₀.1 z = 0 from hw₀T hz,sub_zero]
  have eT : EqOn e.1 0 (standardSphere dim) := fun z hz => by
    change t.1 z-r*t₁.1 z = 0
    rw [show t.1 z = 0 from htT hz,show t₁.1 z = 0 from ht₁T hz,mul_zero,sub_zero]
  have hw₀N : ‖smoothBallSobolev 2 w₀‖ ≤ W*J*N := by
    have h := hI₀ (n:=0) (l:=1) Fin.elim0 (fun _ => A₀) (fun i => Fin.elim0 i) (fun _ => hA₀)
      Fin.elim0 (fun _ => u₀) Fin.elim0 Fin.elim0 (fun _ => 1) (fun _ => G)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun _ => zero_le_one) (fun _ => hG₀)
      (fun i => Fin.elim0 i) (fun _ => hC₀) w₀ hw₀T (fun z hz => by simpa using hw₀ hz)
    simpa [W,N,Fin.sum_univ_one,mul_assoc] using h
  have hdwN : ‖smoothBallSobolev 2 dw‖ ≤ T*J*r*N := by
    have hEq := fun z hz => multiplier_defect_difference_equation hA m u u₀ w w₀ z (hw hz) (hw₀ hz)
    have h := hI (fun _ : Fin 1 => D) ![D,A] (fun _ => hD) (by intro i; fin_cases i <;> assumption)
      (fun _ => w₀) ![u₀,du] (fun _ => 1) (fun _ => G*r) ![1,1] ![G*r,G]
      (fun _ => zero_le_one) (fun _ => by positivity) (by intro i; fin_cases i <;> exact zero_le_one)
      (by intro i; fin_cases i <;> first | exact mul_nonneg hG₀ hr | exact hG₀)
      (fun _ => hCd) (by intro i; fin_cases i <;> assumption)
      dw dwT (fun z hz => by
        have heq := hEq z hz
        change negativeBallDivergence A dw.1 z =
          -negativeBallDivergence D w₀.1 z-greenSourceCutoffError D m.1 u₀.1 z-
            greenSourceCutoffError A m.1 du.1 z at heq
        rw [heq]
        simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
          Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
        ring)
    simp only [Fin.sum_univ_one,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul] at h
    refine h.trans ?_
    calc
      _ ≤ C*(G*r*(W*J*N)+(G*r*J*N+G*J*(H*r*N))) := by
        gcongr
      _ = T*J*r*N := by dsimp [T,W]; ring
  have ht₁N : ‖smoothBallSobolev 2 t₁‖ ≤ T*J*N := by
    have h := hI₀ (fun _ : Fin 1 => L) ![L,A₀] (fun _ => hL) (by intro i; fin_cases i <;> assumption)
      (fun _ => w₀) ![u₀,p₁] (fun _ => 1) (fun _ => G) ![1,1] ![G,G]
      (fun _ => zero_le_one) (fun _ => hG₀) (by intro i; fin_cases i <;> exact zero_le_one)
      (by intro i; fin_cases i <;> exact hG₀)
      (fun _ => hCl) (by intro i; fin_cases i <;> assumption)
      t₁ ht₁T (fun z hz => by
        have heq : negativeBallDivergence A₀ t₁.1 z = -negativeBallDivergence L w₀.1 z -
          greenSourceCutoffError L m.1 u₀.1 z-greenSourceCutoffError A₀ m.1 p₁.1 z := ht₁ hz
        change negativeBallDivergence A₀ t₁.1 z = _
        rw [heq]
        simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
          Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
        ring)
    simp only [Fin.sum_univ_one,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul] at h
    refine h.trans ?_
    calc
      _ ≤ C*(G*(W*J*N)+(G*J*N+G*J*(H*N))) := by
        gcongr
      _ = T*J*N := by dsimp [T,W]; ring
  have hwN : ‖smoothBallSobolev 2 w‖ ≤ (W+T)*J*N := by
    refine (smoothBallSobolev_norm_le_add_sub 2 w w₀).trans ?_
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr₁
      (show 0 ≤ T*J by dsimp only [T,W]; positivity)) (norm_nonneg (smoothSobolev u₀))
    nlinarith only [hw₀N,hdwN,h]
  refine ⟨hw₀N,hdwN,ht₁N,?_⟩
  have hEq := fun z hz => linearized_multiplier_defect_remainder_equation hA hB hL r
    m u u₀ p p₁ w w₀ t t₁ z (ht hz) (ht₁ hz)
  have h := hI ![R,L,D] ![R,L,A,D]
    (by intro i; fin_cases i <;> assumption) (by intro i; fin_cases i <;> assumption)
    ![w,dw,t₁] ![u,du,ep,p₁] ![1,r,r] ![G*r^2,G,G*r] ![1,r,1,r] ![G*r^2,G,G,G*r]
    (by intro i; fin_cases i <;> first | exact zero_le_one | exact hr)
    (by intro i; fin_cases i <;> first | exact mul_nonneg hG₀ (sq_nonneg r) | exact hG₀ | exact mul_nonneg hG₀ hr)
    (by intro i; fin_cases i <;> first | exact zero_le_one | exact hr)
    (by intro i; fin_cases i <;> first | exact mul_nonneg hG₀ (sq_nonneg r) | exact hG₀ | exact mul_nonneg hG₀ hr)
    (by intro i; fin_cases i <;> assumption) (by intro i; fin_cases i <;> assumption)
    e eT (fun z hz => by
      have hz' := hEq z hz
      dsimp only at hz'
      simp only [Fin.sum_univ_succ,Fin.sum_univ_one,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul]
      change negativeBallDivergence A (t.1-r • t₁.1) z = _
      change negativeBallDivergence A (t.1-r • t₁.1) z =
        -negativeBallDivergence R w.1 z-r*negativeBallDivergence L dw.1 z-
        greenSourceCutoffError R m.1 u.1 z-r*greenSourceCutoffError L m.1 du.1 z-
        greenSourceCutoffError A m.1 ep.1 z-r*greenSourceCutoffError D m.1 p₁.1 z-
        r*negativeBallDivergence D t₁.1 z at hz'
      rw [hz']
      ring)
  simp only [Fin.sum_univ_succ,Fin.sum_univ_one,Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,one_mul] at h
  refine h.trans ?_
  calc
    _ ≤ C*((G*r^2*((W+T)*J*N)+(r*G*(T*J*r*N)+r*(G*r)*(T*J*N)))+
      (G*r^2*J*(H*N)+(r*G*J*(H*r*N)+(G*J*(H*r^2*N)+r*(G*r)*J*(H*N))))) := by
      gcongr
    _ = C_e*J*r^2*N := by dsimp [C_e,W]; ring

end CalderonN
