module

public import Proof.CalderonN.CarlemanCalculus
import Mathlib.Tactic

/-! Adapted from `Calderon/CollaboratorUCPIdentityOct17.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

/-! # Pointwise integration-by-parts identities for the Carleman estimate -/

noncomputable section
open MeasureTheory
open scoped ContDiff
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
namespace CalderonN.Carleman

variable {d : ℕ}

/-- `div(a ∇f)` in coordinates. -/
def Lop (a : Fin d → Fin d → (CalderonN.X d) → ℝ) (f : (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) : ℝ :=
  ∑ i, pd i (fun z => ∑ k, a i k z * pd k f z) x

/-- Divergence of a vector field. -/
def divV (X : Fin d → (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) : ℝ := ∑ j, pd j (X j) x

/-- Quadratic form `ξ ⬝ a(x) ξ`. -/
def quad (a : Fin d → Fin d → (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) (ξ : Fin d → ℝ) : ℝ :=
  ∑ i, ∑ k, a i k x * ξ i * ξ k

/-- Coordinate gradient. -/
def grad (v : (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) : Fin d → ℝ := fun i => pd i v x

section
variable (a : Fin d → Fin d → (CalderonN.X d) → ℝ) (X : Fin d → (CalderonN.X d) → ℝ) (q θ v : (CalderonN.X d) → ℝ)

/-- Symmetric part `S v = div(a∇v) + q v`. -/
def Sop (x : (CalderonN.X d)) : ℝ := Lop a v x + q x * v x

/-- Antisymmetric part `B v = -2 X·∇v - (div X) v`. -/
def Bop (x : (CalderonN.X d)) : ℝ := -2 * ∑ j, X j x * pd j v x - divV X x * v x

/-- Gradient coefficient of `2 ∫ S v B v`. -/
def Mgrad (x : (CalderonN.X d)) (ξ : Fin d → ℝ) : ℝ :=
  4 * ∑ i, ∑ j, ∑ l, a i l x * ξ l * pd i (X j) x * ξ j -
    2 * ∑ j, X j x * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k

/-- Zero-order coefficient of `2 ∫ S v B v`. -/
def mzero (x : (CalderonN.X d)) : ℝ := 2 * ∑ j, X j x * pd j q x - Lop a (divV X) x

/-- Flux for `2 S v B v`. -/
def F1 (i : Fin d) (x : (CalderonN.X d)) : ℝ :=
  -4 * (∑ k, a i k x * pd k v x) * (∑ j, X j x * pd j v x) + 2 * quad a x (grad v x) * X i x -
    2 * (∑ k, a i k x * pd k v x) * divV X x * v x +
    v x * v x * (∑ k, a i k x * pd k (divV X) x) - 2 * q x * (v x * v x) * X i x

/-- Flux for `-2 θ v S v`. -/
def F2 (i : Fin d) (x : (CalderonN.X d)) : ℝ :=
  -2 * θ x * v x * (∑ k, a i k x * pd k v x) + v x * v x * (∑ k, a i k x * pd k θ x)

end

@[fun_prop]
theorem contDiff_divV {X : Fin d → (CalderonN.X d) → ℝ} (hX : ∀ j, ContDiff ℝ ∞ (X j)) :
    ContDiff ℝ ∞ (divV X) := by
  unfold divV; fun_prop

theorem sum_flux_comm (a : Fin d → Fin d → ℝ) (ha : ∀ i j, a i j = a j i)
    (u v : Fin d → ℝ) :
    (∑ i, u i * (∑ j, a i j * v j)) = ∑ i, v i * (∑ j, a i j * u j) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ha j i]
  ring

theorem quad_eq_flux (a : Fin d → Fin d → (CalderonN.X d) → ℝ)
    (x : CalderonN.X d) (u : Fin d → ℝ) :
    quad a x u = ∑ i, u i * (∑ j, a i j x * u j) := by
  simp only [quad, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem identity2 {a : Fin d → Fin d → (CalderonN.X d) → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {q θ v : (CalderonN.X d) → ℝ} (hq : ContDiff ℝ ∞ q)
    (hθ : ContDiff ℝ ∞ θ) (hv : ContDiff ℝ ∞ v) (x : (CalderonN.X d)) :
    -2 * θ x * v x * Sop a q v x =
      2 * θ x * quad a x (grad v x) - Lop a θ x * (v x * v x) - 2 * θ x * q x * (v x * v x) +
        ∑ i, pd i (F2 a θ v i) x := by
  let A (i : Fin d) (y : CalderonN.X d) := ∑ k, a i k y * pd k v y
  let B (i : Fin d) (y : CalderonN.X d) := ∑ k, a i k y * pd k θ y
  have hA (i : Fin d) : ContDiff ℝ ∞ (A i) := by
    dsimp only [A]
    fun_prop
  have hB (i : Fin d) : ContDiff ℝ ∞ (B i) := by
    dsimp only [B]
    fun_prop
  have hD (i : Fin d) : pd i (F2 a θ v i) x =
      (-2 * v x) * (pd i θ x * A i x) + (-2 * θ x) * (pd i v x * A i x) +
      (-2 * θ x * v x) * pd i (A i) x +
      (2 * v x) * (pd i v x * B i x) + (v x * v x) * pd i (B i) x := by
    change pd i (fun y => -2 * θ y * v y * A i y + v y * v y * B i y) x = _
    simp (disch := fun_prop) only [pd_add, pd_mul, pd_const]
    ring
  have hS : (∑ i, pd i θ x * A i x) = ∑ i, pd i v x * B i x :=
    sum_flux_comm (fun i j => a i j x) (fun i j => congrFun (hsymm i j) x) _ _
  simp_rw [hD]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hS]
  rw [quad_eq_flux]
  change -2 * θ x * v x * (Lop a v x + q x * v x) =
    2 * θ x * (∑ i, pd i v x * A i x) - Lop a θ x * (v x * v x) -
    2 * θ x * q x * (v x * v x) +
    ((-2 * v x) * (∑ i, pd i v x * B i x) + (-2 * θ x) * (∑ i, pd i v x * A i x) +
      (-2 * θ x * v x) * Lop a v x + (2 * v x) * (∑ i, pd i v x * B i x) +
      (v x * v x) * Lop a θ x)
  ring

theorem identity1 {a : Fin d → Fin d → (CalderonN.X d) → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {X : Fin d → (CalderonN.X d) → ℝ} (hX : ∀ j, ContDiff ℝ ∞ (X j))
    {q v : (CalderonN.X d) → ℝ} (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (x : (CalderonN.X d)) :
    2 * Sop a q v x * Bop X v x =
      Mgrad a X x (grad v x) + mzero a X q x * (v x * v x) + ∑ i, pd i (F1 a X q v i) x := by
  let A (i : Fin d) (y : CalderonN.X d) := ∑ k, a i k y * pd k v y
  let D := divV X
  let B (i : Fin d) (y : CalderonN.X d) := ∑ k, a i k y * pd k D y
  let P (y : CalderonN.X d) := ∑ j, X j y * pd j v y
  let Q (y : CalderonN.X d) := quad a y (grad v y)
  let T (j : Fin d) := ∑ i, A i x * pd j (pd i v) x
  let R (j : Fin d) := ∑ i, ∑ k, pd j (a i k) x * pd i v x * pd k v x
  let J := ∑ i, A i x * ∑ j, pd i (X j) x * pd j v x
  have hD : ContDiff ℝ ∞ D := contDiff_divV hX
  have hA (i : Fin d) : ContDiff ℝ ∞ (A i) := by
    dsimp only [A]
    fun_prop
  have hB (i : Fin d) : ContDiff ℝ ∞ (B i) := by
    dsimp only [B]
    fun_prop
  have hP : ContDiff ℝ ∞ P := by
    dsimp only [P]
    fun_prop
  have hQ : ContDiff ℝ ∞ Q := by
    simp only [Q, quad, grad]
    fun_prop
  have hQF (y : CalderonN.X d) : Q y = ∑ i, pd i v y * A i y := quad_eq_flux a y _
  have hQd (j : Fin d) : pd j Q x = R j + 2 * T j := by
    have hF : Q = fun y => ∑ i, pd i v y * A i y := funext hQF
    rw [hF]
    simp (disch := fun_prop) only [pd_sum, pd_mul]
    rw [Finset.sum_add_distrib]
    have hSplit (i : Fin d) : pd j (A i) x =
        (∑ k, pd j (a i k) x * pd k v x) + ∑ k, a i k x * pd j (pd k v) x := by
      simp (disch := fun_prop) only [A, pd_sum, pd_mul, Finset.sum_add_distrib]
    simp_rw [hSplit, mul_add, Finset.sum_add_distrib]
    have hR : (∑ i, pd i v x * ∑ k, pd j (a i k) x * pd k v x) = R j := by
      simp only [R, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hR, sum_flux_comm (fun i k => a i k x) (fun i k => congrFun (hsymm i k) x)
      (fun i => pd i v x) (fun i => pd j (pd i v) x)]
    have hT : (∑ i, pd j (pd i v) x * A i x) = T j :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hT]
    change T j + (R j + T j) = _
    ring
  have hPd : (∑ i, A i x * pd i P x) = J + ∑ j, X j x * T j := by
    simp (disch := fun_prop) only [P, pd_sum, pd_mul, Finset.sum_add_distrib, mul_add]
    congr 1
    simp only [Finset.mul_sum, T]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun (pd_comm (i := i) (j := j) hv) x]
    ring
  have hM : Mgrad a X x (grad v x) = 4 * J - 2 * ∑ j, X j x * R j := by
    simp only [Mgrad, J, R, grad]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.mul_sum, A, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hStep (i : Fin d) : pd i (F1 a X q v i) x =
      (-4 * P x) * pd i (A i) x - 4 * (A i x * pd i P x) +
      2 * (X i x * pd i Q x) + (2 * Q x) * pd i (X i) x -
      (2 * D x * v x) * pd i (A i) x - (2 * v x) * (pd i D x * A i x) -
      (2 * D x) * (pd i v x * A i x) + (2 * v x) * (pd i v x * B i x) +
      (v x * v x) * pd i (B i) x - (2 * (v x * v x)) * (X i x * pd i q x) -
      (4 * q x * v x) * (X i x * pd i v x) - (2 * q x * (v x * v x)) * pd i (X i) x := by
    change pd i (fun y =>
      -4 * A i y * P y + 2 * Q y * X i y - 2 * A i y * D y * v y +
        v y * v y * B i y - 2 * q y * (v y * v y) * X i y) x = _
    simp (disch := fun_prop) only [pd_add, pd_sub, pd_mul, pd_const]
    ring
  have hS : (∑ i, pd i D x * A i x) = ∑ i, pd i v x * B i x :=
    sum_flux_comm (fun i j => a i j x) (fun i j => congrFun (hsymm i j) x) _ _
  have hQsum : (∑ i, X i x * pd i Q x) =
      (∑ i, X i x * R i) + 2 * (∑ i, X i x * T i) := by
    simp_rw [hQd, mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hM]
  simp_rw [hStep]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hPd, hQsum, hS, ← hQF]
  change 2 * (Lop a v x + q x * v x) * (-2 * P x - D x * v x) = _
  change _ = 4 * J - 2 * (∑ j, X j x * R j) +
    (2 * (∑ j, X j x * pd j q x) - Lop a D x) * (v x * v x) +
    ((-4 * P x) * Lop a v x - 4 * (J + ∑ j, X j x * T j) +
    2 * ((∑ j, X j x * R j) + 2 * (∑ j, X j x * T j)) + (2 * Q x) * D x -
    (2 * D x * v x) * Lop a v x - (2 * v x) * (∑ i, pd i v x * B i x) -
    (2 * D x) * Q x + (2 * v x) * (∑ i, pd i v x * B i x) +
    (v x * v x) * Lop a D x - (2 * (v x * v x)) * (∑ i, X i x * pd i q x) -
    (4 * q x * v x) * P x - (2 * q x * (v x * v x)) * D x)
  ring

theorem conj_identity {a : Fin d → Fin d → (CalderonN.X d) → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {Φ v : (CalderonN.X d) → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (hv : ContDiff ℝ ∞ v) (x : (CalderonN.X d)) :
    Lop a (fun y => Real.exp (-Φ y) * v y) x =
      Real.exp (-Φ x) * (Sop a (fun y => ∑ i, ∑ k, a i k y * pd i Φ y * pd k Φ y) v x +
        Bop (fun j y => ∑ k, a j k y * pd k Φ y) v x) := by
  let A (i : Fin d) (y : CalderonN.X d) := ∑ k, a i k y * pd k v y
  let B (i : Fin d) (y : CalderonN.X d) := ∑ k, a i k y * pd k Φ y
  let E (y : CalderonN.X d) := Real.exp (-Φ y)
  have hA (i : Fin d) : ContDiff ℝ ∞ (A i) := by
    dsimp only [A]
    fun_prop
  have hB (i : Fin d) : ContDiff ℝ ∞ (B i) := by
    dsimp only [B]
    fun_prop
  have hE : ContDiff ℝ ∞ E := hΦ.neg.exp
  have hF (i : Fin d) : (fun y => ∑ k, a i k y * pd k (fun z => E z * v z) y) =
      fun y => E y * (A i y - v y * B i y) := by
    funext y
    simp (disch := fun_prop) only [E, pd_mul, pd_exp, pd_neg, A, B, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  change Lop a (fun y => E y * v y) x = _
  unfold Lop
  simp_rw [hF]
  have hStep (i : Fin d) : pd i (fun y => E y * (A i y - v y * B i y)) x =
      E x * (pd i (A i) x - pd i v x * B i x - v x * pd i (B i) x -
        pd i Φ x * A i x + v x * (pd i Φ x * B i x)) := by
    simp (disch := fun_prop) only [E, pd_mul, pd_sub, pd_exp, pd_neg]
    ring
  simp_rw [hStep]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_flux_comm (fun i j => a i j x) (fun i j => congrFun (hsymm i j) x)
    (fun i => pd i Φ x) (fun i => pd i v x)]
  change _ = E x * ((Lop a v x + quad a x (fun i => pd i Φ x) * v x) + Bop B v x)
  rw [quad_eq_flux]
  change E x * ((∑ i, pd i (A i) x) - (∑ i, pd i v x * B i x) -
    v x * (∑ i, pd i (B i) x) - (∑ i, pd i v x * B i x) +
    v x * (∑ i, pd i Φ x * B i x)) =
    E x * (((∑ i, pd i (A i) x) + (∑ i, pd i Φ x * B i x) * v x) +
      (-2 * (∑ i, B i x * pd i v x) - (∑ i, pd i (B i) x) * v x))
  have hComm : (∑ i, B i x * pd i v x) = ∑ i, pd i v x * B i x :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hComm]
  ring

section integral
variable {v : (CalderonN.X d) → ℝ}

theorem pd_eq_zero_of_notMem {x : (CalderonN.X d)} (hx : x ∉ tsupport v) (k : Fin d) : pd k v x = 0 := by
  simp [pd, fderiv_of_notMem_tsupport ℝ hx]

theorem tsupport_pd_subset (k : Fin d) : tsupport (pd k v) ⊆ tsupport v := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro y hy
  by_contra h
  exact hy (pd_eq_zero_of_notMem h k)

theorem vanish_outside {x : (CalderonN.X d)} (hx : x ∉ tsupport v) :
    v x = 0 ∧ (∀ k, pd k v x = 0) ∧ ∀ i k, pd i (pd k v) x = 0 :=
  ⟨image_eq_zero_of_notMem_tsupport hx, pd_eq_zero_of_notMem hx,
    fun i k => pd_eq_zero_of_notMem (fun h => hx (tsupport_pd_subset k h)) i⟩

theorem integrable_of_vanish {f : (CalderonN.X d) → ℝ} (hf : Continuous f) (hvc : HasCompactSupport v)
    (h : ∀ x ∉ tsupport v, f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hvc h)

end integral

/-- The integrand bounded below in the Carleman estimate. -/
def Qfun (a : Fin d → Fin d → (CalderonN.X d) → ℝ) (X : Fin d → (CalderonN.X d) → ℝ) (q θ : (CalderonN.X d) → ℝ) (κ : ℝ) (v : (CalderonN.X d) → ℝ)
    (x : (CalderonN.X d)) : ℝ :=
  Mgrad a X x (grad v x) + 2 * κ * θ x * quad a x (grad v x) +
    (mzero a X q x - κ * Lop a θ x - 2 * κ * θ x * q x - κ * θ x ^ 2) * (v x * v x)

section
variable {a : Fin d → Fin d → (CalderonN.X d) → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {X : Fin d → (CalderonN.X d) → ℝ} (hX : ∀ j, ContDiff ℝ ∞ (X j))
    {q θ v : (CalderonN.X d) → ℝ} (hq : ContDiff ℝ ∞ q) (hθ : ContDiff ℝ ∞ θ) (hv : ContDiff ℝ ∞ v)
include ha hX hq hθ hv

theorem Sop_vanish {x : (CalderonN.X d)} (hx : x ∉ tsupport v) : Sop a q v x = 0 := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  obtain ⟨h0, h1, h2⟩ := vanish_outside hx
  simp only [Sop, Lop]
  simp (disch := fun_prop) only [pd_mul, pd_sum]
  simp [h0, h1, h2]

theorem Bop_vanish {x : (CalderonN.X d)} (hx : x ∉ tsupport v) : Bop X v x = 0 := by
  obtain ⟨h0, h1, h2⟩ := vanish_outside hx
  simp [Bop, h0, h1]

theorem contDiff_Sop : ContDiff ℝ ∞ (Sop a q v) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold Sop Lop; fun_prop

theorem contDiff_Bop : ContDiff ℝ ∞ (Bop X v) := by
  have : ∀ j, ContDiff ℝ ∞ (fun y => X j y) := hX
  have := contDiff_divV hX
  unfold Bop; fun_prop

theorem contDiff_F1 (i : Fin d) : ContDiff ℝ ∞ (F1 a X q v i) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  have : ∀ j, ContDiff ℝ ∞ (fun y => X j y) := hX
  have := contDiff_divV hX
  unfold F1 quad grad; fun_prop

theorem contDiff_F2 (i : Fin d) : ContDiff ℝ ∞ (F2 a θ v i) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold F2; fun_prop

theorem hasCompactSupport_F (hvc : HasCompactSupport v) (κ : ℝ) (i : Fin d) :
    HasCompactSupport (fun x => F1 a X q v i x + κ * F2 a θ v i x) := by
  apply HasCompactSupport.intro hvc
  intro x hx
  obtain ⟨h0, h1, h2⟩ := vanish_outside hx
  simp [F1, F2, quad, grad, h0, h1]

theorem integral_Qfun_le (hsymm : ∀ i k, a i k = a k i) (hvc : HasCompactSupport v) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
    Integrable (Qfun a X q θ κ v) ∧
      ∫ x, Qfun a X q θ κ v x ≤ ∫ x, (Sop a q v x + Bop X v x) ^ 2 := by
  set G : Fin d → (CalderonN.X d) → ℝ := fun i x => F1 a X q v i x + κ * F2 a θ v i x with hG
  have hGs : ∀ i, ContDiff ℝ ∞ (G i) := fun i =>
    (contDiff_F1 ha hX hq hθ hv i).add (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i))
  have hGc : ∀ i, HasCompactSupport (G i) := hasCompactSupport_F ha hX hq hθ hv hvc κ
  set H : (CalderonN.X d) → ℝ := fun x => 2 * Sop a q v x * Bop X v x - 2 * κ * θ x * v x * Sop a q v x -
    κ * θ x ^ 2 * (v x * v x) with hH
  have hHQ : ∀ x, H x = Qfun a X q θ κ v x + ∑ i, pd i (G i) x := by
    intro x
    have e1 := identity1 ha hsymm hX hq hv x
    have e2 := identity2 ha hsymm hq hθ hv x
    have hpdG : ∀ i, pd i (G i) x = pd i (F1 a X q v i) x + κ * pd i (F2 a θ v i) x := by
      intro i
      simp only [hG]
      rw [pd_add (contDiff_F1 ha hX hq hθ hv i)
        (contDiff_const.mul (contDiff_F2 ha hX hq hθ hv i)),
        pd_const_mul _ (contDiff_F2 ha hX hq hθ hv i)]
    simp only [hpdG, Finset.sum_add_distrib, ← Finset.mul_sum, hH, Qfun]
    linear_combination e1 + κ * e2
  have hS := contDiff_Sop (q := q) ha hX hq hθ hv
  have hB := contDiff_Bop (a := a) (q := q) ha hX hq hθ hv
  have hHi : Integrable H := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [hH, Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx,
        image_eq_zero_of_notMem_tsupport hx]
    · simp only [hH]; fun_prop
  have hSBi : Integrable (fun x => (Sop a q v x + Bop X v x) ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [Sop_vanish ha hX hq hθ hv hx, Bop_vanish ha hX hq hθ hv hx]
    · fun_prop
  have hdi : ∀ i, Integrable (pd i (G i)) := fun i =>
    integrable_of_contDiff_hasCompactSupport (contDiff_pd (hGs i)) (hasCompactSupport_pd (hGc i))
  have hQeq : Qfun a X q θ κ v = fun x => H x - ∑ i, pd i (G i) x := by
    funext x; rw [hHQ x]; ring
  have hQi : Integrable (Qfun a X q θ κ v) := by
    rw [hQeq]; exact hHi.sub (integrable_finsetSum _ fun i _ => hdi i)
  refine ⟨hQi, ?_⟩
  have hint : ∫ x, H x = ∫ x, Qfun a X q θ κ v x := by
    have : ∫ x, ∑ i, pd i (G i) x = 0 := by
      rw [integral_finsetSum _ fun i _ => hdi i]
      simp [integral_pd_eq_zero (hGs _) (hGc _)]
    rw [hQeq, integral_sub hHi (integrable_finsetSum _ fun i _ => hdi i), this, sub_zero]
  rw [← hint]
  apply integral_mono hHi hSBi
  intro x
  simp only [hH]
  nlinarith [sq_nonneg (Bop X v x), mul_nonneg (sub_nonneg.2 hκ1) (sq_nonneg (Sop a q v x)),
    mul_nonneg hκ0 (sq_nonneg (Sop a q v x + θ x * v x))]

end

end CalderonN.Carleman
