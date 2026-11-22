module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

/- Port of the 3D Theorem 3.1 release (check 55d37bfe), same module name
   under Proof.LocalMetricExtension. -/

noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology BigOperators

namespace CalderonN

variable {n : ℕ}

private def contract (A B : Mat n) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

private theorem contract_add (A B C : Mat n) :
    contract A (B + C) = contract A B + contract A C := by
  simp only [contract, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

private theorem contract_smul (A B : Mat n) (c : ℝ) :
    contract A (c • B) = c * contract A B := by
  simp only [contract, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem smul_contract (A B : Mat n) (c : ℝ) :
    contract (c • A) B = c * contract A B := by
  simp only [contract, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private def lowerConnection (g : MetricField n) (x : X n) (k : I n) : Mat n :=
  fun i j => coordDeriv i (fun z => g z k j) x +
    coordDeriv j (fun z => g z i k) x - coordDeriv k (fun z => g z i j) x

private theorem mul_christoffel {g : MetricField n} {x : X n} (hg : (g x).PosDef)
    (k i j : I n) :
    (∑ l, g x k l * christoffel g x l i j) = lowerConnection g x k i j / 2 := by
  let v (m : I n) := coordDeriv i (fun z => g z m j) x +
    coordDeriv j (fun z => g z i m) x - coordDeriv m (fun z => g z i j) x
  calc
    _ = ((g x) *ᵥ ((g x)⁻¹ *ᵥ v)) k / 2 := by
      simp only [christoffel, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc, v]
    _ = _ := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'),
        Matrix.one_mulVec]
      rfl

/-- The harmonic coordinate equation with the free connection index lowered
by the positive definite metric. -/
private theorem contract_lowerConnection_eq_zero {Ω : Set (X n)} {g : MetricField n}
    (hc : HarmonicCoordinates Ω g) {x : X n} (hx : x ∈ Ω) (hg : (g x).PosDef) (k : I n) :
    contract (g x)⁻¹ (lowerConnection g x k) = 0 := by
  have hz : (∑ l, g x k l *
      (∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x l i j)) = 0 := by
    simp only [contracted_christoffel_eq_zero hc hx, mul_zero, Finset.sum_const_zero]
  have he :
      contract (g x)⁻¹ (lowerConnection g x k) / 2 =
        ∑ l, g x k l * (∑ i, ∑ j, (g x)⁻¹ i j * christoffel g x l i j) := by
    simp only [contract, Finset.sum_div]
    calc
      _ = ∑ i, ∑ j, (g x)⁻¹ i j * (∑ l, g x k l * christoffel g x l i j) := by
        simp_rw [mul_christoffel hg, mul_div_assoc]
      _ = ∑ i, ∑ l, ∑ j, g x k l * ((g x)⁻¹ i j * christoffel g x l i j) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      _ = _ := by simp only [Finset.mul_sum]; exact Finset.sum_comm
  rw [hz] at he
  exact (div_eq_zero_iff.mp he).resolve_right (by norm_num)

private def scaleCorrection (A : Mat n) (d : I n → ℝ) (k : I n) : Mat n :=
  fun i j => d i * A k j + d j * A i k - d k * A i j

/-- The correction to the contracted connection has coefficient 2−n. -/
private theorem contract_scaleCorrection {A : Mat n} (hA : A.PosDef)
    (d : I n → ℝ) (k : I n) : contract A⁻¹ (scaleCorrection A d k) = (2 - (n : ℝ)) * d k := by
  have hinv : A⁻¹ * A = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  have hsym (i j : I n) : A i j = A j i := by
    simpa only [star_trivial] using (hA.isHermitian.apply j i)
  have hisym (i j : I n) : A⁻¹ i j = A⁻¹ j i := by
    simpa only [star_trivial] using (hA.inv.isHermitian.apply j i)
  have h₁ : (∑ i, ∑ j, A⁻¹ i j * (d i * A k j)) = d k := by
    calc
      _ = ∑ i, (A⁻¹ * A) i k * d i := by
        apply Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.mul_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl fun j _ => ?_
        rw [hsym k j]
        ring
      _ = _ := by simp [hinv, Matrix.one_apply, ite_mul]
  have h₂ : (∑ i, ∑ j, A⁻¹ i j * (d j * A i k)) = d k := by
    calc
      _ = ∑ i, ∑ j, A⁻¹ j i * (d i * A j k) := Finset.sum_comm
      _ = ∑ i, ∑ j, A⁻¹ i j * (d i * A k j) := by
        apply Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hisym j i, hsym j k]
      _ = _ := h₁
  have h₃ : (∑ i, ∑ j, A⁻¹ i j * (d k * A i j)) = (n : ℝ) * d k := by
    calc
      _ = ∑ i, (A⁻¹ * A) i i * d k := by
        apply Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.mul_apply, Finset.sum_mul]
        apply Finset.sum_congr rfl fun j _ => ?_
        rw [hsym i j]
        ring
      _ = _ := by simp [hinv, I]
  simp only [contract, scaleCorrection, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, h₁, h₂, h₃]
  ring

private theorem lowerConnection_of_smul {U : Set (X n)} (hU : IsOpen U)
    {g₁ g₂ : MetricField n} {c : X n → ℝ} (hg₁ : SmoothMetric U g₁)
    (heq : EqOn g₂ (fun z => c z • g₁ z) U) {x : X n} (hx : x ∈ U)
    (hc : DifferentiableAt ℝ c x) (k : I n) :
    lowerConnection g₂ x k =
      c x • lowerConnection g₁ x k + scaleCorrection (g₁ x) (fun i => coordDeriv i c x) k := by
  have hderiv (i j l : I n) :
      coordDeriv i (fun z => g₂ z j l) x =
        c x * coordDeriv i (fun z => g₁ z j l) x + coordDeriv i c x * g₁ x j l := by
    have he : (fun z => g₂ z j l) =ᶠ[𝓝 x] (fun z => c z * g₁ z j l) := by
      filter_upwards [hU.mem_nhds hx] with z hz
      exact congrArg (fun A : Mat n => A j l) (heq hz)
    have hg₁' : DifferentiableAt ℝ (fun z => g₁ z j l) x :=
      ((hg₁.1 j l).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    unfold coordDeriv
    rw [he.fderiv_eq, fderiv_fun_mul hc hg₁']
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  ext i j
  simp only [lowerConnection, scaleCorrection, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    hderiv]
  ring

/-- Christoffel symbols under a smooth positive scalar change of metric. -/
theorem christoffel_of_conformal_smul {U : Set (X n)} (hU : IsOpen U)
    {g : MetricField n} (hg : SmoothMetric U g) {c : X n → ℝ} {x : X n} (hx : x ∈ U)
    (hc : DifferentiableAt ℝ c x) (hpos : 0 < c x) (k i j : I n) :
    christoffel (fun y => c y • g y) x k i j = christoffel g x k i j +
      ((if k = j then coordDeriv i c x else 0) + (if k = i then coordDeriv j c x else 0) -
        g x i j * (∑ l, (g x)⁻¹ k l * coordDeriv l c x)) / (2 * c x) := by
  let B := g x
  let d (l : I n) := coordDeriv l c x
  let u : ℝˣ := Units.mk0 (c x) hpos.ne'
  have hB : B.PosDef := hg.2 x hx
  have hinv : (c x • B)⁻¹ = (c x)⁻¹ • B⁻¹ :=
    Matrix.inv_smul' _ u (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  have hi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  have hs (a b : I n) : B a b = B b a :=
    congrFun (congrFun hB.isHermitian.isSymm.eq b) a
  have hlow := fun l => congrArg (fun A : Mat n => A i j)
    (lowerConnection_of_smul hU hg (fun _ _ => rfl) hx hc l)
  have hmain : christoffel (fun y => c y • g y) x k i j =
      (∑ l, ((c x)⁻¹ * B⁻¹ k l) *
        (c x * lowerConnection g x l i j + scaleCorrection B d l i j)) / 2 := by
    change (∑ l, (c x • B)⁻¹ k l * lowerConnection (fun y => c y • g y) x l i j) / 2 = _
    simp only [hinv, Matrix.smul_apply, smul_eq_mul, hlow, Matrix.add_apply, B, d]
  have hsplit :
      (∑ l, ((c x)⁻¹ * B⁻¹ k l) *
        (c x * lowerConnection g x l i j + scaleCorrection B d l i j)) =
      (∑ l, B⁻¹ k l * lowerConnection g x l i j) +
        (c x)⁻¹ * ∑ l, B⁻¹ k l * scaleCorrection B d l i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl fun l _ => ?_
    field_simp [hpos.ne']
  have hleft : ∑ l, B⁻¹ k l * (d i * B l j) = if k = j then d i else 0 := by
    calc
      _ = d i * (B⁻¹ * B) k j := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl fun _ _ => ?_
        ring
      _ = _ := by simp [hi, Matrix.one_apply]
  have hright : ∑ l, B⁻¹ k l * (d j * B i l) = if k = i then d j else 0 := by
    calc
      _ = d j * (B⁻¹ * B) k i := by
        simp only [Matrix.mul_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl fun l _ => ?_
        rw [hs i l]
        ring
      _ = _ := by simp [hi, Matrix.one_apply]
  have hthird : ∑ l, B⁻¹ k l * (d l * B i j) = B i j * ∑ l, B⁻¹ k l * d l := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [hmain, hsplit]
  simp only [scaleCorrection, mul_add, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hleft, hright, hthird]
  change ((_ : ℝ) + _) / 2 = (∑ l, B⁻¹ k l * lowerConnection g x l i j) / 2 + _
  field_simp [hpos.ne']
  rfl

/-- The common harmonic coordinates in dimension at least three force a positive conformal factor
to be constant on the connected chart. An agreed metric value fixes it. -/
theorem metric_eqOn_of_harmonic_conformal (hn : 3 ≤ n)
    {U : Set (X n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    {g₁ g₂ : MetricField n} (hg₁ : SmoothMetric U g₁) (hg₂ : SmoothMetric U g₂)
    (h₁ : HarmonicCoordinates U g₁) (h₂ : HarmonicCoordinates U g₂)
    {c : X n → ℝ} (hc : DifferentiableOn ℝ c U) (hcpos : ∀ x ∈ U, 0 < c x)
    (hconformal : EqOn g₂ (fun x => c x • g₁ x) U)
    {x₀ : X n} (hx₀ : x₀ ∈ U) (hmatch : g₁ x₀ = g₂ x₀) :
    EqOn g₁ g₂ U := by
  have hcoord (x : X n) (hx : x ∈ U) (k : I n) : coordDeriv k c x = 0 := by
    let u : ℝˣ := Units.mk0 (c x) (hcpos x hx).ne'
    have hInv : (g₂ x)⁻¹ = (c x)⁻¹ • (g₁ x)⁻¹ := by
      rw [hconformal hx]
      exact Matrix.inv_smul' _ u (isUnit_iff_ne_zero.mpr (hg₁.2 x hx).det_pos.ne')
    have hL₁ := contract_lowerConnection_eq_zero h₁ hx (hg₁.2 x hx) k
    have hL₂ := contract_lowerConnection_eq_zero h₂ hx (hg₂.2 x hx) k
    rw [hInv, lowerConnection_of_smul hU hg₁ hconformal hx (hc.differentiableAt (hU.mem_nhds hx)),
      smul_contract, contract_add, contract_smul, hL₁, mul_zero, zero_add,
      contract_scaleCorrection (hg₁.2 x hx)] at hL₂
    have hneg := (mul_eq_zero.mp hL₂).resolve_left (inv_ne_zero (hcpos x hx).ne')
    have htwo : (2 : ℝ) - (n : ℝ) ≠ 0 := by
      have hthree : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    exact (mul_eq_zero.mp hneg).resolve_left htwo
  have hfd : EqOn (fderiv ℝ c) 0 U := by
    intro x hx
    have hlin : (fderiv ℝ c x).toLinearMap = 0 := by
      apply (EuclideanSpace.basisFun (I n) ℝ).toBasis.ext
      intro i
      change fderiv ℝ c x ((EuclideanSpace.basisFun (I n) ℝ) i) = 0
      rw [EuclideanSpace.basisFun_apply]
      exact hcoord x hx i
    ext v
    exact congrArg (fun L : X n →ₗ[ℝ] ℝ => L v) hlin
  have hc₀ : c x₀ = 1 := by
    let k : I n := ⟨0, by omega⟩
    have he := congrArg (fun A : Mat n => A k k) ((hconformal hx₀).symm.trans hmatch.symm)
    exact mul_right_cancel₀ ((hg₁.2 x₀ hx₀).diag_pos (i := k)).ne'
      (by simpa only [Matrix.smul_apply, smul_eq_mul, one_mul] using he)
  intro x hx
  have hcₓ := hU.is_const_of_fderiv_eq_zero hconn hc hfd hx hx₀
  calc
    g₁ x = c x • g₁ x := by rw [hcₓ, hc₀, one_smul]
    _ = g₂ x := (hconformal hx).symm

end CalderonN
