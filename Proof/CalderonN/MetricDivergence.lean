module

public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Ring

/-! Adapted from `Calderon/MetricDensityConnection.lean` and
`Calderon/MetricHessianDivergence.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

public section

noncomputable section
open Set
open scoped BigOperators Matrix.Norms.Operator ContDiff
namespace CalderonN

variable {n : ℕ}

private theorem symmetric_koszul_contraction
    (Q : I n → I n → ℝ) (D : I n → I n → I n → ℝ) (ρ : ℝ)
    (hQ : ∀ i j, Q i j = Q j i) (hD : ∀ i a b, D i a b = D i b a) (j : I n) :
    (∑ i : I n, ((ρ / 2) * (∑ a, ∑ b, Q b a * D i a b) * Q i j -
      ρ * (∑ a, ∑ b, Q i a * D i a b * Q b j))) =
    -ρ * ∑ a : I n, ∑ b : I n, Q a b * ((1 / 2 : ℝ) *
      ∑ c : I n, Q j c * (D a c b + D b c a - D c b a)) := by
  let T := ∑ a, ∑ b, ∑ c, Q a b * (Q j c * D a c b)
  let S := ∑ a, ∑ b, ∑ c, Q a b * (Q j c * D c b a)
  have hswap : (∑ a, ∑ b, ∑ c, Q a b * (Q j c * D b c a)) = T := by
    unfold T
    rw [Finset.sum_comm (f := fun a b => ∑ c, Q a b * (Q j c * D b c a))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hQ b a]
  have hdiv : (∑ i, ∑ a, ∑ b, Q i a * D i a b * Q b j) = T := by
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by rw [hD i a b, hQ b j, mul_right_comm, mul_assoc]
  have hdensity : (∑ i, (∑ a, ∑ b, Q b a * D i a b) * Q i j) = S := by
    calc
      _ = ∑ i, ∑ a, ∑ b, Q a b * (Q j i * D i b a) := by
        simp only [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by rw [hQ b a, hD i a b, hQ i j, mul_right_comm, mul_assoc]
      _ = S := by
        unfold S
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hconnection : (∑ a, ∑ b, Q a b * ((1 / 2 : ℝ) *
      ∑ c, Q j c * (D a c b + D b c a - D c b a))) = (1 / 2 : ℝ) * (T + T - S) := by
    calc
      _ = (1 / 2 : ℝ) * ∑ a, ∑ b, ∑ c, Q a b * (Q j c * (D a c b + D b c a - D c b a)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hswap]
  calc
    _ = (ρ / 2) * S - ρ * T := by
      rw [← hdensity, ← hdiv]
      simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by rw [hconnection]; ring

lemma fderiv_densityInverse_entry (g : (MetricField n)) (x V : (X n))
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hp : (g x).PosDef) (i j : (I n)) :
    fderiv ℝ (fun y => chartVolume g y * (g y)⁻¹ i j) x V =
      ((chartVolume g x / 2) * ∑ a : (I n), ∑ b : (I n),
        (g x)⁻¹ b a * fderiv ℝ (fun y => g y a b) x V) * (g x)⁻¹ i j -
      chartVolume g x * ∑ a : (I n), ∑ b : (I n),
        (g x)⁻¹ i a * fderiv ℝ (fun y => g y a b) x V * (g x)⁻¹ b j := by
  have hv : DifferentiableAt ℝ (chartVolume g) x :=
    ((hasFDerivAt_metric_determinant g x hg hp).sqrt hp.det_pos.ne').differentiableAt
  let E : (Mat n) →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have hi : DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x :=
    (E.hasFDerivAt.comp x (hasFDerivAt_inverseMetric_matrix g x hg hp)).differentiableAt
  rw [fderiv_fun_mul hv hi]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [fderiv_vol_apply_entries g x V hg hp, fderiv_inverseMetric_entry_apply g x V hg hp]
  ring

@[expose] def divergenceCoeff (g : (MetricField n)) (y : (X n)) (i j : (I n)) : ℝ :=
  chartVolume g y * (g y)⁻¹ i j

theorem divergenceMatrix_posDef (g : MetricField n) (x : X n) (h : (g x).PosDef) :
    Matrix.PosDef (show Mat n from fun i j => divergenceCoeff g x i j) := by
  change (chartVolume g x • (g x)⁻¹).PosDef
  exact h.inv.smul (Real.sqrt_pos.mpr h.det_pos)

@[expose] def divergenceFlux (g : (MetricField n)) (f : (X n) → ℝ) (y : (X n)) (i : (I n)) : ℝ :=
  ∑ j, divergenceCoeff g y i j * coordDeriv j f y

theorem contDiffOn_divergenceCoeff {U : Set (X n)} {g : (MetricField n)}
    (hg : SmoothMetric U g) (i j : (I n)) :
    ContDiffOn ℝ ∞ (fun y => divergenceCoeff g y i j) U :=
  (contDiffOn_metric_volume hg).mul (contDiffOn_metric_inv_entry hg i j)

theorem contDiffOn_divergenceFlux {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)}
    (hg : SmoothMetric U g) {f : (X n) → ℝ} (hf : ContDiffOn ℝ ∞ f U) (i : (I n)) :
    ContDiffOn ℝ ∞ (fun y => divergenceFlux g f y i) U :=
  ContDiffOn.sum fun j _ => (contDiffOn_divergenceCoeff hg i j).mul (contDiffOn_coordDeriv hf hU j)

theorem divergenceCoeff_symm {U : Set (X n)} {g : (MetricField n)} (hg : SmoothMetric U g)
    {y : (X n)} (hy : y ∈ U) (i j : (I n)) :
    divergenceCoeff g y i j = divergenceCoeff g y j i := by
  unfold divergenceCoeff
  rw [show (g y)⁻¹ i j = (g y)⁻¹ j i from
    congrFun (congrFun (hg.2 y hy).inv.isHermitian.isSymm.eq j) i]

/-- The derivative of the inverse metric times volume is the negative
metric-weighted contraction of the connection. -/
theorem divergenceCoeff_connection {U : Set (X n)} (hU : IsOpen U) {g : (MetricField n)}
    (hg : SmoothMetric U g) {y : (X n)} (hy : y ∈ U) (j : (I n)) :
    ∑ i, coordDeriv i (fun z => divergenceCoeff g z i j) y =
      -chartVolume g y * ∑ a, ∑ b, (g y)⁻¹ a b * christoffel g y j a b := by
  let Q : (Mat n) := (g y)⁻¹
  let D (i a b : (I n)) := coordDeriv i (fun z => g z a b) y
  let ρ := chartVolume g y
  have hd (a b : (I n)) : DifferentiableAt ℝ (fun z => g z a b) y :=
    ((hg.1 a b).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have hQ (a b : (I n)) : Q a b = Q b a :=
    congrFun (congrFun (hg.2 y hy).inv.isHermitian.isSymm.eq b) a
  have hD (i a b : (I n)) : D i a b = D i b a :=
    eqOn_coordDeriv hU (fun z hz =>
      congrFun (congrFun (hg.2 z hz).isHermitian.isSymm.eq b) a) i hy
  have hdiff (i : (I n)) : coordDeriv i (fun z => divergenceCoeff g z i j) y =
      ((ρ / 2) * (∑ a, ∑ b, Q b a * D i a b)) * Q i j -
        ρ * (∑ a, ∑ b, Q i a * D i a b * Q b j) :=
    fderiv_densityInverse_entry g y (axis i) hd (hg.2 y hy) i j
  have hΓ (a b : (I n)) : christoffel g y j a b =
      (1 / 2 : ℝ) * ∑ l, Q j l * (D a l b + D b l a - D l b a) := by
    simp only [christoffel, Q, D, fun l => hD b a l, fun l => hD l a b]
    ring
  simp_rw [hdiff, hΓ]
  exact symmetric_koszul_contraction Q D ρ hQ hD j

theorem chartVolume_mul_laplace_eq_divergence {U : Set (X n)} (hU : IsOpen U)
    {g : (MetricField n)} (hg : SmoothMetric U g) {f : (X n) → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {y : (X n)} (hy : y ∈ U) :
    chartVolume g y * laplace g f y =
      ∑ i, coordDeriv i (fun z => divergenceFlux g f z i) y := by
  let A (i j : (I n)) := coordDeriv i (fun z => divergenceCoeff g z i j) y
  let h (j : (I n)) := coordDeriv j f y
  have ha (i j : (I n)) := ((contDiffOn_divergenceCoeff hg i j).differentiableOn (by simp)).differentiableAt
    (hU.mem_nhds hy)
  have hb (j : (I n)) := ((contDiffOn_coordDeriv hf hU j).differentiableOn (by simp)).differentiableAt
    (hU.mem_nhds hy)
  have hder (i : (I n)) : coordDeriv i (fun z => divergenceFlux g f z i) y =
      ∑ j, (A i j * h j + divergenceCoeff g y i j * coordDeriv i (coordDeriv j f) y) := by
    change fderiv ℝ (fun z => ∑ j, divergenceCoeff g z i j * coordDeriv j f z) y (axis i) = _
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun j z => divergenceCoeff g z i j * coordDeriv j f z)
      (fun j _ => (ha i j).mul (hb j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (ha i j) (hb j)]
    change divergenceCoeff g y i j * coordDeriv i (coordDeriv j f) y + h j * A i j = _
    ring
  have hdrift (j : (I n)) : ∑ i, A i j =
      -chartVolume g y * ∑ a, ∑ b, (g y)⁻¹ a b * christoffel g y j a b :=
    divergenceCoeff_connection hU hg hy j
  simp only [hder, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => A i j * h j)]
  simp_rw [← Finset.sum_mul, hdrift]
  have hContract :
      (∑ i, ∑ j, (g y)⁻¹ i j * ∑ k, christoffel g y k i j * h k) =
        ∑ k, (∑ i, ∑ j, (g y)⁻¹ i j * christoffel g y k i j) * h k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    calc
      _ = ∑ i, ∑ k, ∑ j, (g y)⁻¹ i j * (christoffel g y k i j * h k) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [laplace, mul_sub, Finset.sum_sub_distrib]
  rw [hContract]
  simp only [Finset.mul_sum, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib,
    divergenceCoeff, h, mul_assoc]
  ring

theorem divergenceCoeff_div_free_of_harmonicCoordinates {U : Set (X n)} (hU : IsOpen U)
    {g : (MetricField n)} (hg : SmoothMetric U g) (hchart : HarmonicCoordinates U g)
    {y : (X n)} (hy : y ∈ U) (j : (I n)) :
    ∑ i, coordDeriv i (fun z => divergenceCoeff g z i j) y = 0 := by
  rw [divergenceCoeff_connection hU hg hy, contracted_christoffel_eq_zero hchart hy, mul_zero]

end CalderonN
