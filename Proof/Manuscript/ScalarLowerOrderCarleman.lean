module

public import Proof.Manuscript.ScalarElliptic
public import Proof.CalderonN.EllipticCalculus

import Proof.CalderonN.CarlemanCalculus
import Proof.CalderonN.CutoffCommutator
public import Proof.CalderonN.MetricDivergence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

public section

open Set MeasureTheory CalderonN CalderonN.Carleman
open scoped ContDiff Topology

noncomputable section

namespace CalderonPaper

variable {d : ℕ}

@[expose] def lowerOrder (b : I d → X d → ℝ) (c u : X d → ℝ) (x : X d) : ℝ :=
  (∑ i, b i x * coordDeriv i u x) + c x * u x

@[expose] def weightedFunction (τ : ℝ) (φ u : X d → ℝ) (x : X d) : ℝ :=
  Real.exp (τ * φ x) * u x

theorem weightedLowerOrder_eq {φ u : X d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hu : ContDiff ℝ ∞ u) (τ : ℝ) (b : I d → X d → ℝ) (c : X d → ℝ) (x : X d) :
    weightedFunction τ φ (lowerOrder b c u) x =
      (∑ i, b i x * coordDeriv i (weightedFunction τ φ u) x) +
        (c x - τ * ∑ i, b i x * coordDeriv i φ x) * weightedFunction τ φ u x := by
  have hExp : ContDiff ℝ ∞ (fun y => Real.exp (τ * φ y)) :=
    Real.contDiff_exp.comp (contDiff_const.mul hφ)
  have hDer (i : I d) : coordDeriv i (weightedFunction τ φ u) x =
      Real.exp (τ * φ x) * (τ * coordDeriv i φ x * u x + coordDeriv i u x) := by
    change pd i (fun y => Real.exp (τ * φ y) * u y) x = _
    rw [pd_mul hExp hu, pd_exp (contDiff_const.mul hφ), pd_const_mul τ hφ]
    change _ = Real.exp (τ * φ x) * (τ * pd i φ x * u x + pd i u x)
    ring
  simp only [hDer, weightedFunction, lowerOrder]
  rw [mul_add, sub_mul]
  calc
    _ = (∑ i, Real.exp (τ * φ x) * (b i x * coordDeriv i u x)) +
        Real.exp (τ * φ x) * (c x * u x) := by rw [Finset.mul_sum]
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
      have hcancel : (∑ i, b i x * (Real.exp (τ * φ x) * (τ * coordDeriv i φ x * u x))) =
          ∑ i, τ * (b i x * coordDeriv i φ x) * (Real.exp (τ * φ x) * u x) := by
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      have hKeep : (∑ i, b i x * (Real.exp (τ * φ x) * coordDeriv i u x)) =
          ∑ i, Real.exp (τ * φ x) * (b i x * coordDeriv i u x) := by
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [hcancel, hKeep]
      ring

/-- The conjugated lower terms cost only one power of the large
Carleman parameter compared with the principal coercive expression. -/
theorem weightedLowerOrder_sq_bound {φ u : X d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hu : ContDiff ℝ ∞ u) {τ B C M : ℝ} (hτ : 1 ≤ τ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    {b : I d → X d → ℝ} {c : X d → ℝ} {x : X d}
    (hb : ∀ i, |b i x| ≤ B) (hc : |c x| ≤ C) (hphase : ∀ i, |coordDeriv i φ x| ≤ M) :
    weightedFunction τ φ (lowerOrder b c u) x ^ 2 ≤
      (2 * (d : ℝ) * B^2 + 2 * (C + (d : ℝ) * B * M)^2) *
        ((∑ i, coordDeriv i (weightedFunction τ φ u) x ^ 2) +
          τ^2 * (weightedFunction τ φ u x)^2) := by
  let v := weightedFunction τ φ u
  let a := ∑ i, coordDeriv i v x ^ 2
  let A := ∑ i, b i x * coordDeriv i v x
  let P := ∑ i, b i x * coordDeriv i φ x
  have hA₀ : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hBsq : (∑ i, b i x ^ 2) ≤ (d : ℝ) * B^2 := by
    calc
      _ ≤ ∑ _ : I d, B^2 := Finset.sum_le_sum fun i _ => by
        exact (sq_abs (b i x)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (hb i) 2)
      _ = _ := by simp
  have hA : A^2 ≤ (d : ℝ) * B^2 * a :=
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => b i x)
      (fun i => coordDeriv i v x)).trans (mul_le_mul_of_nonneg_right hBsq hA₀)
  have hP : |P| ≤ (d : ℝ) * B * M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _ : I d, B*M := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hb i) (hphase i) (abs_nonneg _) hB
      _ = _ := by simp [mul_assoc]
  have hn : 0 ≤ (d : ℝ) * B * M := by positivity
  have hτ₀ : 0 ≤ τ := zero_le_one.trans hτ
  have hlo : |c x - τ * P| ≤ τ * (C + (d : ℝ) * B * M) := by
    calc
      _ ≤ |c x| + |τ * P| := abs_sub _ _
      _ ≤ C + τ * ((d : ℝ) * B * M) := by
        rw [abs_mul,abs_of_nonneg hτ₀]
        exact add_le_add hc (mul_le_mul_of_nonneg_left hP hτ₀)
      _ ≤ _ := by rw [mul_add]; exact add_le_add (le_mul_of_one_le_left hC hτ) le_rfl
  have hLosq : (c x - τ * P)^2 ≤ (τ * (C + (d : ℝ) * B * M))^2 := by
    exact (sq_abs _).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) hlo 2)
  rw [weightedLowerOrder_eq hφ hu]
  change (A + (c x - τ * P) * v x)^2 ≤ _
  have hSplit : (A + (c x - τ * P) * v x)^2 ≤ 2 * (A^2 + ((c x - τ * P)*v x)^2) := by
    nlinarith [sq_nonneg (A - (c x - τ * P) * v x)]
  have hV : ((c x - τ * P)*v x)^2 ≤ (τ * (C + (d : ℝ) * B * M))^2 * (v x)^2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hLosq (sq_nonneg _)
  refine hSplit.trans ((mul_le_mul_of_nonneg_left (add_le_add hA hV)
    (by norm_num : 0 ≤ (2 : ℝ))).trans ?_)
  change 2 * ((d : ℝ) * B^2 * a + (τ * (C + (d : ℝ) * B * M))^2 * (v x)^2) ≤
    (2 * (d : ℝ) * B^2 + 2 * (C + (d : ℝ) * B * M)^2) * (a + τ^2 * (v x)^2)
  have haCross : 0 ≤ 2 * (C + (d : ℝ) * B * M)^2 * a := by positivity
  have hvCross : 0 ≤ 2 * (d : ℝ) * B^2 * τ^2 * (v x)^2 := by positivity
  linarith only [haCross,hvCross]

/-- Passing from the pointwise lower-order estimate to the Carleman
energy keeps the exact factor inverse in the large parameter. -/
theorem integral_weightedLowerOrder_bound {φ u : X d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hu : ContDiff ℝ ∞ u) {K : Set (X d)} (hSupp : tsupport u ⊆ K)
    {τ B C M : ℝ} (hτ : 1 ≤ τ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hM : 0 ≤ M)
    {b : I d → X d → ℝ} {c : X d → ℝ}
    (hb : ∀ x ∈ K, ∀ i, |b i x| ≤ B) (hc : ∀ x ∈ K, |c x| ≤ C)
    (hphase : ∀ x ∈ K, ∀ i, |coordDeriv i φ x| ≤ M)
    (hGrad : Integrable (fun x => ∑ i, coordDeriv i (weightedFunction τ φ u) x ^ 2))
    (hVal : Integrable (fun x => (weightedFunction τ φ u x)^2))
    (hError : Integrable (fun x => weightedFunction τ φ (lowerOrder b c u) x ^ 2)) :
    (∫ x, weightedFunction τ φ (lowerOrder b c u) x ^ 2) ≤
      ((2 * (d : ℝ) * B^2 + 2 * (C + (d : ℝ) * B * M)^2) / τ) *
        (τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ φ u) x ^ 2) +
          τ^3 * (∫ x, (weightedFunction τ φ u x)^2)) := by
  let cost := 2 * (d : ℝ) * B^2 + 2 * (C + (d : ℝ) * B * M)^2
  let G (x : X d) := ∑ i, coordDeriv i (weightedFunction τ φ u) x ^ 2
  let V (x : X d) := (weightedFunction τ φ u x)^2
  have hτ' : 0 < τ := zero_lt_one.trans_le hτ
  have hPoint (x : X d) : weightedFunction τ φ (lowerOrder b c u) x ^ 2 ≤
      cost * (G x + τ^2 * V x) := by
    by_cases hx : x ∈ K
    · exact weightedLowerOrder_sq_bound hφ hu hτ hB hC hM (hb x hx) (hc x hx) (hphase x hx)
    · have hz : u =ᶠ[𝓝 x] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hSupp h))
      have hd (i : I d) : coordDeriv i u x = 0 := by
        rw [coordDeriv,hz.fderiv_eq]
        simp
      simp only [weightedFunction, lowerOrder, hd, mul_zero, Finset.sum_const_zero,
        hz.eq_of_nhds, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (by positivity)
        (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have h := integral_mono hError ((hGrad.add (hVal.const_mul (τ^2))).const_mul cost) hPoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hGrad (hVal.const_mul (τ^2)), integral_const_mul] at h
  refine h.trans_eq ?_
  change cost * ((∫ x, G x) + τ^2 * ∫ x, V x) =
    cost / τ * (τ * (∫ x, G x) + τ^3 * ∫ x, V x)
  field_simp

/-- Absorb the lower-order remainder once the parameter is large compared
with its uniform numeric bound. The weight and coercive left side stay
the ones of the principal estimate. -/
theorem absorb_weightedError {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P R E : α → ℝ} {energy C cost τ : ℝ} (hC : 0 ≤ C)
    (hτ : 1 ≤ τ) (hLarge : 4 * C * cost ≤ τ)
    (hR : Integrable (fun x => (R x)^2) μ) (hE : Integrable (fun x => (E x)^2) μ)
    (hP : Integrable (fun x => (P x)^2) μ)
    (hResidual : ∀ x, P x = R x - E x) (hEnergy : 0 ≤ energy)
    (hPrincipal : energy ≤ C * (∫ x, (P x)^2 ∂μ))
    (hError : (∫ x, (E x)^2 ∂μ) ≤ cost / τ * energy) :
    energy ≤ 4 * C * (∫ x, (R x)^2 ∂μ) := by
  have hSplit := integral_mono hP ((hR.add hE).const_mul 2)
    (fun x => show (P x)^2 ≤ 2*((R x)^2+(E x)^2) by
      rw [hResidual x]; nlinarith [sq_nonneg (R x + E x)])
  simp only [Pi.add_apply] at hSplit
  rw [integral_const_mul, integral_add hR hE] at hSplit
  have hMain := hPrincipal.trans (mul_le_mul_of_nonneg_left hSplit hC)
  have hAbsorb : 2 * C * (cost / τ) ≤ 1/2 := by
    have hτ' : 0 < τ := zero_lt_one.trans_le hτ
    have hSmall : (2*C*cost)/τ ≤ 1/2 := (div_le_iff₀ hτ').mpr (by linarith)
    rwa [mul_div_assoc] at hSmall
  have hIneq : energy ≤ 2 * C * (∫ x, (R x)^2 ∂μ) + energy / 2 := by
    calc
      energy ≤ 2 * C * (∫ x, (R x)^2 ∂μ) + (2 * C * (cost / τ)) * energy := by
        have he := mul_le_mul_of_nonneg_left hError (by positivity : 0 ≤ 2*C)
        linarith only [hMain,he]
      _ ≤ 2 * C * (∫ x, (R x)^2 ∂μ) + energy / 2 := by
        have he := mul_le_mul_of_nonneg_right hAbsorb hEnergy
        linarith
  linarith only [hIneq]

namespace ScalarElliptic

/-- The discrepancy between a scalar operator and its principal metric
Laplacian, multiplied by the chart volume density. -/
@[expose] def weightedDrift (L : ScalarElliptic d) (k : I d) (x : X d) : ℝ :=
  chartVolume L.metric x * (L.first x k +
    ∑ i, ∑ j, L.principalMatrix x i j * christoffel L.metric x k i j)

@[expose] def weightedPotential (L : ScalarElliptic d) (x : X d) : ℝ :=
  chartVolume L.metric x * L.zeroth x

theorem volume_mul_apply_eq {L : ScalarElliptic d} {D : Set (X d)}
    (hD : IsOpen D) (hL : L.SmoothOn D) {u : X d → ℝ} (hu : ContDiffOn ℝ ∞ u D)
    {x : X d} (hx : x ∈ D) :
    chartVolume L.metric x * L.apply u x =
      Elliptic.Lop (fun i j y => divergenceCoeff L.metric y i j) u x +
        lowerOrder L.weightedDrift L.weightedPotential u x := by
  have hdiv : Elliptic.Lop (fun i j y => divergenceCoeff L.metric y i j) u x =
      chartVolume L.metric x * laplace L.metric u x :=
    (chartVolume_mul_laplace_eq_divergence hD hL.1 hu hx).symm
  rw [hdiv]
  let A := L.principalMatrix x
  let conn (i j k : I d) := christoffel L.metric x k i j
  let der (i : I d) := coordDeriv i u x
  let Q := ∑ i, ∑ j, A i j * coordDeriv i (coordDeriv j u) x
  let V := chartVolume L.metric x
  have hLap : laplace L.metric u x =
      Q - ∑ k, (∑ i, ∑ j, A i j * conn i j k) * der k := by
    change (∑ i, ∑ j, A i j * (coordDeriv i (coordDeriv j u) x - ∑ k, conn i j k * der k)) = _
    simp only [mul_sub, Finset.sum_sub_distrib, Q]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    let t (i j k : I d) := A i j * (conn i j k * der k)
    change (∑ i, ∑ j, ∑ k, t i j k) = ∑ k, ∑ i, ∑ j, t i j k
    calc
      _ = ∑ i, ∑ k, ∑ j, t i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hLap]
  change V * (Q + (∑ i, L.first x i * der i) + L.zeroth x * u x) = _
  have hLow : lowerOrder L.weightedDrift L.weightedPotential u x =
      V * ((∑ i, L.first x i * der i) +
        (∑ k, (∑ i, ∑ j, A i j * conn i j k) * der k) + L.zeroth x * u x) := by
    change (∑ k, (V * (L.first x k + ∑ i, ∑ j, A i j * conn i j k)) * der k) +
      (V * L.zeroth x) * u x = _
    simp only [mul_assoc, mul_add, Finset.sum_add_distrib, Finset.mul_sum, add_mul]
    simp only [← Finset.mul_sum, mul_assoc]
  rw [hLow]
  ring

end ScalarElliptic

private theorem integrable_sq_with_support {f u : X d → ℝ} (hf : Continuous f)
    (hu : HasCompactSupport u) (hzero : ∀ x ∉ tsupport u, f x = 0) :
    Integrable (fun x => f x ^ 2) :=
  (hf.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.intro hu (fun x hx => by change f x ^ 2 = 0; rw [hzero x hx]; simp))

open Elliptic.CutoffCommutator in
/-- A principal divergence-form Carleman estimate with the same weight and
left side for the operator plus bounded lower-order coefficients. -/
theorem carleman_with_lowerOrder
    {a : I d → I d → X d → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    {φ u : X d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hu : ContDiff ℝ ∞ u) (huC : HasCompactSupport u)
    {K : Set (X d)} (hSupp : tsupport u ⊆ K)
    {τ B C M C₀ : ℝ} (hτ : 1 ≤ τ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    {b : I d → X d → ℝ} {c : X d → ℝ} (hbs : ∀ i, Continuous (b i)) (hcs : Continuous c)
    (hb : ∀ x ∈ K, ∀ i, |b i x| ≤ B) (hc : ∀ x ∈ K, |c x| ≤ C)
    (hphase : ∀ x ∈ K, ∀ i, |coordDeriv i φ x| ≤ M)
    (hLarge : 4 * C₀ * (2 * (d : ℝ) * B^2 + 2 * (C + (d : ℝ) * B * M)^2) ≤ τ)
    (hPrincipal :
      τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ φ u) x ^ 2) +
        τ^3 * (∫ x, (weightedFunction τ φ u x)^2) ≤
          C₀ * (∫ x, (weightedFunction τ φ (Elliptic.Lop a u) x)^2)) :
    τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ φ u) x ^ 2) +
        τ^3 * (∫ x, (weightedFunction τ φ u x)^2) ≤
      4*C₀ * (∫ x, (weightedFunction τ φ (fun y => Elliptic.Lop a u y + lowerOrder b c u y) x)^2) := by
  let v := weightedFunction τ φ u
  let E := weightedFunction τ φ (lowerOrder b c u)
  let P := weightedFunction τ φ (Elliptic.Lop a u)
  let R := weightedFunction τ φ (fun x => Elliptic.Lop a u x + lowerOrder b c u x)
  have hForm (x : X d) : P x = R x - E x := by dsimp [P,R,E,weightedFunction]; ring
  have hExp : ContDiff ℝ ∞ (fun x => Real.exp (τ * φ x)) :=
    Real.contDiff_exp.comp (contDiff_const.mul hφ)
  have hv := hExp.mul hu
  have hvD (i : I d) : Continuous (coordDeriv i v) :=
    (contDiff_pd (i := i) hv).continuous
  have hLop : Continuous (Elliptic.Lop a u) := by
    unfold Elliptic.Lop
    exact continuous_finsetSum _ fun i _ => (contDiff_pd (i := i)
      (ContDiff.sum fun j _ => (ha i j).mul (contDiff_pd (i := j) hu))).continuous
  have hLow : Continuous (lowerOrder b c u) :=
    (continuous_finsetSum _ fun i _ => (hbs i).mul (contDiff_pd (i := i) hu).continuous).add
      (hcs.mul hu.continuous)
  have hOff (x : X d) (hx : x ∉ tsupport u) :
      u x = 0 ∧ (∀ i, coordDeriv i u x = 0) ∧ Elliptic.Lop a u x = 0 := by
    have heq := notMem_tsupport_iff_eventuallyEq.mp hx
    refine ⟨heq.eq_of_nhds, fun i => ?_, ?_⟩
    · rw [coordDeriv,heq.fderiv_eq]
      simp
    · exact Lop_eq_zero_of_not_mem_tsupport a hx
  have hV0 : ∀ x ∉ tsupport u, v x = 0 := fun x hx => by
    rw [show v x = Real.exp (τ * φ x) * u x from rfl, (hOff x hx).1, mul_zero]
  have hDv0 : ∀ x ∉ tsupport u, ∀ i, coordDeriv i v x = 0 := by
    intro x hx i
    have heq : v =ᶠ[𝓝 x] fun _ => (0 : ℝ) := (notMem_tsupport_iff_eventuallyEq.mp hx).mono
      (fun y hy => by simp [v, weightedFunction, hy])
    rw [coordDeriv,heq.fderiv_eq]
    simp
  have hE0 : ∀ x ∉ tsupport u, E x = 0 := by
    intro x hx
    simp only [E, weightedFunction, lowerOrder, (hOff x hx).1, (hOff x hx).2.1,
      mul_zero, Finset.sum_const_zero, add_zero]
  have hP0 : ∀ x ∉ tsupport u, P x = 0 := by
    intro x hx
    simp only [P,weightedFunction,(hOff x hx).2.2,mul_zero]
  have hIntP := integrable_sq_with_support (hExp.continuous.mul hLop) huC hP0
  have hIntE := integrable_sq_with_support (hExp.continuous.mul hLow) huC hE0
  have hIntR := integrable_sq_with_support (hExp.continuous.mul (hLop.add hLow)) huC
    (show ∀ x ∉ tsupport u, R x = 0 from fun x hx => by linarith only [hForm x,hP0 x hx,hE0 x hx])
  have hIntV := integrable_sq_with_support hv.continuous huC hV0
  have hIntG : Integrable (fun x => ∑ i, coordDeriv i v x ^ 2) :=
    integrable_finsetSum _ fun i _ => integrable_sq_with_support (hvD i) huC (fun x hx => hDv0 x hx i)
  have hError := integral_weightedLowerOrder_bound hφ hu hSupp hτ hB hC hM hb hc hphase
    hIntG hIntV hIntE
  exact absorb_weightedError hC₀ hτ hLarge hIntR hIntE hIntP hForm (by
    have hτ₀ := zero_le_one.trans hτ
    exact add_nonneg (mul_nonneg hτ₀ (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg (pow_nonneg hτ₀ _) (integral_nonneg fun _ => sq_nonneg _))) hPrincipal hError

end CalderonPaper
