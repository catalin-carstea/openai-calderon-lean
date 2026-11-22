module

public import Proof.CalderonN.StrictCarlemanIdentity
public import Proof.CalderonN.CarlemanWeight
import Mathlib.Tactic

/-! Adapted from `Calderon/MixedKernelConstruction/MixedKernelConstructionC3SupportV015.lean`
at d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.Carleman.Strict

variable {d : ℕ}

section SignedShift
variable {a : Fin d → Fin d → (CalderonN.X d) → ℝ}

theorem divV_const_mul (τ : ℝ) {W : Fin d → (CalderonN.X d) → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j)) (x : (CalderonN.X d)) :
    divV (fun j y => τ * W j y) x = τ * divV W x := by
  unfold divV
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => pd_const_mul τ (hW j) x

theorem Lop_const_mul (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (τ : ℝ) {f : (CalderonN.X d) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : (CalderonN.X d)) :
    Lop a (fun y => τ * f y) x = τ * Lop a f x := by
  have h1 : ∀ i, (fun z => ∑ k, a i k z * pd k (fun y => τ * f y) z) =
      fun z => τ * ∑ k, a i k z * pd k f z := by
    intro i; funext z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_const_mul τ hf]; ring
  have h2 : ∀ i, ContDiff ℝ ∞ (fun z => ∑ k, a i k z * pd k f z) := by
    intro i
    have : ∀ k, ContDiff ℝ ∞ (fun y => a i k y) := fun k => ha i k
    fun_prop
  unfold Lop
  simp only [h1]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => pd_const_mul τ (h2 i) x

theorem Lop_const (c : ℝ) (x : (CalderonN.X d)) : Lop a (fun _ => c) x = 0 := by
  simp [Lop, pd_const]

theorem Mgrad_const_mul (τ : ℝ) {W : Fin d → (CalderonN.X d) → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j)) (x : (CalderonN.X d))
    (ξ : Fin d → ℝ) :
    Mgrad a (fun j y => τ * W j y) x ξ = τ * Mgrad a W x ξ := by
  have h : ∀ i j, pd i (fun y => τ * W j y) x = τ * pd i (W j) x :=
    fun i j => pd_const_mul τ (hW j) x
  have h₁ : (∑ i, ∑ j, ∑ k, a i k x * ξ k * (τ * pd i (W j) x) * ξ j) =
      τ * ∑ i, ∑ j, ∑ k, a i k x * ξ k * pd i (W j) x * ξ j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have h₂ : (∑ j, (τ * W j x) * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k) =
      τ * ∑ j, W j x * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [Mgrad, h, h₁, h₂]
  ring

theorem mzero_const_mul (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (τ : ℝ) {W : Fin d → (CalderonN.X d) → ℝ}
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) {N : (CalderonN.X d) → ℝ} (hN : ContDiff ℝ ∞ N) (x : (CalderonN.X d)) :
    mzero a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) x =
      τ ^ 3 * (2 * ∑ j, W j x * pd j N x) - τ * Lop a (divV W) x := by
  have hd : divV (fun j y => τ * W j y) = fun y => τ * divV W y :=
    funext (divV_const_mul τ hW)
  have hpN : ∀ j, pd j (fun y => τ ^ 2 * N y) x = τ ^ 2 * pd j N x :=
    fun j => pd_const_mul _ hN x
  unfold mzero
  rw [hd, Lop_const_mul ha τ (contDiff_divV hW)]
  have he : (∑ j, (τ * W j x) * (τ ^ 2 * pd j N x)) =
      τ ^ 3 * ∑ j, W j x * pd j N x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [show (∑ j, (τ * W j x) * pd j (fun y => τ ^ 2 * N y) x) =
        (∑ j, (τ * W j x) * (τ ^ 2 * pd j N x)) from Finset.sum_congr rfl fun j _ => by rw [hpN j], he]
  ring

/-- T2: the skew part for the unchanged phase, `Bτ v = -τ(2 W·∇v + (div W) v)`. -/
theorem Bop_const_mul (τ : ℝ) {W : Fin d → (CalderonN.X d) → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (v : (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) :
    Bop (fun j y => τ * W j y) v x = -τ * (2 * ∑ j, W j x * pd j v x + divV W x * v x) := by
  unfold Bop
  rw [divV_const_mul τ hW x]
  have he : (∑ j, (τ * W j x) * pd j v x) =
      τ * ∑ j, W j x * pd j v x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [he]
  ring

/-- T2: the exact signed-shift integrand: `X = τW`, `q = τ²N`, auxiliary `θ ≡ 4mτ`
(`m` any REAL), `κ = 1/2`. The `-8m²τ²` is the completion cost. -/
theorem Qfun_signed_shift (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (τ m : ℝ) {W : Fin d → (CalderonN.X d) → ℝ}
    (hW : ∀ j, ContDiff ℝ ∞ (W j)) {N : (CalderonN.X d) → ℝ} (hN : ContDiff ℝ ∞ N) (v : (CalderonN.X d) → ℝ) (x : (CalderonN.X d)) :
    Qfun a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) (fun _ => 4 * m * τ) (1 / 2) v x =
      τ * (Mgrad a W x (grad v x) + 4 * m * quad a x (grad v x)) +
      (τ ^ 3 * (2 * ∑ j, W j x * pd j N x - 4 * m * N x) - 8 * m ^ 2 * τ ^ 2 -
        τ * Lop a (divV W) x) * (v x * v x) := by
  unfold Qfun
  rw [Mgrad_const_mul τ hW, mzero_const_mul ha τ hW hN, Lop_const]
  ring

/-- The unchanged-phase gradient field `W = a ∇ϑ`. -/
def phaseField (a : Fin d → Fin d → (CalderonN.X d) → ℝ) (ϑ : (CalderonN.X d) → ℝ) (j : Fin d) (y : (CalderonN.X d)) : ℝ :=
  ∑ k, a j k y * pd k ϑ y

/-- The unchanged-phase squared gradient `N = a(∇ϑ,∇ϑ)`. -/
def phaseNorm (a : Fin d → Fin d → (CalderonN.X d) → ℝ) (ϑ : (CalderonN.X d) → ℝ) (y : (CalderonN.X d)) : ℝ :=
  ∑ i, ∑ k, a i k y * pd i ϑ y * pd k ϑ y

theorem contDiff_phaseField (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {ϑ : (CalderonN.X d) → ℝ}
    (hϑ : ContDiff ℝ ∞ ϑ) (j : Fin d) : ContDiff ℝ ∞ (phaseField a ϑ j) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold phaseField; fun_prop

theorem contDiff_phaseNorm (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {ϑ : (CalderonN.X d) → ℝ}
    (hϑ : ContDiff ℝ ∞ ϑ) : ContDiff ℝ ∞ (phaseNorm a ϑ) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold phaseNorm; fun_prop

/-- T3: conjugation by the UNCHANGED phase `τϑ` (existing `conj_identity`, `Φ = τϑ`). -/
theorem conj_unchanged_phase (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (hsymm : ∀ i k, a i k = a k i)
    {ϑ v : (CalderonN.X d) → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (hv : ContDiff ℝ ∞ v) (τ : ℝ) (x : (CalderonN.X d)) :
    Lop a (fun y => Real.exp (-(τ * ϑ y)) * v y) x =
      Real.exp (-(τ * ϑ x)) * (Sop a (fun y => τ ^ 2 * phaseNorm a ϑ y) v x +
        Bop (fun j y => τ * phaseField a ϑ j y) v x) := by
  have hΦ : ContDiff ℝ ∞ (fun y => τ * ϑ y) := contDiff_const.mul hϑ
  have hp : ∀ k y, pd k (fun y => τ * ϑ y) y = τ * pd k ϑ y := fun k y => pd_const_mul τ hϑ y
  have e1 : (fun y => ∑ i, ∑ k, a i k y * pd i (fun y => τ * ϑ y) y *
      pd k (fun y => τ * ϑ y) y) = fun y => τ ^ 2 * phaseNorm a ϑ y := by
    funext y
    unfold phaseNorm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hp, hp]; ring
  have e2 : (fun j y => ∑ k, a j k y * pd k (fun y => τ * ϑ y) y) =
      fun j y => τ * phaseField a ϑ j y := by
    funext j y
    unfold phaseField
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hp]; ring
  have h := conj_identity ha hsymm hΦ hv x
  rw [e1, e2] at h
  exact h

/-- T4: pointwise signed-shift absorption of the rank-one normal loss through the RETAINED
`B²` (pure real algebra; `m` of either sign). -/
theorem signed_shift_pointwise {α β D R0 d0 m τ Mq Gr w d R Z B v : ℝ}
    (hβ : 0 < β) (hD : 0 ≤ D)
    (hcoef : α * Gr ≤ Mq + D * w ^ 2) (hZ : β ≤ Z) (hR : |R| ≤ R0) (hd : |d| ≤ d0)
    (hB : B = -τ * (2 * w + d * v))
    (hτ1 : 1 ≤ τ) (hτD : D ≤ τ) (hτm : 32 * m ^ 2 ≤ β * τ)
    (hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ) :
    α * τ * Gr + β / 2 * τ ^ 3 * (v * v) ≤
      τ * Mq + (τ ^ 3 * Z - 8 * m ^ 2 * τ ^ 2 - τ * R) * (v * v) + B ^ 2 := by
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ1
  have hV : 0 ≤ v * v := mul_self_nonneg v
  have h1 : τ * (α * Gr) ≤ τ * (Mq + D * w ^ 2) := mul_le_mul_of_nonneg_left hcoef hτ0.le
  -- normal square from the skew part
  have h2w : 2 * τ * w = -B - τ * d * v := by rw [hB]; ring
  have hd2 : d ^ 2 ≤ d0 ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le hd) (le_of_abs_le hd)
    exact this
  have hw4 : 4 * τ ^ 2 * w ^ 2 ≤ 2 * B ^ 2 + 2 * τ ^ 2 * d0 ^ 2 * (v * v) := by
    have e : 4 * τ ^ 2 * w ^ 2 = (B + τ * d * v) ^ 2 := by
      have : (2 * τ * w) ^ 2 = (-B - τ * d * v) ^ 2 := by rw [h2w]
      nlinarith [this]
    have hdd : τ ^ 2 * d ^ 2 * (v * v) ≤ τ ^ 2 * d0 ^ 2 * (v * v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 (sq_nonneg τ)) hV
    nlinarith [sq_nonneg (B - τ * d * v)]
  have h2 : τ * D * w ^ 2 ≤ B ^ 2 / 2 + D * τ * d0 ^ 2 * (v * v) / 2 := by
    have hmul : D * (4 * τ ^ 2 * w ^ 2) ≤ D * (2 * B ^ 2 + 2 * τ ^ 2 * d0 ^ 2 * (v * v)) :=
      mul_le_mul_of_nonneg_left hw4 hD
    have hDB : D * B ^ 2 ≤ τ * B ^ 2 := mul_le_mul_of_nonneg_right hτD (sq_nonneg B)
    have key : τ * (τ * D * w ^ 2) ≤ τ * (B ^ 2 / 2 + D * τ * d0 ^ 2 * (v * v) / 2) := by
      nlinarith
    exact le_of_mul_le_mul_left key hτ0
  -- mass coefficient
  have hZ3 : τ ^ 3 * β ≤ τ ^ 3 * Z := mul_le_mul_of_nonneg_left hZ (by positivity)
  have hRR : τ * R ≤ τ * R0 := mul_le_mul_of_nonneg_left (le_of_abs_le hR) hτ0.le
  have hm2 : 32 * m ^ 2 * τ ^ 2 ≤ β * τ * τ ^ 2 :=
    mul_le_mul_of_nonneg_right hτm (sq_nonneg τ)
  have hβτ : β * τ ≤ β * τ * τ := by
    have : 0 ≤ β * τ := by positivity
    nlinarith
  have hR2 : 4 * (R0 + D * d0 ^ 2 / 2) * τ ≤ β * τ * τ * τ :=
    mul_le_mul_of_nonneg_right (hτR.trans hβτ) hτ0.le
  have hc : β / 2 * τ ^ 3 ≤
      τ ^ 3 * Z - 8 * m ^ 2 * τ ^ 2 - τ * R - D * τ * d0 ^ 2 / 2 := by
    nlinarith
  have h3V : β / 2 * τ ^ 3 * (v * v) ≤
      (τ ^ 3 * Z - 8 * m ^ 2 * τ ^ 2 - τ * R - D * τ * d0 ^ 2 / 2) * (v * v) :=
    mul_le_mul_of_nonneg_right hc hV
  nlinarith [sq_nonneg B]

/-- T5 (v-form): integrated signed-shift estimate with the retained `B²`, for compactly
supported smooth `v`, from POINTWISE coefficient bounds on a set `K ⊇ tsupport v`.
The coefficient bounds are intermediate targets (T6 derives them from strictness);
they are not endpoint premises. -/
theorem principal_estimate_of_coefficient_bounds (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {W : Fin d → (CalderonN.X d) → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j))
    {N : (CalderonN.X d) → ℝ} (hN : ContDiff ℝ ∞ N) {v : (CalderonN.X d) → ℝ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (K : Set (CalderonN.X d)) (hsupp : tsupport v ⊆ K)
    (m α β D R0 d0 : ℝ) (hβ : 0 < β) (hD : 0 ≤ D)
    (hcoef : ∀ x ∈ K, ∀ ξ : Fin d → ℝ, α * ∑ i, ξ i ^ 2 ≤
      Mgrad a W x ξ + 4 * m * quad a x ξ + D * (∑ j, W j x * ξ j) ^ 2)
    (hZ : ∀ x ∈ K, β ≤ 2 * ∑ j, W j x * pd j N x - 4 * m * N x)
    (hR : ∀ x ∈ K, |Lop a (divV W) x| ≤ R0)
    (hd : ∀ x ∈ K, |divV W x| ≤ d0)
    (τ : ℝ) (hτ1 : 1 ≤ τ) (hτD : D ≤ τ) (hτm : 32 * m ^ 2 ≤ β * τ)
    (hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ) :
    α * τ * (∫ x, ∑ i, pd i v x ^ 2) + β / 2 * τ ^ 3 * (∫ x, v x ^ 2) ≤
      ∫ x, (Sop a (fun y => τ ^ 2 * N y) v x + Bop (fun j y => τ * W j y) v x) ^ 2 := by
  have hX : ∀ j, ContDiff ℝ ∞ (fun y => τ * W j y) := fun j => contDiff_const.mul (hW j)
  have hq : ContDiff ℝ ∞ (fun y => τ ^ 2 * N y) := contDiff_const.mul hN
  have hθc : ContDiff ℝ ∞ (fun _ : (CalderonN.X d) => 4 * m * τ) := contDiff_const
  obtain ⟨hI, hle⟩ := integral_Qfun_add_Bop_sq_le (X := fun j y => τ * W j y)
    (θ := fun _ => 4 * m * τ) ha hX hq hθc hv hsymm hvc (κ := 1 / 2) (by norm_num) (by norm_num)
  have hG : Integrable (fun x => ∑ i, pd i v x ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [(vanish_outside hx).2.1]
    · fun_prop
  have hV : Integrable (fun x => v x ^ 2) := by
    apply integrable_of_vanish _ hvc
    · intro x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    · fun_prop
  have hpt : ∀ x, α * τ * ∑ i, pd i v x ^ 2 + β / 2 * τ ^ 3 * v x ^ 2 ≤
      Qfun a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) (fun _ => 4 * m * τ) (1 / 2) v x +
        Bop (fun j y => τ * W j y) v x ^ 2 := by
    intro x
    by_cases hx : x ∈ tsupport v
    · have hxK := hsupp hx
      rw [Qfun_signed_shift ha τ m hW hN v x]
      have hc := hcoef x hxK (grad v x)
      have key := signed_shift_pointwise (Gr := ∑ i, pd i v x ^ 2)
        (w := ∑ j, W j x * pd j v x) (d := divV W x) (v := v x) (R := Lop a (divV W) x)
        (Z := 2 * ∑ j, W j x * pd j N x - 4 * m * N x)
        (Mq := Mgrad a W x (grad v x) + 4 * m * quad a x (grad v x))
        (B := Bop (fun j y => τ * W j y) v x) hβ hD hc (hZ x hxK) (hR x hxK) (hd x hxK)
        (Bop_const_mul τ hW v x) hτ1 hτD hτm hτR
      linarith [key]
    · obtain ⟨h0, h1, -⟩ := vanish_outside hx
      have hB0 := Bop_vanish ha hX hq hθc hv hx
      have hQ0 : Qfun a (fun j y => τ * W j y) (fun y => τ ^ 2 * N y) (fun _ => 4 * m * τ)
          (1 / 2) v x = 0 := by
        simp [Qfun, Mgrad, quad, grad, h0, h1]
      rw [hQ0, hB0]
      simp [h0, h1]
  have hL : Integrable (fun x => α * τ * ∑ i, pd i v x ^ 2 + β / 2 * τ ^ 3 * v x ^ 2) :=
    (hG.const_mul _).add (hV.const_mul _)
  have hmono := integral_mono hL hI (fun x => hpt x)
  rw [integral_add (hG.const_mul _) (hV.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  linarith

/-- T3+T5: the strict-weight principal estimate for the UNCHANGED phase `ϑ`, in conjugated
form `v = exp(τϑ) w`, against `exp(2τϑ) (div(a∇w))²`, from the pointwise coefficient bounds of
the actual phase fields `W = a∇ϑ`, `N = a(∇ϑ,∇ϑ)` on `K ⊇ tsupport w`; `m` any real. -/
theorem unchanged_phase_estimate_of_coefficient_bounds (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ w : (CalderonN.X d) → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (K : Set (CalderonN.X d)) (hK : tsupport w ⊆ K)
    (m α β D R0 d0 : ℝ) (hβ : 0 < β) (hD : 0 ≤ D)
    (hcoef : ∀ x ∈ K, ∀ ξ : Fin d → ℝ, α * ∑ i, ξ i ^ 2 ≤
      Mgrad a (phaseField a ϑ) x ξ + 4 * m * quad a x ξ +
        D * (∑ j, phaseField a ϑ j x * ξ j) ^ 2)
    (hZ : ∀ x ∈ K, β ≤ 2 * ∑ j, phaseField a ϑ j x * pd j (phaseNorm a ϑ) x -
      4 * m * phaseNorm a ϑ x)
    (hR : ∀ x ∈ K, |Lop a (divV (phaseField a ϑ)) x| ≤ R0)
    (hd : ∀ x ∈ K, |divV (phaseField a ϑ) x| ≤ d0)
    (τ : ℝ) (hτ1 : 1 ≤ τ) (hτD : D ≤ τ) (hτm : 32 * m ^ 2 ≤ β * τ)
    (hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ) :
    α * τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
      β / 2 * τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
      ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  have hv : ContDiff ℝ ∞ (fun y => Real.exp (τ * ϑ y) * w y) := by fun_prop
  have hvc : HasCompactSupport (fun y => Real.exp (τ * ϑ y) * w y) :=
    HasCompactSupport.mul_left (f := fun y => Real.exp (τ * ϑ y)) hwc
  have hsupp : tsupport (fun y => Real.exp (τ * ϑ y) * w y) ⊆ K :=
    (tsupport_mul_subset_right (f := fun y => Real.exp (τ * ϑ y))).trans hK
  have h := principal_estimate_of_coefficient_bounds ha hsymm (contDiff_phaseField ha hϑ)
    (contDiff_phaseNorm ha hϑ) hv hvc K hsupp m α β D R0 d0 hβ hD hcoef hZ hR hd τ hτ1 hτD
    hτm hτR
  have hconj : ∀ x, (Sop a (fun y => τ ^ 2 * phaseNorm a ϑ y)
      (fun y => Real.exp (τ * ϑ y) * w y) x +
      Bop (fun j y => τ * phaseField a ϑ j y) (fun y => Real.exp (τ * ϑ y) * w y) x) ^ 2 =
      Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
    intro x
    have h1 := conj_unchanged_phase ha hsymm hϑ hv τ x
    have hvw : (fun y => Real.exp (-(τ * ϑ y)) * (Real.exp (τ * ϑ y) * w y)) = w := by
      funext y
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [hvw] at h1
    have e : Real.exp (2 * (τ * ϑ x)) * Real.exp (-(τ * ϑ x)) ^ 2 = 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add,
        show 2 * (τ * ϑ x) + (-(τ * ϑ x) + -(τ * ϑ x)) = 0 by ring, Real.exp_zero]
    rw [h1, mul_pow, ← mul_assoc, e, one_mul]
  have hint : (∫ x, (Sop a (fun y => τ ^ 2 * phaseNorm a ϑ y)
      (fun y => Real.exp (τ * ϑ y) * w y) x +
      Bop (fun j y => τ * phaseField a ϑ j y) (fun y => Real.exp (τ * ϑ y) * w y) x) ^ 2) =
      ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 :=
    congrArg (fun f : (CalderonN.X d) → ℝ => ∫ x, f x) (funext hconj)
  exact h.trans hint.le

end SignedShift

end CalderonN.Carleman.Strict
