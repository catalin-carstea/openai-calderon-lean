module

public import Proof.CalderonN.StrictCarlemanEstimate
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

variable {d : ℕ} [NeZero d]

section StrictMargins

/-- Sup-norm to Euclidean sum of squares on `Fin d → ℝ`. -/
theorem sum_sq_le_card_add_one_norm_sq (ξ : Fin d → ℝ) : ∑ i, ξ i ^ 2 ≤ ((d : ℝ) + 1) * ‖ξ‖ ^ 2 := by
  have h : ∀ i, ξ i ^ 2 ≤ ‖ξ‖ ^ 2 := by
    intro i
    have h1 : ‖ξ i‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ i
    rw [Real.norm_eq_abs] at h1
    calc ξ i ^ 2 = |ξ i| ^ 2 := (sq_abs _).symm
      _ ≤ ‖ξ‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  calc
    _ ≤ ∑ _i : Fin d, ‖ξ‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = (d : ℝ) * ‖ξ‖ ^ 2 := by simp
    _ ≤ _ := by gcongr; linarith

/-- A continuous positive function on a compact set has a positive lower bound. -/
theorem exists_pos_lower_on_compact {K : Set (CalderonN.X d)} (hK : IsCompact K) {f : (CalderonN.X d) → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ K, β ≤ f x := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn h hf
  exact ⟨f x0, hpos x0 hx0, fun x hx => hmin hx⟩

/-- T6a: uniform rank-one (Finsler) coercivity by compactness. Tangential positivity of a
continuous quadratic family on the kernel of a continuous linear family gives ONE `D ≥ 0`
and ONE `α > 0` with `α Σξᵢ² ≤ Q + Dℓ²` on all of `K`. No sign condition on `Q` itself. -/
theorem uniform_rank_one_coercivity {K : Set (CalderonN.X d)} (hK : IsCompact K)
    (Q ℓ : (CalderonN.X d) → (Fin d → ℝ) → ℝ)
    (hQc : Continuous (fun p : (CalderonN.X d) × (Fin d → ℝ) => Q p.1 p.2))
    (hℓc : Continuous (fun p : (CalderonN.X d) × (Fin d → ℝ) => ℓ p.1 p.2))
    (hQh : ∀ x (c : ℝ) ξ, Q x (c • ξ) = c ^ 2 * Q x ξ)
    (hℓh : ∀ x (c : ℝ) ξ, ℓ x (c • ξ) = c * ℓ x ξ)
    (hpos : ∀ x ∈ K, ∀ ξ, ξ ≠ 0 → ℓ x ξ = 0 → 0 < Q x ξ) :
    ∃ D α : ℝ, 0 ≤ D ∧ 0 < α ∧ ∀ x ∈ K, ∀ ξ : Fin d → ℝ,
      α * ∑ i, ξ i ^ 2 ≤ Q x ξ + D * ℓ x ξ ^ 2 := by
  set S : Set (Fin d → ℝ) := Metric.sphere 0 1 with hSdef
  set T : Set ((CalderonN.X d) × (Fin d → ℝ)) := K ×ˢ S with hTdef
  have hT : IsCompact T := hK.prod (isCompact_sphere 0 1)
  set F : ℕ → (CalderonN.X d) × (Fin d → ℝ) → ℝ := fun n p => Q p.1 p.2 + (n : ℝ) * ℓ p.1 p.2 ^ 2 with hF
  have hFc : ∀ n, Continuous (F n) := fun n => hQc.add (continuous_const.mul (hℓc.pow 2))
  set C : ℕ → Set ((CalderonN.X d) × (Fin d → ℝ)) := fun n => T ∩ F n ⁻¹' Set.Iic 0 with hC
  have hCcl : ∀ n, IsClosed (C n) := fun n =>
    hT.isClosed.inter (isClosed_Iic.preimage (hFc n))
  have hCc : ∀ n, IsCompact (C n) := fun n => hT.of_isClosed_subset (hCcl n) Set.inter_subset_left
  have hmono : ∀ n n', n ≤ n' → C n' ⊆ C n := by
    intro n n' hnn p hp
    refine ⟨hp.1, ?_⟩
    have h1 : F n' p ≤ 0 := hp.2
    have h2 : F n p ≤ F n' p := by
      simp only [hF]
      have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
      nlinarith [sq_nonneg (ℓ p.1 p.2)]
    exact le_trans h2 h1
  have hempty : ∃ n, C n = ∅ := by
    by_contra hne
    push_neg at hne
    have hdir : Directed (· ⊇ ·) C := fun n n' =>
      ⟨max n n', hmono n _ (le_max_left _ _), hmono n' _ (le_max_right _ _)⟩
    obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir
      (fun n => hne n) hCc hCcl
    rw [Set.mem_iInter] at hp
    have hpT : p ∈ T := (hp 0).1
    have hle : ∀ n : ℕ, Q p.1 p.2 + (n : ℝ) * ℓ p.1 p.2 ^ 2 ≤ 0 := fun n => (hp n).2
    have hℓ0 : ℓ p.1 p.2 = 0 := by
      by_contra hℓ
      have hsq : 0 < ℓ p.1 p.2 ^ 2 := by positivity
      obtain ⟨n, hn⟩ := exists_nat_gt (-Q p.1 p.2 / ℓ p.1 p.2 ^ 2)
      have h1 := hle n
      rw [div_lt_iff₀ hsq] at hn
      linarith
    have hξ : p.2 ≠ 0 := by
      intro h0
      have h1 : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hpT.2
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hQ := hpos p.1 hpT.1 p.2 hξ hℓ0
    have h0 := hle 0
    simp only [Nat.cast_zero, zero_mul, add_zero] at h0
    linarith
  obtain ⟨n, hn⟩ := hempty
  have hFpos : ∀ p ∈ T, 0 < F n p := by
    intro p hp
    by_contra h
    push_neg at h
    have : p ∈ C n := ⟨hp, h⟩
    rw [hn] at this
    exact this
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · exact ⟨n, 1, Nat.cast_nonneg n, one_pos, by simp [hK0]⟩
  have hSne : S.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hTne : T.Nonempty := hKne.prod hSne
  obtain ⟨p0, hp0, hmin⟩ := hT.exists_isMinOn hTne (hFc n).continuousOn
  have hα0 : 0 < F n p0 := hFpos p0 hp0
  have hα3 : 0 < F n p0 / ((d : ℝ) + 1) := div_pos hα0 (by positivity)
  refine ⟨n, F n p0 / ((d : ℝ) + 1), Nat.cast_nonneg n, hα3, ?_⟩
  intro x hx ξ
  have hQ0 : Q x 0 = 0 := by
    have := hQh x 0 0
    rw [smul_zero] at this
    rw [this]; ring
  have hℓ0 : ℓ x 0 = 0 := by
    have := hℓh x 0 0
    rw [smul_zero] at this
    rw [this]; ring
  by_cases hξ : ξ = 0
  · subst hξ
    simp [hQ0, hℓ0]
  have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set η : Fin d → ℝ := ‖ξ‖⁻¹ • ξ with hη
  have hηS : (x, η) ∈ T := by
    refine ⟨hx, ?_⟩
    show η ∈ Metric.sphere (0 : Fin d → ℝ) 1
    rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hmin' : F n p0 ≤ F n (x, η) := hmin hηS
  have hξη : ξ = ‖ξ‖ • η := by
    rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hFξ : Q x ξ + (n : ℝ) * ℓ x ξ ^ 2 = ‖ξ‖ ^ 2 * F n (x, η) := by
    conv_lhs => rw [hξη, hQh, hℓh]
    simp only [hF]
    ring
  have h3 := sum_sq_le_card_add_one_norm_sq ξ
  have hfin : F n p0 / ((d : ℝ) + 1) * ∑ i, ξ i ^ 2 ≤ F n p0 * ‖ξ‖ ^ 2 := by
    calc
      _ ≤ (F n p0 / ((d : ℝ) + 1)) * (((d : ℝ) + 1) * ‖ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hα3.le
      _ = _ := by
        rw [← mul_assoc, div_mul_cancel₀ _ (by positivity)]
  have hfin2 : F n p0 * ‖ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * F n (x, η) := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hmin' (sq_nonneg _)
  rw [hFξ]
  linarith

variable {a : Fin d → Fin d → (CalderonN.X d) → ℝ}

theorem contDiff_Lop (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) {f : (CalderonN.X d) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (Lop a f) := by
  have : ∀ i k, ContDiff ℝ ∞ (fun y => a i k y) := ha
  unfold Lop; fun_prop

theorem Mgrad_smul (W : Fin d → (CalderonN.X d) → ℝ) (x : CalderonN.X d)
    (c : ℝ) (ξ : Fin d → ℝ) :
    Mgrad a W x (c • ξ) = c ^ 2 * Mgrad a W x ξ := by
  have h₁ : (∑ i, ∑ j, ∑ k, a i k x * (c * ξ k) * pd i (W j) x * (c * ξ j)) =
      c ^ 2 * ∑ i, ∑ j, ∑ k, a i k x * ξ k * pd i (W j) x * ξ j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have h₂ : (∑ j, W j x * ∑ i, ∑ k, pd j (a i k) x * (c * ξ i) * (c * ξ k)) =
      c ^ 2 * ∑ j, W j x * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun k _ => by ring
  simp only [Mgrad, Pi.smul_apply, smul_eq_mul, h₁, h₂]
  ring

theorem quad_smul (x : CalderonN.X d) (c : ℝ) (ξ : Fin d → ℝ) :
    quad a x (c • ξ) = c ^ 2 * quad a x ξ := by
  simp only [quad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem lin_smul (W : Fin d → (CalderonN.X d) → ℝ)
    (x : CalderonN.X d) (c : ℝ) (ξ : Fin d → ℝ) :
    ∑ j, W j x * (c • ξ) j = c * ∑ j, W j x * ξ j := by
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- T6: the coordinate strict-weight Carleman estimate for the UNCHANGED phase `ϑ` on a compact
`K`. Hypotheses are exactly the signed-`m` coordinate strict pseudo-convexity of `ϑ` on `K`
(tangential: shifted `Mgrad` positive on `ker (W·)`; normal: `Z > 0`); `m` is any real. The
constants `C, τ0` are chosen BEFORE `τ` and `w`. -/
theorem strict_weight_carleman_of_coordinate_strictness (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ : (CalderonN.X d) → ℝ} (hϑ : ContDiff ℝ ∞ ϑ)
    {K : Set (CalderonN.X d)} (hK : IsCompact K) (m : ℝ)
    (htan : ∀ x ∈ K, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j x * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) x ξ + 4 * m * quad a x ξ)
    (hnor : ∀ x ∈ K, 0 < 2 * ∑ j, phaseField a ϑ j x * pd j (phaseNorm a ϑ) x -
      4 * m * phaseNorm a ϑ x) :
    ∃ C τ0 : ℝ, 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : (CalderonN.X d) → ℝ, ContDiff ℝ ∞ w →
      HasCompactSupport w → tsupport w ⊆ K →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  set W := phaseField a ϑ with hWdef
  set N := phaseNorm a ϑ with hNdef
  have hW : ∀ j, ContDiff ℝ ∞ (W j) := contDiff_phaseField ha hϑ
  have hN : ContDiff ℝ ∞ N := contDiff_phaseNorm ha hϑ
  have hac : ∀ i k, Continuous (a i k) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (pd j (a i k)) := fun j i k => (contDiff_pd (ha i k)).continuous
  have hWc : ∀ j, Continuous (W j) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (pd i (W j)) := fun i j => (contDiff_pd (hW j)).continuous
  have hQc : Continuous (fun p : (CalderonN.X d) × (Fin d → ℝ) =>
      Mgrad a W p.1 p.2 + 4 * m * quad a p.1 p.2) := by
    simp only [Mgrad, quad]
    fun_prop
  have hℓc : Continuous (fun p : (CalderonN.X d) × (Fin d → ℝ) => ∑ j, W j p.1 * p.2 j) := by
    fun_prop
  obtain ⟨D, α, hD, hα, hcoef⟩ := uniform_rank_one_coercivity hK
    (fun x ξ => Mgrad a W x ξ + 4 * m * quad a x ξ) (fun x ξ => ∑ j, W j x * ξ j) hQc hℓc
    (by
      intro x c ξ
      rw [Mgrad_smul, quad_smul]
      ring)
    (fun x c ξ => lin_smul W x c ξ)
    htan
  have hZc : ContinuousOn (fun x => 2 * ∑ j, W j x * pd j N x - 4 * m * N x) K := by
    have : ∀ j, Continuous (pd j N) := fun j => (contDiff_pd hN).continuous
    have : Continuous N := hN.continuous
    refine Continuous.continuousOn ?_
    fun_prop
  obtain ⟨β, hβ, hZ⟩ := exists_pos_lower_on_compact hK hZc hnor
  obtain ⟨R0, hR⟩ := hK.exists_bound_of_continuousOn
    (contDiff_Lop ha (contDiff_divV hW)).continuous.continuousOn
  obtain ⟨d0, hd⟩ := hK.exists_bound_of_continuousOn (contDiff_divV hW).continuous.continuousOn
  set c : ℝ := min α (β / 2) with hcdef
  have hc : 0 < c := lt_min hα (half_pos hβ)
  refine ⟨1 / c, max (max 1 D) (max (32 * m ^ 2 / β) (4 * (R0 + D * d0 ^ 2 / 2) / β)),
    one_div_pos.mpr hc, le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro τ hτ w hw hwc hK'
  have hτ1 : 1 ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
  have hτD : D ≤ τ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
  have hτm : 32 * m ^ 2 ≤ β * τ := by
    have h1 : 32 * m ^ 2 / β ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτ
    rw [div_le_iff₀ hβ] at h1
    linarith
  have hτR : 4 * (R0 + D * d0 ^ 2 / 2) ≤ β * τ := by
    have h1 : 4 * (R0 + D * d0 ^ 2 / 2) / β ≤ τ :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ
    rw [div_le_iff₀ hβ] at h1
    linarith
  have h := unchanged_phase_estimate_of_coefficient_bounds ha hsymm hϑ hw hwc K hK' m α β D R0
    d0 hβ hD hcoef hZ (fun x hx => by simpa [Real.norm_eq_abs] using hR x hx)
    (fun x hx => by simpa [Real.norm_eq_abs] using hd x hx) τ hτ1 hτD hτm hτR
  have hG0 : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV0 : 0 ≤ ∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hτ0 : 0 ≤ τ := by linarith
  have e1 : c * (τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2)) ≤
      α * τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hτ0) hG0
  have e2 : c * (τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2)) ≤
      β / 2 * τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hτ0 3)) hV0
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
  linarith

theorem sum_sq_pos_of_ne_zero {ξ : Fin d → ℝ} (hξ : ξ ≠ 0) : 0 < ∑ i, ξ i ^ 2 := by
  by_contra hle
  push_neg at hle
  apply hξ
  funext i
  have hi : ξ i ^ 2 ≤ 0 := by
    have := Finset.single_le_sum (f := fun i => ξ i ^ 2) (fun j _ => sq_nonneg (ξ j))
      (Finset.mem_univ i)
    linarith
  exact (pow_eq_zero_iff (n := 2) (by norm_num)).mp (le_antisymm hi (sq_nonneg _))

/-- T9: from coordinate source strictness at ONE point `p` (tangential Hessian plus normal
Hessian value `h` positive on `ker (W(p)·)`, `N(p) > 0`), CONSTRUCT a real shift `m` (either
sign), a closed ball around `p`, and the strict-weight Carleman constants, chosen before `τ`
and `w`. -/
theorem local_strict_weight_carleman_of_point_strictness (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hsymm : ∀ i k, a i k = a k i) {ϑ : (CalderonN.X d) → ℝ} (hϑ : ContDiff ℝ ∞ ϑ) (p : (CalderonN.X d))
    (hN : 0 < phaseNorm a ϑ p)
    (hstrict : ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) :
    ∃ m r C τ0 : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ0 ∧ ∀ τ : ℝ, τ0 ≤ τ → ∀ w : (CalderonN.X d) → ℝ,
      ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ Metric.closedBall p r →
      τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * ϑ y) * w y) x ^ 2) +
        τ ^ 3 * (∫ x, (Real.exp (τ * ϑ x) * w x) ^ 2) ≤
        C * ∫ x, Real.exp (2 * (τ * ϑ x)) * Lop a w x ^ 2 := by
  set W := phaseField a ϑ with hWdef
  set N := phaseNorm a ϑ with hNdef
  set h : ℝ := (∑ j, W j p * pd j N p) / (2 * N p) with hhdef
  have hW : ∀ j, ContDiff ℝ ∞ (W j) := contDiff_phaseField ha hϑ
  have hNs : ContDiff ℝ ∞ N := contDiff_phaseNorm ha hϑ
  have hac : ∀ i k, Continuous (a i k) := fun i k => (ha i k).continuous
  have hdac : ∀ j i k, Continuous (pd j (a i k)) := fun j i k => (contDiff_pd (ha i k)).continuous
  have hWc : ∀ j, Continuous (W j) := fun j => (hW j).continuous
  have hdWc : ∀ i j, Continuous (pd i (W j)) := fun i j => (contDiff_pd (hW j)).continuous
  have hNc : Continuous N := hNs.continuous
  have hdNc : ∀ j, Continuous (pd j N) := fun j => (contDiff_pd hNs).continuous
  -- the compact tangential unit set at `p`
  set Sg : Set (Fin d → ℝ) := Metric.sphere 0 1 ∩ {ξ | ∑ j, W j p * ξ j = 0} with hSg
  have hSgc : IsCompact Sg := (isCompact_sphere 0 1).inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hfc : Continuous (fun ξ : Fin d → ℝ => Mgrad a W p ξ + 4 * h * quad a p ξ) := by
    simp only [Mgrad, quad]; fun_prop
  have hqc : Continuous (fun ξ : Fin d → ℝ => quad a p ξ) := by
    simp only [quad]; fun_prop
  obtain ⟨μ, hμ, hμf⟩ : ∃ μ : ℝ, 0 < μ ∧ ∀ ξ ∈ Sg, μ ≤ Mgrad a W p ξ + 4 * h * quad a p ξ := by
    rcases Sg.eq_empty_or_nonempty with h0 | hne
    · exact ⟨1, one_pos, by simp [h0]⟩
    obtain ⟨ξ0, hξ0, hmin⟩ := hSgc.exists_isMinOn hne hfc.continuousOn
    refine ⟨_, hstrict ξ0 ?_ hξ0.2, fun ξ hξ => hmin hξ⟩
    intro h0
    have h1 : ‖ξ0‖ = 1 := mem_sphere_zero_iff_norm.mp hξ0.1
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨B, hB⟩ := hSgc.exists_bound_of_continuousOn hqc.continuousOn
  set Λ : ℝ := max B 1 with hΛ
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hΛne : Λ ≠ 0 := hΛpos.ne'
  have hc0 : 0 < μ / (2 * Λ) := div_pos hμ (mul_pos two_pos hΛpos)
  set m : ℝ := h - μ / (8 * Λ) with hm
  -- tangential positivity at `p` for the constructed signed `m`
  have htanp : ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∑ j, W j p * ξ j = 0 →
      0 < Mgrad a W p ξ + 4 * m * quad a p ξ := by
    intro ξ hξ hker
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    set η : Fin d → ℝ := ‖ξ‖⁻¹ • ξ with hη
    have hηS : η ∈ Sg := by
      refine ⟨?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
      · show ∑ j, W j p * η j = 0
        rw [hη, lin_smul, hker, mul_zero]
    have h1 := hμf η hηS
    have h2 : quad a p η ≤ Λ := by
      have := hB η hηS
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    have hη' : 0 < Mgrad a W p η + 4 * m * quad a p η := by
      have e : Mgrad a W p η + 4 * m * quad a p η =
          (Mgrad a W p η + 4 * h * quad a p η) - μ / (2 * Λ) * quad a p η := by
        rw [hm]; ring
      have h3 : μ / (2 * Λ) * quad a p η ≤ μ / (2 * Λ) * Λ :=
        mul_le_mul_of_nonneg_left h2 hc0.le
      have h4 : μ / (2 * Λ) * Λ = μ / 2 := by
        rw [div_mul_eq_mul_div]; exact mul_div_mul_right μ 2 hΛne
      rw [e]; linarith
    have hξη : ξ = ‖ξ‖ • η := by rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hξη, Mgrad_smul, quad_smul]
    have : 0 < ‖ξ‖ ^ 2 := by positivity
    nlinarith
  -- normal margin at `p`
  have hZp : 0 < 2 * ∑ j, W j p * pd j N p - 4 * m * N p := by
    have e : 2 * ∑ j, W j p * pd j N p - 4 * m * N p = μ / (2 * Λ) * N p := by
      have hNne : N p ≠ 0 := hN.ne'
      have hsN : (∑ j, W j p * pd j N p) / (2 * N p) * N p = (∑ j, W j p * pd j N p) / 2 := by
        rw [div_mul_eq_mul_div]; exact mul_div_mul_right _ 2 hNne
      rw [hm, hhdef]
      linear_combination (-4) * hsN
    rw [e]; exact mul_pos hc0 hN
  -- uniform rank-one coercivity at the point
  have hQc : Continuous (fun q : (CalderonN.X d) × (Fin d → ℝ) =>
      Mgrad a W q.1 q.2 + 4 * m * quad a q.1 q.2) := by
    simp only [Mgrad, quad]; fun_prop
  have hℓc : Continuous (fun q : (CalderonN.X d) × (Fin d → ℝ) => ∑ j, W j q.1 * q.2 j) := by
    fun_prop
  obtain ⟨D, α, hD, hα, hcoef⟩ := uniform_rank_one_coercivity isCompact_singleton
    (fun x ξ => Mgrad a W x ξ + 4 * m * quad a x ξ) (fun x ξ => ∑ j, W j x * ξ j) hQc hℓc
    (fun x c ξ => by simp only [Mgrad_smul, quad_smul]; ring)
    (fun x c ξ => lin_smul W x c ξ)
    (fun x hx ξ hξ hker => by
      rw [Set.mem_singleton_iff.mp hx] at hker ⊢
      exact htanp ξ hξ hker)
  -- persistence near `p` (tube lemma over the compact unit sphere)
  have hFc : Continuous (fun q : (CalderonN.X d) × (Fin d → ℝ) =>
      Mgrad a W q.1 q.2 + 4 * m * quad a q.1 q.2 + D * (∑ j, W j q.1 * q.2 j) ^ 2) :=
    hQc.add (continuous_const.mul (hℓc.pow 2))
  have hev : ∀ᶠ x in nhds p, ∀ ξ ∈ Metric.sphere (0 : Fin d → ℝ) 1,
      0 < Mgrad a W x ξ + 4 * m * quad a x ξ + D * (∑ j, W j x * ξ j) ^ 2 := by
    apply (isCompact_sphere (0 : Fin d → ℝ) 1).eventually_forall_of_forall_eventually
    intro ξ0 hξ0
    have hne : ξ0 ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hξ0
      exact zero_ne_one hξ0
    have hpos0 : 0 < Mgrad a W p ξ0 + 4 * m * quad a p ξ0 + D * (∑ j, W j p * ξ0 j) ^ 2 := by
      have h1 : α * ∑ i, ξ0 i ^ 2 ≤ Mgrad a W p ξ0 + 4 * m * quad a p ξ0 +
          D * (∑ j, W j p * ξ0 j) ^ 2 := hcoef p (Set.mem_singleton p) ξ0
      have h2 := mul_pos hα (sum_sq_pos_of_ne_zero hne)
      linarith
    exact (hFc.continuousAt (x := (p, ξ0))).eventually (lt_mem_nhds hpos0)
  have hZc : Continuous (fun x => 2 * ∑ j, W j x * pd j N x - 4 * m * N x) := by
    fun_prop
  have hZev : ∀ᶠ x in nhds p, 0 < 2 * ∑ j, W j x * pd j N x - 4 * m * N x :=
    (hZc.continuousAt (x := p)).eventually (lt_mem_nhds hZp)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev.and hZev)
  have hK : ∀ x ∈ Metric.closedBall p (ε / 2), dist x p < ε := fun x hx =>
    lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (half_lt_self hε)
  have htanK : ∀ x ∈ Metric.closedBall p (ε / 2), ∀ ξ : Fin d → ℝ, ξ ≠ 0 →
      ∑ j, W j x * ξ j = 0 → 0 < Mgrad a W x ξ + 4 * m * quad a x ξ := by
    intro x hx ξ hξ hker
    have hx' := (hball (hK x hx)).1
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    set η : Fin d → ℝ := ‖ξ‖⁻¹ • ξ with hη
    have hηS : η ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hkerη : ∑ j, W j x * η j = 0 := by rw [hη, lin_smul, hker, mul_zero]
    have h1 := hx' η hηS
    rw [hkerη] at h1
    have hη' : 0 < Mgrad a W x η + 4 * m * quad a x η := by nlinarith
    have hξη : ξ = ‖ξ‖ • η := by rw [hη, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [hξη, Mgrad_smul, quad_smul]
    have : 0 < ‖ξ‖ ^ 2 := by positivity
    nlinarith
  have hnorK : ∀ x ∈ Metric.closedBall p (ε / 2),
      0 < 2 * ∑ j, W j x * pd j N x - 4 * m * N x := fun x hx => (hball (hK x hx)).2
  obtain ⟨C, τ0, hC, hτ0, hest⟩ := strict_weight_carleman_of_coordinate_strictness ha hsymm hϑ
    (isCompact_closedBall p (ε / 2)) m htanK hnorK
  exact ⟨m, ε / 2, C, τ0, half_pos hε, hC, hτ0, hest⟩

/-- J3.a: the phase field of a scalar-rescaled coefficient. -/
theorem phaseField_smul_coeff {ρ ϑ : (CalderonN.X d) → ℝ} (j : Fin d) (y : (CalderonN.X d)) :
    phaseField (fun i k z => ρ z * a i k z) ϑ j y = ρ y * phaseField a ϑ j y := by
  simp only [phaseField, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- J3.a: the phase norm of a scalar-rescaled coefficient. -/
theorem phaseNorm_smul_coeff {ρ ϑ : (CalderonN.X d) → ℝ} (y : (CalderonN.X d)) :
    phaseNorm (fun i k z => ρ z * a i k z) ϑ y = ρ y * phaseNorm a ϑ y := by
  simp only [phaseNorm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- J3.a: the quadratic form of a scalar-rescaled coefficient. -/
theorem quad_smul_coeff {ρ : (CalderonN.X d) → ℝ} (x : (CalderonN.X d)) (ξ : Fin d → ℝ) :
    quad (fun i k z => ρ z * a i k z) x ξ = ρ x * quad a x ξ := by
  simp only [quad, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- J3.b: exact `Mgrad` rescaling for `a' = ρa`, `W' = ρW` (any smooth `W`). -/
theorem Mgrad_smul_coeff {ρ : (CalderonN.X d) → ℝ} (hρ : ContDiff ℝ ∞ ρ) (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    {W : Fin d → (CalderonN.X d) → ℝ} (hW : ∀ j, ContDiff ℝ ∞ (W j)) (x : (CalderonN.X d)) (ξ : Fin d → ℝ) :
    Mgrad (fun i k z => ρ z * a i k z) (fun j y => ρ y * W j y) x ξ =
      ρ x ^ 2 * Mgrad a W x ξ +
      4 * ρ x * (∑ i, ∑ l, a i l x * ξ l * pd i ρ x) * (∑ j, W j x * ξ j) -
      2 * ρ x * (∑ j, W j x * pd j ρ x) * quad a x ξ := by
  have h1 : ∀ i j, pd i (fun y => ρ y * W j y) x = pd i ρ x * W j x + ρ x * pd i (W j) x :=
    fun i j => pd_mul hρ (hW j) x
  have h2 : ∀ j i k, pd j (fun z => ρ z * a i k z) x =
      pd j ρ x * a i k x + ρ x * pd j (a i k) x :=
    fun j i k => pd_mul hρ (ha i k) x
  let U := ∑ i, ∑ j, ∑ l, a i l x * ξ l * pd i (W j) x * ξ j
  let V := ∑ j, W j x * ∑ i, ∑ k, pd j (a i k) x * ξ i * ξ k
  let A := ∑ i, ∑ l, a i l x * ξ l * pd i ρ x
  let B := ∑ j, W j x * ξ j
  let C := ∑ j, W j x * pd j ρ x
  have hA (i : Fin d) :
      (∑ j, ∑ l, ρ x * a i l x * ξ l * (pd i ρ x * W j x) * ξ j) =
        ρ x * ((∑ l, a i l x * ξ l * pd i ρ x) * B) := by
    simp only [B, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hU : (∑ i, ∑ j, ∑ l, ρ x * a i l x * ξ l * (pd i ρ x * W j x + ρ x * pd i (W j) x) * ξ j) =
      ρ x * A * B + ρ x ^ 2 * U := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    have hA' : (∑ i, ∑ j, ∑ l, ρ x * a i l x * ξ l * (pd i ρ x * W j x) * ξ j) =
        ρ x * A * B := by
      simp_rw [hA, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [A, mul_assoc, Finset.sum_mul]
    rw [hA']
    congr 1
    simp only [U, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have hV : (∑ j, (ρ x * W j x) * ∑ i, ∑ k,
      (pd j ρ x * a i k x + ρ x * pd j (a i k) x) * ξ i * ξ k) =
      ρ x * C * quad a x ξ + ρ x ^ 2 * V := by
    simp only [add_mul, Finset.sum_add_distrib, mul_add]
    congr 1
    · calc
        _ = ∑ j, (ρ x * (W j x * pd j ρ x)) * quad a x ξ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [quad, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by
          simp only [C, Finset.sum_mul, Finset.mul_sum]
    · simp only [V, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun k _ => by ring
  simp only [Mgrad, h1, h2, hU,hV]
  change 4 * (ρ x * A * B + ρ x ^ 2 * U) - 2 * (ρ x * C * quad a x ξ + ρ x ^ 2 * V) =
    ρ x ^ 2 * (4 * U - 2 * V) + 4 * ρ x * A * B - 2 * ρ x * C * quad a x ξ
  ring

/-- J3.d: the T9 point criterion transports EXACTLY from `a` to `b = ρa` for a smooth `ρ` with
`ρ(p) > 0` (the `∓2ρ(W·∇ρ)Q` terms cancel; the mixed term dies on the kernel). Phase unchanged,
no sign condition on `h` or `∇ρ`. -/
theorem point_strictness_smul {b a : Fin d → Fin d → (CalderonN.X d) → ℝ} {ρ ϑ : (CalderonN.X d) → ℝ}
    (hb : ∀ i k z, b i k z = ρ z * a i k z) (hρ : ContDiff ℝ ∞ ρ)
    (ha : ∀ i k, ContDiff ℝ ∞ (a i k)) (hϑ : ContDiff ℝ ∞ ϑ) (p : (CalderonN.X d)) (hρp : 0 < ρ p)
    (hN : 0 < phaseNorm a ϑ p)
    (hstrict : ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∑ j, phaseField a ϑ j p * ξ j = 0 →
      0 < Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) :
    0 < phaseNorm b ϑ p ∧
    ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∑ j, phaseField b ϑ j p * ξ j = 0 →
      0 < Mgrad b (phaseField b ϑ) p ξ +
        4 * ((∑ j, phaseField b ϑ j p * pd j (phaseNorm b ϑ) p) / (2 * phaseNorm b ϑ p)) *
          quad b p ξ := by
  have hb' : b = fun i k z => ρ z * a i k z :=
    funext fun i => funext fun k => funext fun z => hb i k z
  subst hb'
  have hW : ∀ j, ContDiff ℝ ∞ (phaseField a ϑ j) := contDiff_phaseField ha hϑ
  have hNs : ContDiff ℝ ∞ (phaseNorm a ϑ) := contDiff_phaseNorm ha hϑ
  have hF : phaseField (fun i k z => ρ z * a i k z) ϑ = fun j y => ρ y * phaseField a ϑ j y :=
    funext fun j => funext fun y => phaseField_smul_coeff j y
  have hNN : phaseNorm (fun i k z => ρ z * a i k z) ϑ = fun y => ρ y * phaseNorm a ϑ y :=
    funext fun y => phaseNorm_smul_coeff y
  simp only [hF, hNN]
  refine ⟨mul_pos hρp hN, fun ξ hξ hker => ?_⟩
  have hker0 : ∑ j, phaseField a ϑ j p * ξ j = 0 := by
    have e : ∑ j, ρ p * phaseField a ϑ j p * ξ j = ρ p * ∑ j, phaseField a ϑ j p * ξ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at hker
    exact (mul_eq_zero.mp hker).resolve_left hρp.ne'
  have hpN : ∀ j, pd j (fun y => ρ y * phaseNorm a ϑ y) p =
      pd j ρ p * phaseNorm a ϑ p + ρ p * pd j (phaseNorm a ϑ) p :=
    fun j => pd_mul hρ hNs p
  rw [Mgrad_smul_coeff hρ ha hW, quad_smul_coeff, hker0]
  simp only [hpN]
  have h0 := hstrict ξ hξ hker0
  have hNne : phaseNorm a ϑ p ≠ 0 := hN.ne'
  have hρne : ρ p ≠ 0 := hρp.ne'
  have e : (∑ j, ρ p * phaseField a ϑ j p *
      (pd j ρ p * phaseNorm a ϑ p + ρ p * pd j (phaseNorm a ϑ) p)) /
      (2 * (ρ p * phaseNorm a ϑ p)) =
      (∑ j, phaseField a ϑ j p * pd j ρ p) / 2 +
      ρ p * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) := by
    have hnum : (∑ j, ρ p * phaseField a ϑ j p *
        (pd j ρ p * phaseNorm a ϑ p + ρ p * pd j (phaseNorm a ϑ) p)) =
        (ρ p * phaseNorm a ϑ p) * (∑ j, phaseField a ϑ j p * pd j ρ p) +
          (ρ p)^2 * ∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hnum]
    field_simp <;> ring
  rw [e]
  have e2 : ρ p ^ 2 * Mgrad a (phaseField a ϑ) p ξ +
      4 * ρ p * (∑ i, ∑ l, a i l p * ξ l * pd i ρ p) * 0 -
      2 * ρ p * (∑ j, phaseField a ϑ j p * pd j ρ p) * quad a p ξ +
      4 * ((∑ j, phaseField a ϑ j p * pd j ρ p) / 2 +
        ρ p * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p))) *
        (ρ p * quad a p ξ) =
      ρ p ^ 2 * (Mgrad a (phaseField a ϑ) p ξ +
        4 * ((∑ j, phaseField a ϑ j p * pd j (phaseNorm a ϑ) p) / (2 * phaseNorm a ϑ p)) *
          quad a p ξ) := by ring
  rw [e2]
  exact mul_pos (pow_pos hρp 2) h0

end StrictMargins

end CalderonN.Carleman.Strict
