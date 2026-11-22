module

public import Proof.CalderonN.ActualCoefficientFirstVariationJets

import Proof.CalderonN.CompactFiniteJets
import Mathlib.Tactic

/-! With the independent radius written as r(1+t), the actual quadratic
coefficient remainder factors as r² times a family with uniform jets. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def actualRelativeCoefficientInput (r : ℝ) (p : FramedRadialParameter dim) :
    FramedRadialParameter dim :=
  ((p.1.1,r*(1+p.1.2)),p.2)

@[expose] def actualRelativeCoefficientFirst (d : Data dim) (p : FramedRadialParameter dim) : Mat dim :=
  (1+p.1.2) • actualFramedCoefficientFirst d p

@[expose] def actualRelativeCoefficientRemainder (d : Data dim) (r : ℝ)
    (p : FramedRadialParameter dim) : Mat dim :=
  (1+p.1.2)^2 • actualFramedCoefficientRadialRemainder d (actualRelativeCoefficientInput r p)

theorem uniform_actual_relativeCoefficient_factorization (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C₁ C₂ : ℝ, 0 < η ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      (∀ y ∈ Y, ∀ z ∈ closedBall (0:X dim) L,
        LocalSmoothJetBudget (actualRelativeCoefficientFirst d) ((y,0),z) N C₁ ∧
          LocalSmoothJetBudget (actualRelativeCoefficientRemainder d (d.radius y)) ((y,0),z) N C₂) ∧
      (∀ (r : ℝ) (p : FramedRadialParameter dim), p.1.1 ∈ Y → p.2 ∈ closedBall (0:X dim) L →
        |r*(1+p.1.2)| ≤ 2*d.radius p.1.1 →
        actualFramedCoefficientField d (actualRelativeCoefficientInput r p) =
          1+r • actualRelativeCoefficientFirst d p+r^2 • actualRelativeCoefficientRemainder d r p) := by
  let P := FramedRadialParameter dim
  let Z : Set P := (closure Y ×ˢ {(0:ℝ)}) ×ˢ closedBall (0:X dim) L
  let R : ℝ × P → P := fun q => actualRelativeCoefficientInput q.1 q.2
  let τ (p : P) := 1+p.1.2
  let τ₂ (p : P) := (1+p.1.2)^2
  let J := Icc (0:ℝ) 1 ×ˢ Z
  have hZ : IsCompact Z := (hYc.prod isCompact_singleton).prod (isCompact_closedBall _ _)
  have hJ : IsCompact J := isCompact_Icc.prod hZ
  have hτ : ContDiff ℝ ∞ τ := contDiff_const.add contDiff_fst.snd
  have hτ₂ : ContDiff ℝ ∞ τ₂ := hτ.pow 2
  have hR : ContDiff ℝ ∞ R :=
    (contDiff_snd.fst.fst.prodMk (contDiff_fst.mul (contDiff_const.add contDiff_snd.fst.snd))).prodMk contDiff_snd.snd
  obtain ⟨Cτ,hCτ,hτj⟩ := exists_uniform_finite_jet_bound hZ hτ N
  obtain ⟨Cτ₂,hCτ₂,hτ₂j⟩ := exists_uniform_finite_jet_bound hZ hτ₂ N
  obtain ⟨D,hD,hRj⟩ := exists_uniform_finite_jet_bound hJ hR N
  obtain ⟨η₁,F₁,hη₁,hF₁,hFirst⟩ := uniform_actual_framedCoefficient_first_jets
    hn hY hΩ hYc N (by omega) K ρ c₀ M Cj hK hρ L
  obtain ⟨η₂,F₂,hη₂,hF₂,hSecond⟩ := uniform_actual_framedCoefficient_radialRemainder
    hn hY hΩ hYc N hm K ρ c₀ M Cj hK hρ L hL
  let Smul : ℝ →L[ℝ] Mat dim →L[ℝ] Mat dim := ContinuousLinearMap.lsmul ℝ ℝ
  let C₁ := (2:ℝ)^N*‖Smul‖*Cτ*F₁
  let C₂ := (2:ℝ)^N*‖Smul‖*Cτ₂*(N.factorial*F₂*D^N)
  have hx : 0 ≤ (2:ℝ)^N*‖Smul‖ := by positivity
  have hC₁ : 0 ≤ C₁ := mul_nonneg (mul_nonneg hx (zero_le_one.trans hCτ)) hF₁
  have hC₂ : 0 ≤ C₂ := mul_nonneg (mul_nonneg hx (zero_le_one.trans hCτ₂))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hF₂) (pow_nonneg (zero_le_one.trans hD) _))
  refine ⟨min η₁ (min η₂ 1),C₁,C₂,lt_min hη₁ (lt_min hη₂ zero_lt_one),hC₁,hC₂,?_⟩
  intro floor hf ε hε hεη d hd hdFrame
  have hFirst' := hFirst floor hf ε hε (hεη.trans (min_le_left _ _)) d hd hdFrame
  have hSecond' := hSecond floor hf ε hε (hεη.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd hdFrame
  constructor
  · intro y hy z hz
    let p : P := ((y,0),z)
    let r := d.radius y
    have hr := (hd.2.2.2.2.1.2 y hy).1
    have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans (hd.2.2.2.2.2 y hy).2
    have hr₁ : r ≤ 1 := hrε.trans (hεη.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hpZ : p ∈ Z := ⟨⟨subset_closure hy,mem_singleton 0⟩,hz⟩
    have hrpJ : (r,p) ∈ J := ⟨⟨hr.le,hr₁⟩,hpZ⟩
    have hI : LocalSmoothJetBudget (actualRelativeCoefficientInput r) p N D :=
      ⟨(hR.comp (contDiff_const.prodMk contDiff_id)).contDiffAt,fun j hj =>
        (norm_iteratedFDeriv_slice_right_le hR r p j).trans (hRj (r,p) hrpJ j hj)⟩
    have hT : LocalSmoothJetBudget τ p N Cτ := ⟨hτ.contDiffAt,hτj p hpZ⟩
    have hT₂ : LocalSmoothJetBudget τ₂ p N Cτ₂ := ⟨hτ₂.contDiffAt,hτ₂j p hpZ⟩
    have h0 : (0:ℝ) ∈ Icc (-1:ℝ) 1 := by constructor <;> norm_num
    have hB₁ := hFirst' y hy 0 h0 z hz
    have hR₂ := (hSecond' y hy r (by rw [abs_of_pos hr]; linarith) z hz).1
    have hIp : actualRelativeCoefficientInput r p = ((y,r),z) := by simp only [actualRelativeCoefficientInput,p,add_zero,mul_one]
    have hB₂ : LocalSmoothJetBudget (actualFramedCoefficientRadialRemainder d)
        (actualRelativeCoefficientInput r p) N F₂ := by rwa [hIp]
    exact ⟨hT.bilinear hB₁ Smul,hT₂.bilinear (hI.comp hB₂ hD) Smul⟩
  · intro r p hy hz hs
    have h := (hSecond' p.1.1 hy (r*(1+p.1.2)) hs p.2 hz).2
    rw [show actualRelativeCoefficientInput r p = ((p.1.1,r*(1+p.1.2)),p.2) from rfl,h]
    simp only [actualRelativeCoefficientFirst,actualRelativeCoefficientRemainder,actualFramedCoefficientFirst,
      smul_smul,mul_pow,mul_assoc,actualRelativeCoefficientInput]

end CalderonN
