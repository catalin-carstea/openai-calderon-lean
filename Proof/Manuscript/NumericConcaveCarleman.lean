module

public import Proof.Manuscript.ScalarLowerOrderCarleman
public import Proof.Manuscript.ScalarFamilyBounds
public import Proof.CalderonN.ExponentialBalancing

import all Proof.CalderonN.StrictMetricWeight
import Proof.CalderonN.StrictParametricEstimate
import Proof.CalderonN.StrictPointShift
import Proof.CalderonN.ConcaveMetricWeight
import Proof.CalderonN.CarlemanIdentity
import Proof.CalderonN.DilationConnection
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric MeasureTheory CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

open CalderonN.Carleman.Strict
open CalderonN.Carleman (Mgrad quad pd Lop divV)
open CalderonN.Elliptic (strictHeight)
open CalderonN.Elliptic.Strict (JointSmooth jointSmooth_pd jointSmooth_add jointSmooth_mul
  jointSmooth_sum jointSmooth_divV jointSmooth_Lop jointSmooth_slice)

private abbrev Coeff (n : ℕ) := I n → I n → X n → ℝ

private def tangentialForm (a : Coeff n) (φ : X n → ℝ) (m : ℝ) (x : X n) (ξ : I n → ℝ) :=
  Mgrad a (phaseField a φ) x ξ + 4*m*quad a x ξ

private def phaseLinear (a : Coeff n) (φ : X n → ℝ) (x : X n) (ξ : I n → ℝ) :=
  ∑ j, phaseField a φ j x * ξ j

private def normalForm (a : Coeff n) (φ : X n → ℝ) (m : ℝ) (x : X n) :=
  2 * ∑ j, phaseField a φ j x * pd j (phaseNorm a φ) x - 4*m*phaseNorm a φ x

private def fullTangentialForm (a : Coeff n) (φ : X n → ℝ) (m D : ℝ)
    (x : X n) (ξ : I n → ℝ) :=
  tangentialForm a φ m x ξ + D*(phaseLinear a φ x ξ)^2

private theorem tangentialForm_smul (a : Coeff n) (φ : X n → ℝ) (m : ℝ)
    (x : X n) (c : ℝ) (ξ : I n → ℝ) :
    tangentialForm a φ m x (c • ξ) = c^2 * tangentialForm a φ m x ξ := by
  unfold tangentialForm
  rw [Mgrad_smul,quad_smul]
  ring

private theorem phaseLinear_smul (a : Coeff n) (φ : X n → ℝ) (x : X n)
    (c : ℝ) (ξ : I n → ℝ) : phaseLinear a φ x (c • ξ) = c * phaseLinear a φ x ξ :=
  lin_smul _ _ _ _

private theorem fullTangentialForm_smul (a : Coeff n) (φ : X n → ℝ) (m D : ℝ)
    (x : X n) (c : ℝ) (ξ : I n → ℝ) :
    fullTangentialForm a φ m D x (c • ξ) = c^2 * fullTangentialForm a φ m D x ξ := by
  unfold fullTangentialForm
  rw [tangentialForm_smul,phaseLinear_smul]
  ring

/-- Continuity of the four expressions used by the release's unchanged
phase estimate. It is joint in any chosen smooth coefficient family. -/
private theorem continuous_strictCarlemanData {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P → Coeff n) (φ : P → X n → ℝ) (ha : ∀ i j, JointSmooth fun p => a p i j)
    (hφ : JointSmooth φ) (m : ℝ) :
    Continuous (fun q : (P × X n) × (I n → ℝ) => tangentialForm (a q.1.1) (φ q.1.1) m q.1.2 q.2) ∧
    Continuous (fun q : (P × X n) × (I n → ℝ) => phaseLinear (a q.1.1) (φ q.1.1) q.1.2 q.2) ∧
    Continuous (fun q : P × X n => normalForm (a q.1) (φ q.1) m q.2) ∧
    Continuous (fun q : P × X n => Lop (a q.1) (divV (phaseField (a q.1) (φ q.1))) q.2) ∧
    Continuous (fun q : P × X n => divV (phaseField (a q.1) (φ q.1)) q.2) := by
  let W : P → I n → X n → ℝ := fun p => phaseField (a p) (φ p)
  let N : P → X n → ℝ := fun p => phaseNorm (a p) (φ p)
  have hW : ∀ j, JointSmooth fun p => W p j := by
    intro j
    exact jointSmooth_sum (F := fun k p x => a p j k x * pd k (φ p) x)
      (fun k => jointSmooth_mul (ha j k) (jointSmooth_pd hφ k))
  have hN : JointSmooth N := by
    exact jointSmooth_sum (F := fun i p x => ∑ k, a p i k x * pd i (φ p) x * pd k (φ p) x)
      (fun i => jointSmooth_sum (F := fun k p x => a p i k x * pd i (φ p) x * pd k (φ p) x)
        (fun k => jointSmooth_mul (jointSmooth_mul (ha i k) (jointSmooth_pd hφ i)) (jointSmooth_pd hφ k)))
  have hA : Continuous (fun z : P × X n => fun i k => a z.1 i k z.2) :=
    continuous_pi fun i => continuous_pi fun k => (ha i k).continuous
  have hDW : Continuous (fun z : P × X n => fun i j => pd i (W z.1 j) z.2) :=
    continuous_pi fun i => continuous_pi fun j => (jointSmooth_pd (hW j) i).continuous
  have hDA : Continuous (fun z : P × X n => fun j i k => pd j (a z.1 i k) z.2) :=
    continuous_pi fun j => continuous_pi fun i => continuous_pi fun k => (jointSmooth_pd (ha i k) j).continuous
  have hWj : Continuous (fun z : P × X n => fun j => W z.1 j z.2) :=
    continuous_pi fun j => (hW j).continuous
  have hDiv : JointSmooth (fun p => divV (W p)) := jointSmooth_divV hW
  have hRes : Continuous (fun q : P × X n => Lop (a q.1) (divV (W q.1)) q.2) :=
    (jointSmooth_Lop ha hDiv).continuous
  refine ⟨?_,?_,?_,hRes,hDiv.continuous⟩
  · exact (continuous_E1_form hA hDW hDA hWj).add (continuous_const.mul (continuous_quad_form hA))
  · exact continuous_finsetSum _ fun j _ =>
      ((hW j).continuous.comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  · exact (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      (hW j).continuous.mul (jointSmooth_pd hN j).continuous)).sub (continuous_const.mul hN.continuous)

private theorem tangential_bound_of_sphere (a : Coeff n) (φ : X n → ℝ) (m D α : ℝ)
    (x : X n) (hUnit : ∀ ξ ∈ sphere (0 : I n → ℝ) 1,
      α * ∑ i, ξ i^2 ≤ fullTangentialForm a φ m D x ξ) :
    ∀ ξ : I n → ℝ, α * ∑ i, ξ i^2 ≤ fullTangentialForm a φ m D x ξ := by
  intro ξ
  by_cases hξ : ξ = 0
  · simp [hξ,fullTangentialForm,tangentialForm,phaseLinear, Mgrad,quad]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let u := ‖ξ‖⁻¹ • ξ
  have hu : u ∈ sphere (0 : I n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm]
    change ‖‖ξ‖⁻¹ • ξ‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have he : ξ = ‖ξ‖ • u := by unfold u; rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
  rw [he,fullTangentialForm_smul]
  simp only [Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
  rw [mul_left_comm α]
  exact mul_le_mul_of_nonneg_left (hUnit u hu) (sq_nonneg _)

omit [NeZero n] in
private theorem numeric_principal_carleman (a : Coeff n) (φ : X n → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hsym : ∀ i j, a i j = a j i) (hφ : ContDiff ℝ ∞ φ)
    (K : Set (X n)) (m α β D R₀ d₀ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hD : 0 ≤ D)
    (hTang : ∀ x ∈ K, ∀ ξ : I n → ℝ, α * ∑ i, ξ i^2 ≤ fullTangentialForm a φ m D x ξ)
    (hNor : ∀ x ∈ K, β ≤ normalForm a φ m x)
    (hR : ∀ x ∈ K, |Lop a (divV (phaseField a φ)) x| ≤ R₀)
    (hd : ∀ x ∈ K, |divV (phaseField a φ) x| ≤ d₀)
    (τ : ℝ) (hτ : max (max 1 D) (max (32*m^2/β) (4*(R₀+D*d₀^2/2)/β)) ≤ τ)
    (w : X n → ℝ) (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) (hK : tsupport w ⊆ K) :
    τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ φ w) x ^ 2) +
        τ^3 * (∫ x, (weightedFunction τ φ w x)^2) ≤
      (1/min α (β/2)) * (∫ x, (weightedFunction τ φ (Elliptic.Lop a w) x)^2) := by
  let T := max (max 1 D) (max (32*m^2/β) (4*(R₀+D*d₀^2/2)/β))
  have hτ₁ : 1 ≤ τ := ((le_max_left 1 D).trans (le_max_left _ _)).trans hτ
  have hτD : D ≤ τ := ((le_max_right 1 D).trans (le_max_left _ _)).trans hτ
  have hτM : 32*m^2 ≤ β*τ := by
    have h : 32*m^2/β ≤ T := (le_max_left _ _).trans (le_max_right _ _)
    have hh := (div_le_iff₀ hβ).mp (h.trans hτ)
    linarith
  have hτR : 4*(R₀+D*d₀^2/2) ≤ β*τ := by
    have h : 4*(R₀+D*d₀^2/2)/β ≤ T := (le_max_right _ _).trans (le_max_right _ _)
    have hh := (div_le_iff₀ hβ).mp (h.trans hτ)
    linarith
  have h := unchanged_phase_estimate_of_coefficient_bounds ha hsym hφ hw hwc K hK
    m α β D R₀ d₀ hβ hD hTang hNor hR hd τ hτ₁ hτD hτM hτR
  let c := min α (β/2)
  have hc : 0 < c := lt_min hα (half_pos hβ)
  have hG0 : 0 ≤ ∫ x, ∑ i, pd i (fun y => Real.exp (τ * φ y) * w y) x ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hV0 : 0 ≤ ∫ x, (Real.exp (τ * φ x) * w x)^2 := integral_nonneg fun x => sq_nonneg _
  have hτ0 : 0 ≤ τ := zero_le_one.trans hτ₁
  have hLeft := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left α (β/2)) hτ0) hG0
  have hRight := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_right α (β/2)) (pow_nonneg hτ0 3)) hV0
  have he (x : X n) : Real.exp (2 * (τ * φ x)) * Lop a w x ^ 2 =
      (weightedFunction τ φ (Elliptic.Lop a w) x)^2 := by
    unfold weightedFunction
    rw [mul_pow,pow_two (Real.exp _),← Real.exp_add]
    change Real.exp (2 * (τ * φ x)) * Lop a w x ^ 2 =
      Real.exp (τ * φ x + τ * φ x) * Lop a w x ^ 2
    rw [two_mul]
  simp only [he] at h
  change _ ≤ (1/c) * _
  rw [div_mul_eq_mul_div,one_mul,le_div_iff₀ hc]
  change ((τ * (∫ x, ∑ i, pd i (fun y => Real.exp (τ * φ y) * w y) x ^ 2) +
     τ ^ 3 * (∫ x, (Real.exp (τ * φ x) * w x)^2)) * c) ≤ _
  linarith only [hLeft,hRight,h]


private theorem reference_le_eventually {Y : Type*} [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) {b : Y → ℝ} {G : ℝ × Y → ℝ}
    (hb : Continuous b) (hG : Continuous G) (href : ∀ x ∈ K, b x < G (0,x)) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ K, b x ≤ G (t,x) := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hc : Continuous (fun q : ℝ × Y => G q - b q.2) :=
    hG.sub (hb.comp continuous_snd)
  have hev : ∀ᶠ q : ℝ × Y in 𝓝 ((0 : ℝ),x), 0 < G q - b q.2 :=
    hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (sub_pos.mpr (href x hx)))
  exact hev.mono fun _ h => (sub_pos.mp h).le

private theorem reference_abs_eventually {Y : Type*} [TopologicalSpace Y] {K : Set Y}
    (hK : IsCompact K) {G : ℝ × Y → ℝ} (hG : Continuous G)
    {C : ℝ} (href : ∀ x ∈ K, |G (0,x)| < C) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ K, |G (t,x)| ≤ C := by
  have h := reference_le_eventually hK (continuous_const (y := -C)) hG.abs.neg
    (fun x hx => neg_lt_neg (href x hx))
  exact h.mono fun _ h x hx => neg_le_neg_iff.mp (h x hx)

set_option maxHeartbeats 4400000 in
/-- Fixed-reference principal Carleman data. The spatial radius, all
energy constants, and the concavity range are chosen before the operator
path, including when the path changes the higher spatial jets. -/
theorem exists_reference_concave_principalCarleman {L₀ : ScalarElliptic n} (hL₀ : L₀.SmoothOn univ)
    {θ : X n → ℝ} (hθ : ContDiff ℝ ∞ θ) (x₀ : X n) (hs : StrictMetricWeightAt L₀.metric θ x₀) :
    ∃ r C τ₀ : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ₀ ∧
      ∀ (L : ℝ → ScalarElliptic n), SmoothFamilyOn L univ → L 0 = L₀ →
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ κ : ℝ, |κ| ≤ r → ∀ τ : ℝ, τ₀ ≤ τ →
        ∀ w : X n → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall x₀ r →
        let φ := fun x => strictHeight κ (θ x)
        τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ φ w) x ^ 2) +
          τ^3 * (∫ x, (weightedFunction τ φ w x)^2) ≤
          C * ∫ x, (weightedFunction τ φ
            (Elliptic.Lop (fun i j y => divergenceCoeff (L t).metric y i j) w) x)^2 := by
  let A₀ : Coeff n := fun i j x => divergenceCoeff L₀.metric x i j
  have hA₀ (i j : I n) : ContDiff ℝ ∞ (A₀ i j) :=
    contDiffOn_univ.mp (contDiffOn_divergenceCoeff hL₀.1 i j)
  have hSym₀ (i j : I n) : A₀ i j = A₀ j i :=
    funext fun x => divergenceCoeff_symm hL₀.1 (mem_univ x) i j
  have hPoint := point_strictness_chart hL₀.1 hθ hs
  obtain ⟨m,hTan₀,hNor₀⟩ := exists_signed_shift_of_point_strictness A₀ hA₀ hSym₀ hθ x₀
    hPoint.1 hPoint.2
  let ψ (κ : ℝ) (x : X n) := strictHeight κ (θ x)
  have hψ : JointSmooth ψ :=
    (hθ.comp contDiff_snd).sub (contDiff_fst.mul ((hθ.comp contDiff_snd).pow 2))
  have hψ₀ : ψ 0 = θ := by funext x; simp [ψ,strictHeight]
  have hRefData := continuous_strictCarlemanData (fun _ : ℝ => A₀) ψ
    (fun i j => (hA₀ i j).comp contDiff_snd) hψ m
  obtain ⟨D,α,hD,hα,hRank⟩ := uniform_rank_one_coercivity_on_compact_parameter_space
    (isCompact_singleton (x := ((0 : ℝ),x₀)))
    (fun q ξ => tangentialForm A₀ (ψ q.1) m q.2 ξ)
    (fun q ξ => phaseLinear A₀ (ψ q.1) q.2 ξ) hRefData.1 hRefData.2.1
    (fun q c ξ => tangentialForm_smul _ _ _ _ _ _)
    (fun q c ξ => phaseLinear_smul _ _ _ _ _)
    (fun q hq ξ hξ hker => by
      rw [mem_singleton_iff.mp hq,hψ₀] at hker ⊢
      exact hTan₀ ξ hξ hker)
  let S := sphere (0 : I n → ℝ) 1
  have hS : IsCompact S := isCompact_sphere _ _
  let β := normalForm A₀ θ m x₀
  have hβ : 0 < β := hNor₀
  have hRForm : Continuous (fun q : (ℝ × X n) × (I n → ℝ) =>
      fullTangentialForm A₀ (ψ q.1.1) m D q.1.2 q.2) :=
    hRefData.1.add (continuous_const.mul (hRefData.2.1.pow 2))
  have hPos : ∀ᶠ q : ℝ × X n in 𝓝 ((0 : ℝ),x₀), ∀ ξ ∈ S,
      α/2 * ∑ i, ξ i^2 < fullTangentialForm A₀ (ψ q.1) m D q.2 ξ := by
    apply hS.eventually_forall_of_forall_eventually
    intro ξ hξ
    have hξ0 : ξ ≠ 0 := by
      intro h
      have hn := mem_sphere_zero_iff_norm.mp hξ
      rw [h,norm_zero] at hn
      exact zero_ne_one hn
    have hlt : α/2 * ∑ i, ξ i^2 < α * ∑ i, ξ i^2 :=
      mul_lt_mul_of_pos_right (half_lt_self hα) (sum_sq_pos_of_ne_zero hξ0)
    have hCenter := hlt.trans_le (hRank (0,x₀) (mem_singleton _) ξ)
    have hC : Continuous (fun q : (ℝ × X n) × (I n → ℝ) =>
        fullTangentialForm A₀ (ψ q.1.1) m D q.1.2 q.2 - α/2 * ∑ i, q.2 i^2) :=
      hRForm.sub (by fun_prop)
    have he : ∀ᶠ q : (ℝ × X n) × (I n → ℝ) in 𝓝 (((0 : ℝ),x₀),ξ),
        0 < fullTangentialForm A₀ (ψ q.1.1) m D q.1.2 q.2 - α/2 * ∑ i, q.2 i^2 :=
      hC.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (sub_pos.mpr hCenter))
    exact he.mono fun _ h => sub_pos.mp h
  have hNPos : ∀ᶠ q : ℝ × X n in 𝓝 ((0 : ℝ),x₀), β/2 < normalForm A₀ (ψ q.1) m q.2 :=
    hRefData.2.2.1.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by simpa only [hψ₀] using (half_lt_self hβ)))
  obtain ⟨r₀,hr₀,hroom⟩ := Metric.eventually_nhds_iff.mp (hPos.and hNPos)
  let r := r₀/2
  have hr : 0 < r := half_pos hr₀
  let K := closedBall x₀ r
  let Q := closedBall (0 : ℝ) r ×ˢ K
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hQ' (q : ℝ × X n) (hq : q ∈ Q) : dist q (0,x₀) < r₀ := by
    rw [Prod.dist_eq]
    exact (max_le (mem_closedBall.mp hq.1) (mem_closedBall.mp hq.2)).trans_lt (half_lt_self hr₀)
  obtain ⟨AA,hAA⟩ := hQ.exists_bound_of_continuousOn hRefData.2.2.2.1.continuousOn
  obtain ⟨BB,hBB⟩ := hQ.exists_bound_of_continuousOn hRefData.2.2.2.2.continuousOn
  let R₀ := max AA 0 + 1
  let d₀ := max BB 0 + 1
  let β' := β/2
  let α' := α/2
  have hβ' : 0 < β' := half_pos hβ
  have hα' : 0 < α' := half_pos hα
  let τ₀ := max (max 1 D) (max (32 * m^2 / β') (4*(R₀+D*d₀^2/2)/β'))
  let C := 1 / min α' (β'/2)
  have hC : 0 < C := one_div_pos.mpr (lt_min hα' (half_pos hβ'))
  refine ⟨r,C,τ₀,hr,hC,(le_max_left _ _).trans (le_max_left _ _),fun L hL he => ?_⟩
  let a (p : ℝ × ℝ) : Coeff n := fun i j x => divergenceCoeff (L p.1).metric x i j
  let φ (p : ℝ × ℝ) := ψ p.2
  have ha (i j : I n) : JointSmooth (fun p => a p i j) :=
    (hL.contDiff_divergence_univ i j).comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hφ : JointSmooth φ := hψ.comp (contDiff_fst.snd.prodMk contDiff_snd)
  have hData := continuous_strictCarlemanData a φ ha hφ m
  let Cmb (z : ℝ × (ℝ × X n)) := ((z.1,z.2.1),z.2.2)
  have hCmb : Continuous Cmb := (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  have hTang := reference_le_eventually (hQ.prod hS)
    (b := fun q : (ℝ × X n) × (I n → ℝ) => α' * ∑ i, q.2 i^2) (by fun_prop)
    ((hData.1.add (continuous_const.mul (hData.2.1.pow 2))).comp
      ((hCmb.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd))
    (fun q hq => by
      change α' * ∑ i, q.2 i^2 < fullTangentialForm (a (0,q.1.1)) (ψ q.1.1) m D q.1.2 q.2
      have hae : a (0,q.1.1) = A₀ := by simp [a,A₀,he]
      rw [hae]
      exact (hroom (hQ' q.1 hq.1)).1 q.2 hq.2)
  have hNormal := reference_le_eventually hQ (continuous_const (y := β'))
    (hData.2.2.1.comp hCmb) (fun q hq => by
      change β' < normalForm (a (0,q.1)) (ψ q.1) m q.2
      have hae : a (0,q.1) = A₀ := by simp [a,A₀,he]
      rw [hae]
      exact (hroom (hQ' q hq)).2)
  have hResidual := reference_abs_eventually hQ (hData.2.2.2.1.comp hCmb) (C := R₀)
    (fun q hq => by
      change |Lop (a (0,q.1)) (divV (phaseField (a (0,q.1)) (ψ q.1))) q.2| < R₀
      have hae : a (0,q.1) = A₀ := by simp [a,A₀,he]
      rw [hae,← Real.norm_eq_abs]
      exact ((hAA q hq).trans (le_max_left _ _)).trans_lt (lt_add_one _))
  have hDiverg := reference_abs_eventually hQ (hData.2.2.2.2.comp hCmb) (C := d₀)
    (fun q hq => by
      change |divV (phaseField (a (0,q.1)) (ψ q.1)) q.2| < d₀
      have hae : a (0,q.1) = A₀ := by simp [a,A₀,he]
      rw [hae,← Real.norm_eq_abs]
      exact ((hBB q hq).trans (le_max_left _ _)).trans_lt (lt_add_one _))
  filter_upwards [hTang,hNormal,hResidual,hDiverg] with t ht hn hR hd κ hκ τ hτ w hw hwc hwK
  have hκ' : κ ∈ closedBall (0 : ℝ) r := by simpa [mem_closedBall_zero_iff,Real.norm_eq_abs] using hκ
  have hP (x : X n) (hx : x ∈ K) : (κ,x) ∈ Q := ⟨hκ',hx⟩
  have hsym (i j : I n) : a (t,κ) i j = a (t,κ) j i :=
    funext fun x => divergenceCoeff_symm (hL.1 t).1 (mem_univ x) i j
  exact numeric_principal_carleman (a (t,κ)) (ψ κ)
    (fun i j => jointSmooth_slice (ha i j) (t,κ)) hsym (jointSmooth_slice hψ κ)
    K m α' β' D R₀ d₀ hα' hβ' hD
    (fun x hx => tangential_bound_of_sphere (a (t,κ)) (ψ κ) m D α' x
      (fun ξ hξ => ht ((κ,x),ξ) ⟨hP x hx,hξ⟩))
    (fun x hx => hn (κ,x) (hP x hx)) (fun x hx => hR (κ,x) (hP x hx))
    (fun x hx => hd (κ,x) (hP x hx)) τ hτ w hw hwc hwK


theorem SmoothFamilyOn.contDiff_weightedDrift_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) (k : I n) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => (L q.1).weightedDrift k q.2) := by
  have hChr (i j : I n) : ContDiff ℝ ∞ (fun q : ℝ × X n => christoffel (L q.1).metric q.2 k i j) :=
    contDiffOn_univ.mp (contDiffOn_christoffel_slice isOpen_univ
      (g := fun q : ℝ × X n => (L q.1).metric q.2) (fun i j => (hL.2.1 i j).mono (by simp))
      (fun q _ => (hL.1 q.1).1.2 q.2 (mem_univ _)) k i j)
  exact hL.contDiff_chartVolume_univ.mul ((hL.contDiff_first_univ k).add
    (ContDiff.sum fun i _ => ContDiff.sum fun j _ => (hL.contDiff_principal_univ i j).mul (hChr i j)))

theorem SmoothFamilyOn.contDiff_weightedPotential_univ {L : ℝ → ScalarElliptic n}
    (hL : SmoothFamilyOn L univ) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => (L q.1).weightedPotential q.2) :=
  hL.contDiff_chartVolume_univ.mul hL.contDiff_zeroth_univ

set_option maxHeartbeats 2500000 in
/-- The fixed-reference concave Carleman estimate for the full scalar
operator, with lower drift and potential absorbed at a common threshold. -/
theorem exists_reference_concave_scalarCarleman {L₀ : ScalarElliptic n} (hL₀ : L₀.SmoothOn univ)
    {θ : X n → ℝ} (hθ : ContDiff ℝ ∞ θ) (x₀ : X n) (hs : StrictMetricWeightAt L₀.metric θ x₀) :
    ∃ r C τ₀ : ℝ, 0 < r ∧ 0 < C ∧ 1 ≤ τ₀ ∧
      ∀ (L : ℝ → ScalarElliptic n), SmoothFamilyOn L univ → L 0 = L₀ →
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ κ : ℝ, |κ| ≤ r → ∀ τ : ℝ, τ₀ ≤ τ →
        ∀ w : X n → ℝ, ContDiff ℝ ∞ w → HasCompactSupport w → tsupport w ⊆ closedBall x₀ r →
        let φ := fun x => strictHeight κ (θ x)
        τ * (∫ x, ∑ i, coordDeriv i (weightedFunction τ φ w) x ^ 2) +
          τ^3 * (∫ x, (weightedFunction τ φ w x)^2) ≤
          C * ∫ x, (weightedFunction τ φ
            (fun y => chartVolume (L t).metric y * (L t).apply w y) x)^2 := by
  obtain ⟨r,C₀,T₀,hr,hC₀,hT₀,hP⟩ := exists_reference_concave_principalCarleman hL₀ hθ x₀ hs
  let K := closedBall x₀ r
  have hK : IsCompact K := isCompact_closedBall _ _
  let Q := closedBall (0 : ℝ) r ×ˢ K
  have hQ : IsCompact Q := (isCompact_closedBall _ _).prod hK
  let ψ (κ : ℝ) (x : X n) := strictHeight κ (θ x)
  have hψ : JointSmooth ψ :=
    (hθ.comp contDiff_snd).sub (contDiff_fst.mul ((hθ.comp contDiff_snd).pow 2))
  choose A hA using (fun i : I n => hQ.exists_bound_of_continuousOn
    (jointSmooth_pd hψ i).continuous.continuousOn)
  let M := ∑ i, max (A i) 0
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => le_max_right _ _
  have hPhase (κ : ℝ) (hκ : |κ| ≤ r) (x : X n) (hx : x ∈ K) (i : I n) :
      |coordDeriv i (ψ κ) x| ≤ M := by
    have hκ' : κ ∈ closedBall (0 : ℝ) r := by simpa [mem_closedBall_zero_iff,Real.norm_eq_abs] using hκ
    exact ((hA i (κ,x) ⟨hκ',hx⟩).trans (le_max_left _ _)).trans
      (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i))
  let J := I n ⊕ Unit
  let F (L : ScalarElliptic n) (j : J) : X n → ℝ :=
    Sum.elim (fun i => L.weightedDrift i) (fun _ => L.weightedPotential) j
  have hF (L : ℝ → ScalarElliptic n) (hL : SmoothFamilyOn L univ) (j : J) :
      ContDiff ℝ ∞ (fun q : ℝ × X n => F (L q.1) j q.2) := by
    cases j with
    | inl i => exact hL.contDiff_weightedDrift_univ i
    | inr _ => exact hL.contDiff_weightedPotential_univ
  have hF₀ (j : J) : ContDiff ℝ ∞ (F L₀ j) := by
    have hj := hF (fun _ => L₀) (smoothFamilyOn_const hL₀) j
    exact hj.comp (contDiff_const (c := (0 : ℝ)) |>.prodMk
      (contDiff_id : ContDiff ℝ ∞ (id : X n → X n)))
  obtain ⟨B,hB,hBbound⟩ := exists_reference_spatial_jet_bounds hK hF₀ 0
  let T := max T₀ (4*C₀*(2*(n:ℝ)*B^2 + 2*(B+(n:ℝ)*B*M)^2))
  refine ⟨r,4*C₀,T,hr,by positivity,hT₀.trans (le_max_left _ _),fun L hL he => ?_⟩
  have hBpath := hBbound (fun j q => F (L q.1) j q.2) (hF L hL)
    (fun j => by change (fun x => F (L 0) j x) = F L₀ j; rw [he])
  filter_upwards [hP L hL he,hBpath] with t ht hLow κ hκ τ hτ w hw hwc hwK
  let a (i j : I n) (x : X n) := divergenceCoeff (L t).metric x i j
  let b := (L t).weightedDrift
  let c := (L t).weightedPotential
  have hb (x : X n) (hx : x ∈ K) (i : I n) : |b i x| ≤ B := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,F,Sum.elim_inl,b] using hLow x hx (Sum.inl i) 0 le_rfl
  have hc (x : X n) (hx : x ∈ K) : |c x| ≤ B := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,F,Sum.elim_inr,c] using hLow x hx (Sum.inr ()) 0 le_rfl
  have hBs (i : I n) : Continuous (b i) :=
    (jointSmooth_slice (F := fun t => (L t).weightedDrift i) (hL.contDiff_weightedDrift_univ i) t).continuous
  have hCs : Continuous c :=
    (jointSmooth_slice (F := fun t => (L t).weightedPotential) hL.contDiff_weightedPotential_univ t).continuous
  have ha (i j : I n) : ContDiff ℝ ∞ (a i j) :=
    jointSmooth_slice (F := fun t x => divergenceCoeff (L t).metric x i j) (hL.contDiff_divergence_univ i j) t
  have hτ₀ : T₀ ≤ τ := (le_max_left _ _).trans hτ
  have hLarge : 4*C₀*(2*(n:ℝ)*B^2 + 2*(B+(n:ℝ)*B*M)^2) ≤ τ :=
    (le_max_right _ _).trans hτ
  have hMain := carleman_with_lowerOrder ha (jointSmooth_slice hψ κ) hw hwc hwK
    (hT₀.trans hτ₀) hB.le hB.le hM hC₀.le hBs hCs hb hc (hPhase κ hκ) hLarge
    (ht κ hκ τ hτ₀ w hw hwc hwK)
  have hEq (x : X n) :
      Elliptic.Lop a w x + lowerOrder b c w x = chartVolume (L t).metric x * (L t).apply w x :=
    (volume_mul_apply_eq isOpen_univ (hL.1 t) hw.contDiffOn (mem_univ x)).symm
  simpa only [weightedFunction,hEq] using hMain

end CalderonPaper.ScalarElliptic
