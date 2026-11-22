module

public import Proof.CalderonN.DilationHarmonic

public import Proof.CalderonN.DilationConnection
import Proof.CalderonN.PrincipalMetric
import Proof.CalderonN.Hessian
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.MetricRecovery
import Proof.CalderonN.MetricJetBound
import Proof.CalderonN.NormalizedMetric
import Proof.CalderonN.SliceJets
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity

public section

noncomputable section
open Matrix Set Filter
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 1500000

private theorem hessian_spans_pos_smul {n : ℕ} {g : (MetricField dim)} {u : Fin n → (X dim) → ℝ}
    (hspan : HessianSpanning g u) (hpos : (g 0).PosDef) {s : ℝ} (hs : 0 < s) (H : (Mat dim)) :
    H ∈ Submodule.span ℝ (Set.range fun a => hessian (u a) 0) ↔
      H.transpose = H ∧ (((s • g 0)⁻¹ : (Mat dim)) * H).trace = 0 := by
  let c : ℝˣ := Units.mk0 s hs.ne'
  have hinv : (s • g 0)⁻¹ = s⁻¹ • (g 0)⁻¹ :=
    Matrix.inv_smul' _ c (isUnit_iff_ne_zero.mpr hpos.det_pos.ne')
  rw [hinv, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_eq_zero,
    or_iff_right (inv_ne_zero hs.ne')]
  exact hspan H

/-- The uniform Hessian inversion in Section 6.1. Its constant is chosen
before the final positive spatial dilation and works for every radius
parameter once the paired order-ten derivative bound has been obtained. -/
theorem exists_uniform_normalized_metric_jet_recovery
    {Ω K : Set (X dim)} (hΩ : IsOpen Ω) (h₀ : (0 : (X dim)) ∈ Ω) (hK : IsCompact K)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω g₁) (hg₂ : SmoothMetric Ω g₂)
    (hchart₁ : HarmonicCoordinates Ω g₁) (hchart₂ : HarmonicCoordinates Ω g₂)
    {n : ℕ} {u₁ u₂ : Fin n → (X dim) → ℝ}
    (hu₁ : ∀ a, Harmonic Ω g₁ (u₁ a)) (hu₂ : ∀ a, Harmonic Ω g₂ (u₂ a))
    (hspan : HessianSpanning g₁ u₁) {σ : (X dim) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hσpos : ∀ y, 0 < σ y) :
    let V := fun (lam : ℝ) (a : Fin n) (y : (X dim)) =>
      renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₂ a) lam y -
      renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₁ a) lam y
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ lam in 𝓝 (0 : ℝ), lam ≠ 0 → ∀ y ∈ K, lam • y ∈ Ω ∧
      ∀ B : ℝ, 0 ≤ B → (∀ a d, d ≤ 10 → ‖iteratedFDeriv ℝ d (V lam a) y‖ ≤ B) →
        smallJet (conformalReference σ g₁ lam) (dilatedMetric g₂ lam) y ≤ C * B := by
  let U₀ : Set (ℝ × (X dim)) := {q | q.1 • q.2 ∈ Ω}
  let γ (q : ℝ × (X dim)) := conformalReference σ g₁ q.1 q.2
  let g (q : ℝ × (X dim)) := dilatedMetric g₂ q.1 q.2
  let Q (q : ℝ × (X dim)) := principal (conformalReference σ g₁ q.1) (dilatedMetric g₂ q.1) q.2
  let H (q : ℝ × (X dim)) (a : Fin n) := hessian (u₁ a) (q.1 • q.2)
  let A (q : ℝ × (X dim)) := metricSystemMatrix (γ q) (H q)
  let D (q : ℝ × (X dim)) := ((A q).transpose * A q).det
  let U := U₀ ∩ {q : ℝ × (X dim) | D q ≠ 0}
  have hU₀ : IsOpen U₀ := hΩ.preimage (continuous_fst.smul continuous_snd)
  have hmap : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => q.1 • q.2) := contDiff_fst.smul contDiff_snd
  have hγ (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => γ q i j) U₀ :=
    (hσ.comp contDiff_snd).contDiffOn.mul ((hg₁.1 i j).comp hmap.contDiffOn (fun _ hq => hq))
  have hg (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => g q i j) U₀ :=
    (hg₂.1 i j).comp hmap.contDiffOn (fun _ hq => hq)
  have hγpos (q : ℝ × (X dim)) (hq : q ∈ U₀) : (γ q).PosDef :=
    (hg₁.2 _ hq).smul (hσpos q.2)
  have hgpos (q : ℝ × (X dim)) (hq : q ∈ U₀) : (g q).PosDef := hg₂.2 _ hq
  have hQ (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => Q q i j) U₀ :=
    contDiffOn_normalized_inv_entry_of_entries hγ hg hγpos hgpos i j
  have hH (a : Fin n) (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => H q a i j) U₀ :=
    (contDiffOn_coordDeriv (contDiffOn_coordDeriv (hu₁ a).1 hΩ j) hΩ i).comp
      hmap.contDiffOn (fun _ hq => hq)
  have hA := contDiffOn_metricSystemMatrix_entries hγ hH
  have hD : ContinuousOn D U₀ := (contDiffOn_det_of_entries (contDiffOn_gram_entry hA)).continuousOn
  have hU : IsOpen U := by
    have ho : IsOpen ({0}ᶜ : Set ℝ) := isOpen_compl_singleton
    exact hD.isOpen_inter_preimage hU₀ ho
  have hzero (y : (X dim)) : ((0 : ℝ), y) ∈ U₀ := by
    change (0 : ℝ) • y ∈ Ω
    simpa using h₀
  have hUbase (y : (X dim)) (_ : y ∈ K) : ((0 : ℝ), y) ∈ U := by
    refine ⟨hzero y, ?_⟩
    have heγ : γ (0, y) = σ y • g₁ 0 := by simp [γ, conformalReference, dilatedMetric]
    have heH : H (0, y) = fun a => hessian (u₁ a) 0 := by simp [H]
    have hi : Function.Injective (A (0, y)).mulVec := by
      apply metricSystemMatrix_injective (hγpos _ (hzero y))
      rw [heγ, heH]
      exact hessian_spans_pos_smul hspan (hg₁.2 _ h₀) (hσpos y)
    exact (gram_posDef_of_mulVec_injective hi).det_pos.ne'
  let coeff (qv : ((I dim) × (I dim)) × (Fin n × (I dim) × (I dim))) (q : ℝ × (X dim)) :=
    hessianRecoveryCoeff (γ q) (Q q) (H q) qv.1 qv.2
  have hcoeff (qv : ((I dim) × (I dim)) × (Fin n × (I dim) × (I dim))) : ContDiffOn ℝ ∞ (coeff qv) U :=
    contDiffOn_hessianRecoveryCoeff
      (fun i j => (hγ i j).mono inter_subset_left)
      (fun i j => (hQ i j).mono inter_subset_left)
      (fun a i j => (hH a i j).mono inter_subset_left)
      (fun _ hq => hq.2) qv.1 qv.2
  obtain ⟨C₀, hC₀, hjet⟩ := exists_uniform_slice_jet_bound hK hU hUbase hcoeff 8
  let C := max 1 ((dim : ℝ) * (9 : ℝ)^dim * Fintype.card (Fin n × (I dim) × (I dim)) * (2 : ℝ)^8 * C₀)
  refine ⟨C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  filter_upwards [hjet] with lam hlam hne y hy
  obtain ⟨hyU, hby⟩ := hlam y hy
  refine ⟨hyU.1, fun B hB hVjet => ?_⟩
  let T : Set (X dim) := {z | lam • z ∈ Ω}
  let S : Set (X dim) := {z | (lam, z) ∈ U}
  let v₁ (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₁ a) lam
  let v₂ (a : Fin n) := renormalizedHarmonic (u₁ a 0) (fderiv ℝ (u₁ a) 0) (u₂ a) lam
  let V (a : Fin n) (z : (X dim)) := v₂ a z - v₁ a z
  have hT : IsOpen T := hΩ.preimage ((lam • ContinuousLinearMap.id ℝ (X dim)).continuous)
  have hS : IsOpen S := hU.preimage (continuous_const.prodMk continuous_id)
  have hST : S ⊆ T := fun _ hz => hz.1
  have hs₁ := smoothMetric_dilated hg₁ lam
  have hs₂ := smoothMetric_dilated hg₂ lam
  have hc₁ := harmonicCoordinates_dilated hΩ hg₁ hchart₁ lam
  have hc₂ := harmonicCoordinates_dilated hΩ hg₂ hchart₂ lam
  have hv₁ (a : Fin n) : Harmonic T (dilatedMetric g₁ lam) (v₁ a) :=
    harmonic_renormalizedHarmonic hΩ hg₁ hchart₁ (hu₁ a) _ _ hne
  have hv₂ (a : Fin n) : Harmonic T (dilatedMetric g₂ lam) (v₂ a) :=
    harmonic_renormalizedHarmonic hΩ hg₂ hchart₂ (hu₂ a) _ _ hne
  have heq (q : (I dim) × (I dim)) :
      EqOn (fun z => (Q (lam, z) - (γ (lam, z))⁻¹) q.1 q.2)
        (fun z => ∑ v : Fin n × (I dim) × (I dim), coeff (q, v) (lam, z) *
          hessian (V v.1) z v.2.1 v.2.2) S := by
    intro z hz
    have hzT := hST hz
    have hn (a : Fin n) := normalized_metric_system hT hc₁ hc₂ (hv₁ a) (hv₂ a) hzT
      (hγpos _ hz.1) (hs₁.2 z hzT) (hs₂.2 z hzT) (hσpos z)
      (show γ (lam, z) = σ z • dilatedMetric g₁ lam z from rfl)
    have hs (a : Fin n) : hessian (v₁ a) z = H (lam, z) a :=
      hessian_renormalizedHarmonic hΩ (hu₁ a).1 _ _ hne hzT
    have hsym : (Q (lam, z) - (γ (lam, z))⁻¹).transpose = Q (lam, z) - (γ (lam, z))⁻¹ := by
      have hgi := (hs₂.2 z hzT).inv.isHermitian.isSymm.eq
      simp only [Q, principal, Matrix.transpose_sub, Matrix.transpose_smul,
        (hγpos (lam, z) hz.1).inv.isHermitian.isSymm.eq, hgi]
    have hvalues (a : Fin n) : ((Q (lam, z) - (γ (lam, z))⁻¹) * H (lam, z) a).trace =
        -(Q (lam, z) * hessian (V a) z).trace := by
      rw [← hs a]
      exact (hn a).1
    exact eq_sum_hessianRecoveryCoeff _ _ _ _ _ hsym hvalues
      (trace_normalized_difference (hγpos (lam, z) hz.1) (hgpos (lam, z) hz.1)) hz.2 q
  exact (smallJet_le_of_hessian_recovery_model hS hyU
    (fun a => ((hv₂ a).1.sub (hv₁ a).1).mono hST)
    (fun q v => (hcoeff (q, v)).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz => hz))
    heq (zero_le_one.trans hC₀) hB (fun q v => hby (q, v)) hVjet).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)

end CalderonN
