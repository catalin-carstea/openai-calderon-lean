module

public import Proof.CalderonN.FixedTube.Placement

import Mathlib.Tactic

/-!
Adapted from `Calderon/MixedKernelConstruction/MixedKernelClosedTubeConstruction.lean`
in `anisotropic-calderon-lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc.
-/

@[expose] public section

noncomputable section
open Set Metric Filter
open scoped Topology InnerProductSpace

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

/-- for `σ ≥ 0` the actual tube radius `(a, Y) ↦ a t(Y)^(1+σ)` is jointly continuous. -/
theorem tubeRadius_continuous (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous fun p : ℝ × (X dim) => tubeRadius normal M e0 p.1 σ p.2 := by
  have ht : Continuous (tubeHeight normal M e0) :=
    continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt (normal := normal) M e0 Y).continuousAt
  show Continuous fun p : ℝ × (X dim) => p.1 * tubeHeight normal M e0 p.2 ^ (1 + σ)
  exact continuous_fst.mul ((ht.comp continuous_snd).rpow_const fun _ => Or.inr (by linarith))

/-- the actual tube endpoint `(a, Y, ω) ↦ Y + r_a(Y) ω` is jointly continuous. -/
theorem tubeEndpoint_continuous (M e0 σ : ℝ) (hσ : 0 ≤ σ) :
    Continuous fun p : ℝ × (X dim) × (X dim) => p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2 :=
  continuous_snd.fst.add
    (((tubeRadius_continuous (normal := normal) M e0 σ hσ).comp (continuous_fst.prodMk continuous_snd.fst)).smul
      continuous_snd.snd)

/-- the literal N23 unseeded sweep set of `(a, Y, ω)` is closed. -/
theorem tubeSweep_isClosed (M e0 σ c0 B T0 amin amax : ℝ) (hσ : 0 ≤ σ) :
    IsClosed {p : ℝ × (X dim) × (X dim) | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 normal ∧ tubeHeight normal M e0 p.2.1 ≤ T0 ∧
      amin ≤ p.1 ∧ p.1 ≤ amax ∧
      c0 * ‖(p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
        min ((p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) normal) (p.2.1 normal)} := by
  have ht : Continuous (tubeHeight normal M e0) :=
    continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt (normal := normal) M e0 Y).continuousAt
  have hE := tubeEndpoint_continuous (normal := normal) M e0 σ hσ
  have hY : Continuous fun p : ℝ × (X dim) × (X dim) => p.2.1 := continuous_snd.fst
  have hY2 : Continuous fun p : ℝ × (X dim) × (X dim) => p.2.1 normal :=
    (EuclideanSpace.proj (𝕜 := ℝ) normal).continuous.comp hY
  have hX2 : Continuous fun p : ℝ × (X dim) × (X dim) => (p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) normal :=
    (EuclideanSpace.proj (𝕜 := ℝ) normal).continuous.comp hE
  have hc : ∀ c : ℝ, Continuous fun _ : ℝ × (X dim) × (X dim) => c := fun c => continuous_const
  have ha : Continuous fun p : ℝ × (X dim) × (X dim) => p.1 := continuous_fst
  have e1 : IsClosed {p : ℝ × (X dim) × (X dim) | ‖p.2.2‖ = 1} :=
    isClosed_eq (continuous_norm.comp continuous_snd.snd) (hc 1)
  have e2 : IsClosed {p : ℝ × (X dim) × (X dim) | -B - 1 ≤ p.2.1 normal} := isClosed_le (hc _) hY2
  have e3 : IsClosed {p : ℝ × (X dim) × (X dim) | tubeHeight normal M e0 p.2.1 ≤ T0} :=
    isClosed_le (ht.comp hY) (hc _)
  have e4 : IsClosed {p : ℝ × (X dim) × (X dim) | amin ≤ p.1} := isClosed_le (hc _) ha
  have e5 : IsClosed {p : ℝ × (X dim) × (X dim) | p.1 ≤ amax} := isClosed_le ha (hc _)
  have e6 : IsClosed {p : ℝ × (X dim) × (X dim) |
      c0 * ‖(p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
        min ((p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) normal) (p.2.1 normal)} :=
    isClosed_le ((hc c0).mul (hE.sub hY).norm) (hX2.min hY2)
  simp only [Set.setOf_and]
  exact e1.inter (e2.inter (e3.inter (e4.inter (e5.inter e6))))

/-- for `e0 > 0` the literal N23 unseeded sweep set of `(a, Y, ω)` is compact. -/
theorem tubeSweep_isCompact (M e0 σ c0 B T0 amin amax : ℝ) (hσ : 0 ≤ σ) (he0 : 0 < e0) :
    IsCompact {p : ℝ × (X dim) × (X dim) | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 normal ∧ tubeHeight normal M e0 p.2.1 ≤ T0 ∧
      amin ≤ p.1 ∧ p.1 ≤ amax ∧
      c0 * ‖(p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
        min ((p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) normal) (p.2.1 normal)} := by
  refine Metric.isCompact_of_isClosed_isBounded (tubeSweep_isClosed (normal := normal) M e0 σ c0 B T0 amin amax hσ) ?_
  set C : ℝ := |B| + 1 + |T0| + |M| with hC
  set S : ℝ := Real.sqrt ((T0 - M + B + 1) / e0 + C ^ 2) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  refine (Metric.isBounded_closedBall (x := (0 : ℝ × (X dim) × (X dim)))
    (r := |amin| + |amax| + S + 1)).subset ?_
  rintro ⟨a, Y, w⟩ ⟨hw, hY2, hT, ha1, ha2, -⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hamin := neg_abs_le amin
  have hamax := le_abs_self amax
  have h0min := abs_nonneg amin
  have h0max := abs_nonneg amax
  refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · rw [Real.norm_eq_abs]
    exact abs_le.2 ⟨by simp only at ha1 ⊢; linarith, by simp only at ha2 ⊢; linarith⟩
  · simp only at hY2 hT ⊢
    unfold tubeHeight at hT
    have hs0 := mul_nonneg he0.le (transversePair_nonneg normal Y)
    have h1 : transversePair normal Y Y ≤ (T0 - M + B + 1) / e0 := by
      rw [le_div_iff₀ he0]
      linarith [mul_comm e0 (transversePair normal Y Y)]
    have hT0 := le_abs_self T0
    have hM0 := neg_abs_le M
    have hT1 := abs_nonneg T0
    have hM1 := abs_nonneg M
    have hB0 := le_abs_self B
    have hB1 := abs_nonneg B
    have h2 : Y normal ^ 2 ≤ C ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hn : ‖Y‖ = Real.sqrt (transversePair normal Y Y + Y normal ^ 2) := by
      exact norm_eq_transversePair normal Y
    have hY : ‖Y‖ ≤ S := by
      rw [hn, hS]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  · simp only at hw ⊢
    linarith

/-- N23's constants make the literal sweep set `Q` compact, and N23's identity-data strictness
holds at every point of `Q`. -/
theorem tube_native_strict_sweep_set {c0 η d B M : ℝ} (hc0 : 0 < c0) (hη : 0 < η)
    (hη10 : η ≤ 1 / 10) (hc0η : 13 * η ≤ c0) (hd : 0 < d) (hB : 0 ≤ B) (hM : B + 3 < M) :
    ∃ σ T0 e0 : ℝ, 0 < σ ∧ σ ≤ 1 ∧ 0 < e0 ∧ e0 ≤ 1 ∧ M + B + B ^ 2 < T0 ∧
      1 < c0 * min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) * T0 ^ σ ∧ IsCompact {p : ℝ × (X dim) × (X dim) | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 normal ∧ tubeHeight normal M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) normal) (p.2.1 normal)} ∧
      ∀ p ∈ {p : ℝ × (X dim) × (X dim) | ‖p.2.2‖ = 1 ∧ -B - 1 ≤ p.2.1 normal ∧ tubeHeight normal M e0 p.2.1 ≤ T0 ∧
        min 1 (d / (2 * (M + B + B ^ 2) ^ 2)) ≤ p.1 ∧ p.1 ≤ 2 / c0 + 1 ∧
        c0 * ‖(p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) - p.2.1‖ ≤
          min ((p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2) normal) (p.2.1 normal)},
        ProductStrictHessianAt (fun _ => (1 : (Mat dim))) (fun _ => (1 : (Mat dim)))
          (tubePhase normal M e0 p.1 σ) (p.2.1 + tubeRadius normal M e0 p.1 σ p.2.1 • p.2.2,p.2.1) := by
  obtain ⟨σ, T0, e0, hσ, -, hσ1, hcap, hseed, he0, he01, -, hS⟩ :=
    tube_native_strict_sweep_base (normal := normal) hc0 hη hη10 hc0η hd hB hM
  refine ⟨σ, T0, e0, hσ, hσ1, he0, he01, hcap, hseed, tubeSweep_isCompact (normal := normal) M e0 σ c0 B T0 _ _ hσ.le he0, ?_⟩
  rintro ⟨a, Y, w⟩ ⟨hw, hY2, hT, ha1, ha2, hsep⟩
  exact hS a Y w hw hY2 hT ha1 ha2 (not_lt.2 hsep)

/-- at every sweep point the positive-height set `{t > 0}` is a neighborhood. -/
theorem tubeSweep_height_pos_nhds {M e0 B T0 : ℝ} (he0 : 0 ≤ e0) (hM : B + 3 < M)
    {p : ℝ × (X dim) × (X dim)} (hy : -B - 1 ≤ p.2.1 normal) (htT : tubeHeight normal M e0 p.2.1 ≤ T0) :
    {q : ℝ × (X dim) × (X dim) | 0 < tubeHeight normal M e0 q.2.1} ∈ 𝓝 p := by
  have ht : Continuous (tubeHeight normal M e0) :=
    continuous_iff_continuousAt.2 fun Y => (tube_height_hasFDerivAt (normal := normal) M e0 Y).continuousAt
  have h1 := (tube_base_height he0 hM hy htT).1
  exact (isOpen_lt continuous_const (ht.comp continuous_snd.fst)).mem_nhds
    (show 0 < tubeHeight normal M e0 p.2.1 by linarith)

end CalderonN.FixedTube
