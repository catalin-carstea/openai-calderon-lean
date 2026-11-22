module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! The compact restriction algebra and spectral counting in Section 3.2.
Adapted from `Calderon/MixedKernelConstruction/C3Spectral.lean` at
d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

public section

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators RealInnerProductSpace
namespace LocalMetricExtension
attribute [local instance] Classical.propDecidable

/-- A continuous linear map with finite-dimensional range is a compact operator. -/
theorem isCompactOperator_of_finiteDimensional_range {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P : E →L[ℝ] F) [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)] :
    IsCompactOperator P := by
  let P' : E →L[ℝ] LinearMap.range P.toLinearMap :=
    P.codRestrict (LinearMap.range P.toLinearMap) (fun x => LinearMap.mem_range_self _ x)
  have hP' : IsCompactOperator P' := by
    refine ⟨closedBall 0 ‖P'‖, isCompact_closedBall _ _, ?_⟩
    refine Filter.mem_of_superset (ball_mem_nhds (0 : E) one_pos) fun x hx => ?_
    simp only [mem_preimage, mem_closedBall, dist_zero_right]
    have hx' : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp hx).le
    calc ‖P' x‖ ≤ ‖P'‖ * ‖x‖ := P'.le_opNorm x
      _ ≤ ‖P'‖ * 1 := by gcongr
      _ = ‖P'‖ := mul_one _
  have heq : (P : E → F) = ((LinearMap.range P.toLinearMap).subtypeL : _ → F) ∘ P' := rfl
  rw [heq]
  exact hP'.clm_comp _

/-- An operator that is an operator-norm limit of actual finite-range maps is compact. -/
theorem isCompactOperator_of_finiteRank_approx {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (R : E →L[ℝ] F)
    (happrox : ∀ ε > 0, ∃ P : E →L[ℝ] F,
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧ ‖R - P‖ ≤ ε) :
    IsCompactOperator R := by
  have h : ∀ n : ℕ, ∃ P : E →L[ℝ] F,
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧ ‖R - P‖ ≤ 1 / ((n : ℝ) + 1) :=
    fun n => happrox _ Nat.one_div_pos_of_nat
  choose P hPfin hP using h
  refine isCompactOperator_of_tendsto (l := atTop) (F := P) ?_
    (Filter.Eventually.of_forall fun n => by
      have := hPfin n
      exact isCompactOperator_of_finiteDimensional_range (P n))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact hP n

/-- Every finite set of Gram indices above a threshold `ε` has cardinality at most the
finrank of the range of ONE actual finite-range approximant with STRICT error `< ε`. -/
theorem card_le_finrank_of_gram {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R P : E →L[ℝ] F) [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    {ι : Type*} (w : ι → E) (hw : Orthonormal ℝ w) (μ : ι → ℝ)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (ε : ℝ) (hε : 0 < ε) (hRP : ‖R - P‖ < ε)
    (S : Finset ι) (hS : ∀ i ∈ S, ε ≤ |μ i|) :
    S.card ≤ Module.finrank ℝ (LinearMap.range P.toLinearMap) := by
  classical
  let f : S → LinearMap.range P.toLinearMap :=
    fun i => ⟨P (w i), LinearMap.mem_range_self _ _⟩
  have hli : LinearIndependent ℝ f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let v : E := ∑ i, g i • w i
    have hPv : P v = 0 := by
      have h0 := congrArg Subtype.val hg
      simpa [v, f, map_sum, map_smul] using h0
    have hwS : Orthonormal ℝ (fun i : S => w i) := hw.comp _ Subtype.val_injective
    have hnormv : ‖v‖ ^ 2 = ∑ i, g i * g i := by
      rw [← real_inner_self_eq_norm_sq]
      have h := hwS.inner_sum g g Finset.univ
      simp only [conj_trivial] at h
      exact h
    have hRv : ‖R v‖ ^ 2 = ∑ i, g i * (g i * μ i ^ 2) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [v, map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
        real_inner_smul_right, hgram, Subtype.coe_inj, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hRPv : R v = (R - P) v := by
      rw [sub_apply, hPv, sub_zero]
    have hlow : ε ^ 2 * ‖v‖ ^ 2 ≤ ‖R v‖ ^ 2 := by
      rw [hnormv, hRv, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hμ : ε ^ 2 ≤ μ i ^ 2 := by
        rw [← sq_abs (μ i)]
        exact pow_le_pow_left₀ hε.le (hS i i.2) 2
      have := mul_le_mul_of_nonneg_left hμ (mul_self_nonneg (g i))
      linarith
    have hup : ‖R v‖ ^ 2 ≤ ‖R - P‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [hRPv, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((R - P).le_opNorm v) 2
    have hv0 : ‖v‖ ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖v‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have hlt : ‖R - P‖ ^ 2 < ε ^ 2 := pow_lt_pow_left₀ hRP (norm_nonneg _) two_ne_zero
      have := hlow.trans hup
      nlinarith
    rw [hnormv] at hv0
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (g j))).mp hv0 i
      (Finset.mem_univ _)
    exact mul_self_eq_zero.mp this
  have := hli.fintype_card_le_finrank
  simpa using this

/-- C3-D6a: the threshold set is finite, with the same cardinal bound. -/
theorem finite_threshold_of_gram {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (R P : E →L[ℝ] F) [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    {ι : Type*} (w : ι → E) (hw : Orthonormal ℝ w) (μ : ι → ℝ)
    (hgram : ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0)
    (ε : ℝ) (hε : 0 < ε) (hRP : ‖R - P‖ < ε) :
    {i | ε ≤ |μ i|}.Finite ∧ ∀ h : {i | ε ≤ |μ i|}.Finite,
      h.toFinset.card ≤ Module.finrank ℝ (LinearMap.range P.toLinearMap) := by
  have hcard := card_le_finrank_of_gram R P w hw μ hgram ε hε hRP
  refine ⟨?_, fun h => hcard h.toFinset fun i hi => by simpa using hi⟩
  by_contra hinf
  obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank ℝ (LinearMap.range P.toLinearMap) + 1)
  have := hcard t fun i hi => ht hi
  omega



section Gram

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gram_isCompactOperator (R : E →L[ℝ] F) (hR : IsCompactOperator R) :
    IsCompactOperator (ContinuousLinearMap.adjoint R ∘L R) :=
  hR.clm_comp (ContinuousLinearMap.adjoint R)

theorem gram_isSymmetric (R : E →L[ℝ] F) :
    ((ContinuousLinearMap.adjoint R ∘L R : E →L[ℝ] E) : E →ₗ[ℝ] E).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- An orthonormal eigenfamily of the actual Gram operator satisfies the Gram identity with `μ_i = √ν_i`. -/
theorem gram_of_eigen (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (hw : Orthonormal ℝ w)
    (ν : ι → ℝ) (hT : ∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = ν i • w i) :
    ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then Real.sqrt (ν i) ^ 2 else 0 := by
  have key : ∀ i j, inner ℝ (R (w i)) (R (w j)) = ν j * inner ℝ (w i) (w j) := by
    intro i j
    have hj : ContinuousLinearMap.adjoint R (R (w j)) = ν j • w j := hT j
    rw [← ContinuousLinearMap.adjoint_inner_right, hj, real_inner_smul_right]
  have hν : ∀ i, 0 ≤ ν i := by
    intro i
    have h := key i i
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hw.1 i, one_pow,
      mul_one] at h
    rw [← h]
    positivity
  intro i j
  rw [key]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq, hw.1 i, one_pow, mul_one,
      Real.sq_sqrt (hν i)]
  · rw [ite_eq_right h, hw.2 h, mul_zero]

/-- Every eigenspace of the Gram operator of a compact injective
map is finite-dimensional; the zero eigenspace is `⊥` by injectivity. -/
theorem gram_eigenspace_finiteDimensional (R : E →L[ℝ] F) (hR : IsCompactOperator R)
    (hinj : Function.Injective R) (ν : ℝ) :
    FiniteDimensional ℝ (Module.End.eigenspace
      ((ContinuousLinearMap.adjoint R ∘L R : E →L[ℝ] E) : E →ₗ[ℝ] E) ν) := by
  by_cases hν : ν = 0
  · subst hν
    have hbot : Module.End.eigenspace
        ((ContinuousLinearMap.adjoint R ∘L R : E →L[ℝ] E) : E →ₗ[ℝ] E) 0 = ⊥ := by
      rw [Module.End.eigenspace_zero, LinearMap.ker_eq_bot']
      intro x hx
      have h0 : ContinuousLinearMap.adjoint R (R x) = 0 := hx
      have hRx : R x = 0 := by
        have h := ContinuousLinearMap.adjoint_inner_right R x (R x)
        rw [h0, inner_zero_right] at h
        exact inner_self_eq_zero.mp h.symm
      exact hinj (by rw [hRx, map_zero])
    rw [hbot]
    infer_instance
  · exact ContinuousLinearMap.finite_dimensional_eigenspace (gram_isCompactOperator R hR) ν hν

/-- The eigen Hilbert basis of the Gram operator of a compact
injective map, with strictly positive eigenvalues. No countability, separability or
infinite-dimensionality is used. -/
theorem exists_gram_hilbertBasis (R : E →L[ℝ] F) (hR : IsCompactOperator R)
    (hinj : Function.Injective R) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ E) (ν : ι → ℝ), (∀ i, 0 < ν i) ∧
      ∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = ν i • w i := by
  classical
  let T : E →ₗ[ℝ] E := ((ContinuousLinearMap.adjoint R ∘L R : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hfd : ∀ ν : ℝ, FiniteDimensional ℝ (Module.End.eigenspace T ν) :=
    gram_eigenspace_finiteDimensional R hR hinj
  let b : ∀ ν : ℝ, OrthonormalBasis (Fin (Module.finrank ℝ (Module.End.eigenspace T ν))) ℝ
      (Module.End.eigenspace T ν) := fun ν => stdOrthonormalBasis ℝ _
  let v : (Σ ν : ℝ, Fin (Module.finrank ℝ (Module.End.eigenspace T ν))) → E :=
    fun a => (b a.1 a.2 : E)
  have hon : Orthonormal ℝ v :=
    (gram_isSymmetric R).orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun ν => (b ν).orthonormal)
  have hle : (⨆ ν, Module.End.eigenspace T ν) ≤ Submodule.span ℝ (Set.range v) := by
    refine iSup_le fun ν x hx => ?_
    show ((⟨x, hx⟩ : Module.End.eigenspace T ν) : E) ∈ _
    rw [← (b ν).sum_repr ⟨x, hx⟩, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ν, k⟩, rfl⟩)
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [eq_bot_iff]
    calc (Submodule.span ℝ (Set.range v))ᗮ ≤ (⨆ ν, Module.End.eigenspace T ν)ᗮ :=
          Submodule.orthogonal_le hle
      _ = ⊥ := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
          (gram_isCompactOperator R hR) (gram_isSymmetric R)
  have hT : ∀ a, ContinuousLinearMap.adjoint R (R (v a)) = a.1 • v a := fun a =>
    Module.End.mem_eigenspace_iff.mp (b a.1 a.2).2
  refine ⟨_, HilbertBasis.mkOfOrthogonalEqBot hon hsp, fun a => a.1, ?_, ?_⟩
  · intro a
    show 0 < a.1
    have hw1 : ‖v a‖ = 1 := hon.1 a
    have hRne : R (v a) ≠ 0 := by
      intro h0
      have hva : v a = 0 := hinj (by rw [h0, map_zero])
      rw [hva, norm_zero] at hw1
      exact zero_ne_one hw1
    have h1 : inner ℝ (R (v a)) (R (v a)) = a.1 := by
      rw [← ContinuousLinearMap.adjoint_inner_right, hT a, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hw1]
      ring
    rw [← h1, real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hRne) 2
  · intro a
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact hT a

/-- Singular data `0 < μ_i ≤ ‖R‖`, `R†R w_i = μ_i² w_i` and the
Gram identity consumed by the threshold counting. -/
theorem exists_gram_spectral_data (R : E →L[ℝ] F) (hR : IsCompactOperator R)
    (hinj : Function.Injective R) :
    ∃ (ι : Type) (w : HilbertBasis ι ℝ E) (μ : ι → ℝ), (∀ i, 0 < μ i) ∧ (∀ i, μ i ≤ ‖R‖) ∧
      (∀ i, (ContinuousLinearMap.adjoint R ∘L R) (w i) = μ i ^ 2 • w i) ∧
      ∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0 := by
  obtain ⟨ι, w, ν, hν, hT⟩ := exists_gram_hilbertBasis R hR hinj
  have hsq : ∀ i, Real.sqrt (ν i) ^ 2 = ν i := fun i => Real.sq_sqrt (hν i).le
  have hgram := gram_of_eigen R w w.orthonormal ν hT
  refine ⟨ι, w, fun i => Real.sqrt (ν i), fun i => Real.sqrt_pos.mpr (hν i), ?_, ?_, hgram⟩
  · intro i
    have h := hgram i i
    rw [ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
    have hle : ‖R (w i)‖ ≤ ‖R‖ := by
      calc ‖R (w i)‖ ≤ ‖R‖ * ‖w i‖ := R.le_opNorm _
        _ = ‖R‖ := by rw [w.orthonormal.1 i, mul_one]
    show Real.sqrt (ν i) ≤ ‖R‖
    refine (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (norm_nonneg R) two_ne_zero).mp ?_
    rw [← h]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  · intro i
    show _ = Real.sqrt (ν i) ^ 2 • w i
    rw [hsq]
    exact hT i

end Gram

-- The resolution threshold and dyadic summable majorant are chosen
-- from the finite-rank approximation bounds before the operator is chosen.
theorem uniform_powerSum_of_counted_approx
    (M : ℝ) (hM : 0 < M) (dim s : ℕ) (B : ℝ) (N A0 : ℕ)
    (β : ℝ) (hβ : 0 < β) (hsβ : (dim : ℝ) < s * β) :
    ∃ P : ℝ, 0 ≤ P ∧
    ∀ {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (R : E →L[ℝ] F) {ι : Type*} (w : ι → E) (_hw : Orthonormal ℝ w) (μ : ι → ℝ),
      (∀ i, 0 < μ i) → (∀ i, μ i ≤ M) →
      (∀ i j, inner ℝ (R (w i)) (R (w j)) = if i = j then μ i ^ 2 else 0) →
      (∀ A : ℕ, A0 ≤ A → ∃ T : E →L[ℝ] F,
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ N * A ^ dim ∧
        ‖R - T‖ * (A : ℝ) ^ s ≤ B) →
      Summable (fun i => μ i ^ β) ∧ (∑' i, μ i ^ β) ≤ P := by
  classical
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hsβ
    exact (not_lt_of_ge (Nat.cast_nonneg dim)) hsβ
  set a : ℝ := ((2 : ℝ) ^ s)⁻¹ with ha
  have h2s : 1 < (2 : ℝ) ^ s := one_lt_pow₀ (by norm_num) hs
  have ha0 : 0 < a := by positivity
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ h2s
  -- the resolution offset `K`
  obtain ⟨K1, hK1⟩ := pow_unbounded_of_one_lt (B / M) (by norm_num : (1 : ℝ) < 2)
  set K := max A0 K1 with hKdef
  have hBK : B < M * ((2 : ℝ) ^ K) ^ s := by
    have h1 : (2 : ℝ) ^ K1 ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    have h2 : (2 : ℝ) ^ K ≤ ((2 : ℝ) ^ K) ^ s := le_self_pow₀ (one_le_pow₀ (by norm_num)) hs
    have h3 : B / M < ((2 : ℝ) ^ K) ^ s := by linarith
    rw [div_lt_iff₀ hM] at h3
    linarith
  have hA0 : ∀ m : ℕ, A0 ≤ 2 ^ (m + 1 + K) := fun m =>
    (le_max_left A0 K1).trans (Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hkey : ∀ m : ℕ, a ^ (m + 1) * ((2 : ℝ) ^ (m + 1 + K)) ^ s = ((2 : ℝ) ^ K) ^ s := by
    intro m
    rw [ha, inv_pow, inv_mul_eq_iff_eq_mul₀ (by positivity), ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_add]
    congr 1
    ring
  let g : ℕ → ℝ := fun m => (N : ℝ) * ((2 : ℝ) ^ (m + 1 + K)) ^ dim * (a ^ m * M) ^ β
  -- geometric majorant
  have haβ : a ^ β = ((2 : ℝ) ^ ((s : ℝ) * β))⁻¹ := by
    rw [ha, Real.inv_rpow (by positivity), ← Real.rpow_natCast_mul (by norm_num)]
  let scale : ℝ := 2 ^ dim
  have hscale : scale < (2 : ℝ) ^ ((s : ℝ) * β) := by
    simpa only [Real.rpow_natCast, scale] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hsβ
  set q : ℝ := scale * a ^ β with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, haβ, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hscale
  have hgeq : g = fun m => ((N : ℝ) * scale ^ (K + 1) * M ^ β) * q ^ m := by
    funext m
    simp only [g, hq]
    rw [Real.mul_rpow (by positivity) hM.le, ← Real.rpow_pow_comm ha0.le]
    have hpowSplit : ((2 : ℝ) ^ (m + 1 + K)) ^ dim = scale ^ (K + 1) * scale ^ m := by
      rw [show scale = (2 : ℝ) ^ dim from rfl, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [hpowSplit]
    ring
  have hgs : Summable g := by
    rw [hgeq]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine ⟨∑' m, g m, tsum_nonneg (fun m => by dsimp [g]; positivity), ?_⟩
  intro E F _ _ _ _ R ι w hw μ hμ hμM hgram happrox
  -- the bands
  let J : ℕ → Set ι := fun m => {i | a ^ (m + 1) * M < μ i ∧ μ i ≤ a ^ m * M}
  have huniq : ∀ i m m', i ∈ J m → i ∈ J m' → m ≤ m' := by
    intro i m m' h h'
    by_contra hlt
    push Not at hlt
    have h1 : a ^ m ≤ a ^ (m' + 1) := pow_le_pow_of_le_one ha0.le ha1.le (by omega)
    have h2 := mul_le_mul_of_nonneg_right h1 hM.le
    have h3 : μ i ≤ a ^ m * M := h.2
    have h4 : a ^ (m' + 1) * M < μ i := h'.1
    linarith
  have hcov : ∀ i, ∃! m, i ∈ J m := by
    intro i
    obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near_of_lt_one (div_pos (hμ i) hM)
      ((div_le_one hM).mpr (hμM i)) ha0 ha1
    have hm : i ∈ J m := ⟨(lt_div_iff₀ hM).mp hm1, (div_le_iff₀ hM).mp hm2⟩
    exact ⟨m, hm, fun m' hm' => le_antisymm (huniq _ _ _ hm' hm) (huniq _ _ _ hm hm')⟩
  -- the band majorant
  have hband : ∀ m (t : Finset (J m)), ∑ x ∈ t, μ x ^ β ≤ g m := by
    intro m t
    obtain ⟨P, hPfin, hPrank, hPerr⟩ := happrox (2 ^ (m + 1 + K)) (hA0 m)
    have := hPfin
    have hpow : (0 : ℝ) < ((2 : ℝ) ^ (m + 1 + K)) ^ s := by positivity
    have hlt : ‖R - P‖ < a ^ (m + 1) * M := by
      have he : ‖R - P‖ * ((2 : ℝ) ^ (m + 1 + K)) ^ s ≤ B := by exact_mod_cast hPerr
      have h1 : a ^ (m + 1) * M * ((2 : ℝ) ^ (m + 1 + K)) ^ s = M * ((2 : ℝ) ^ K) ^ s := by
        rw [mul_comm (a ^ (m + 1)) M, mul_assoc, hkey]
      by_contra hge
      push Not at hge
      have := mul_le_mul_of_nonneg_right hge hpow.le
      linarith
    have hcard := card_le_finrank_of_gram R P w hw μ hgram (a ^ (m + 1) * M) (by positivity) hlt
      (t.map (Function.Embedding.subtype _)) (by
        intro i hi
        obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hi
        rw [Function.Embedding.coe_subtype, abs_of_pos (hμ x)]
        exact x.2.1.le)
    rw [Finset.card_map] at hcard
    have hcardR : (t.card : ℝ) ≤ (N : ℝ) * ((2 : ℝ) ^ (m + 1 + K)) ^ dim := by
      have := hcard.trans hPrank
      exact_mod_cast this
    calc ∑ x ∈ t, μ x ^ β ≤ t.card • (a ^ m * M) ^ β :=
          Finset.sum_le_card_nsmul t _ _ fun x _ => Real.rpow_le_rpow (hμ x).le x.2.2 hβ.le
      _ = (t.card : ℝ) * (a ^ m * M) ^ β := nsmul_eq_mul _ _
      _ ≤ g m := mul_le_mul_of_nonneg_right hcardR (Real.rpow_nonneg (by positivity) _)
  have hf : (0 : ι → ℝ) ≤ fun i => μ i ^ β := fun i => Real.rpow_nonneg (hμ i).le β
  have hlocal (m : ℕ) : Summable (fun i : J m => μ i ^ β) :=
    summable_of_sum_le (fun i => hf i) (hband m)
  have hmaj (m : ℕ) : (∑' i : J m, μ i ^ β) ≤ g m :=
    Real.tsum_le_of_sum_le (fun i => hf i) (hband m)
  have hseries := Summable.of_nonneg_of_le
    (fun m => tsum_nonneg fun i : J m => hf i) hmaj hgs
  have hall := (summable_partition hf hcov).mpr ⟨hlocal, hseries⟩
  refine ⟨hall, ?_⟩
  rw [← (Set.sigmaEquiv J hcov).tsum_eq (fun i => μ i ^ β)]
  have htotal := (Set.sigmaEquiv J hcov).summable_iff.mpr hall
  exact (htotal.tsum_sigma' hlocal).trans_le (hseries.tsum_le_tsum hmaj hgs)

end LocalMetricExtension
