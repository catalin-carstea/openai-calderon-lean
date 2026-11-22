module

public import Proof.CalderonN.ConformalDepth
public import Proof.CalderonN.RadiusProfileGeometry

import Proof.CalderonN.FrameJetBound
import Proof.CalderonN.CarlemanCalculus
import Proof.CalderonN.MetricPair
import Proof.CalderonN.ProfileCovariant
import Proof.CalderonN.SoftplusComposition
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set Filter
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] {normal : I dim}

open SoftplusProfile (logSlope)

private theorem smooth_log_shrinkingRadius {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (p : ℕ) :
    ContDiff ℝ ∞ (fun z => Real.log (shrinkingRadius R p depth δ z)) :=
  (contDiff_shrinkingRadius ht R p δ).log (fun z => (shrinkingRadius_pos hR hδ p depth z).ne')

/-! The scalar-to-Fréchet bound follows the derivative budget in
`Calderon/ProfileFrechetJets.lean` at d6704c49395a38eb07e0249afeb8ea83d67971cc. -/
private theorem norm_iteratedFDeriv_log_shrinkingRadius_le
    {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth) (x : (X dim)) {R δ B D : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) {p : ℕ} (hp : 1 ≤ p)
    {n : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hD : 0 ≤ D) (hBa : 1 ≤ B * logSlope δ (depth x))
    (hDt : ∀ k : ℕ, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k depth x‖ ≤ D ^ k) :
    ‖iteratedFDeriv ℝ n (fun y => Real.log (shrinkingRadius R p depth δ y)) x‖ ≤
      (n.factorial : ℝ) * SoftplusProfile.profileJetBoundSum n * (B * D) ^ n *
        ((p : ℝ) * logSlope δ (depth x)) ^ n := by
  let f := fun y => Real.log (softplus δ (depth y))
  have hf : ContDiff ℝ ∞ f := (SoftplusProfile.contDiff_scalar_log_softplus δ hδ).comp ht
  have he : (fun y => Real.log (shrinkingRadius R p depth δ y)) =
      (fun _ => Real.log R) + fun y => (p : ℝ) * f y := by
    funext y
    simp only [Pi.add_apply, f, shrinkingRadius,
      Real.log_mul hR.ne' (pow_ne_zero _ (softplus_pos hδ (depth y)).ne'), Real.log_pow]
  rw [he, iteratedFDeriv_add_apply contDiffAt_const ((contDiff_const.mul hf).of_le (by simp)).contDiffAt,
    iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, zero_add]
  have hscale : iteratedFDeriv ℝ n (fun y => (p : ℝ) * f y) x =
      (p : ℝ) • iteratedFDeriv ℝ n f x := by
    exact iteratedFDeriv_const_smul_apply' (a := (p : ℝ)) (i := n) (x := x)
      ((hf.of_le (by simp)).contDiffAt)
  rw [hscale, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg p)]
  have hbase := SoftplusProfile.norm_iteratedFDeriv_log_softplus_comp_le
    depth ht n hn δ hδ x B D hB hBa hDt
  have h := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg p)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ n := le_self_pow₀ hpR (by omega)
  have ha : 0 ≤ logSlope δ (depth x) := (SoftplusProfile.logSlope_pos δ _ hδ).le
  have hBS := SoftplusProfile.profileJetBoundSum_nonneg n
  have hr := mul_le_mul_of_nonneg_right hpPow
    (show 0 ≤ (n.factorial : ℝ) * SoftplusProfile.profileJetBoundSum n *
      (B * logSlope δ (depth x)) ^ n * D ^ n by positivity)
  convert h.trans hr using 1
  simp only [mul_pow]
  ring

private theorem exists_uniform_depth_jet_bound {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth)
    {K : Set (X dim)} (hK : IsCompact K) (N : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ k : ℕ, 1 ≤ k → k ≤ N → ∀ x ∈ K,
      ‖iteratedFDeriv ℝ k depth x‖ ≤ D ^ k := by
  let S (x : (X dim)) := ∑ i ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ i depth x‖
  have hS : Continuous S :=
    continuous_finsetSum _ fun _ _ => (ht.continuous_iteratedFDeriv (by simp)).norm
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max A 1, le_max_right _ _, fun k hk hkn x hx => ?_⟩
  have hsingle : ‖iteratedFDeriv ℝ k depth x‖ ≤ S x := by
    exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
      (f := fun j => ‖iteratedFDeriv ℝ j depth x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  exact hsingle.trans ((le_abs_self _).trans ((hA x hx).trans ((le_max_left _ _).trans
    (le_self_pow₀ (le_max_right _ _) (by omega)))))

private theorem exists_log_radius_jet_bounds
    {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth) {K : Set (X dim)} (hK : IsCompact K)
    {N : ℕ} {m : ℝ} (hm : 0 < m) {T : ℝ} (hT : ∀ y ∈ K, depth y ≤ T) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ {y : (X dim)}, y ∈ K → ∀ (γ : (MetricField dim)),
      m ≤ Real.sqrt (covectorSq γ depth y) → ∀ {R δ : ℝ}, 0 < R → δ ∈ Ioc (0 : ℝ) 1 →
      ∀ {p : ℕ}, 1 ≤ p → ∀ k : ℕ, 1 ≤ k → k ≤ N →
        ‖iteratedFDeriv ℝ k (fun z => Real.log (shrinkingRadius R p depth δ z)) y‖ ≤
          J * (beta γ (shrinkingRadius R p depth δ) y)^k := by
  obtain ⟨D, hD, hDt⟩ := exists_uniform_depth_jet_bound ht hK N
  let B := 1 + Real.log (1 + Real.exp T)
  have hB : 1 ≤ B := le_add_of_nonneg_right (SoftplusProfile.log_exp_add_one_pos T).le
  let C (k : ℕ) :=
    (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D / m)^k
  have hC (k : ℕ) : 0 ≤ C k := by
    have hS := SoftplusProfile.profileJetBoundSum_nonneg k
    dsimp only [C]
    positivity
  let J := ∑ k ∈ Finset.range (N + 1), C k
  refine ⟨J, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro y hy γ hcov R δ hR hδ p hp k hk hkn
  have ha := (SoftplusProfile.logSlope_pos δ (depth y) hδ.1).le
  have hBa : 1 ≤ B * logSlope δ (depth y) :=
    (div_le_iff₀ (zero_lt_one.trans_le hB)).mp
      (SoftplusProfile.logSlope_uniform_lower_bound δ (depth y) T hδ.1 hδ.2 (hT y hy))
      |>.trans_eq (mul_comm _ _)
  let a := (p : ℝ) * logSlope δ (depth y)
  have ha' : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) ha
  let b := beta γ (shrinkingRadius R p depth δ) y
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hab : a ≤ b / m := by
    apply (le_div_iff₀ hm).2
    change a * m ≤ beta γ (shrinkingRadius R p depth δ) y
    rw [beta_shrinkingRadius (ht.differentiable (by simp) y) hR hδ.1]
    exact mul_le_mul_of_nonneg_left hcov ha'
  have hJ : C k ≤ J :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega))
  have hF := norm_iteratedFDeriv_log_shrinkingRadius_le ht y hR hδ.1 hp hk hB
    (zero_le_one.trans hD) hBa (fun i hi hik => hDt i hi (hik.trans hkn) y hy)
  have hscale :
      (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D)^k * (b / m)^k =
        C k * b^k := by
    dsimp only [C]
    simp only [div_eq_mul_inv, mul_pow]
    ring
  calc
    _ ≤ (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D)^k * a^k := hF
    _ ≤ (k.factorial : ℝ) * SoftplusProfile.profileJetBoundSum k * (B * D)^k * (b / m)^k := by
      have hS := SoftplusProfile.profileJetBoundSum_nonneg k
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha' hab k) (by positivity)
    _ = C k * b^k := hscale
    _ ≤ J * b^k := mul_le_mul_of_nonneg_right hJ (pow_nonneg hb _)

/-- The first and second coordinate derivatives of the radius stay
bounded where the protected quantities bound the radius and its weighted
logarithmic gradient. The bounds are uniform in the smoothing parameter. -/
theorem exists_shrinkingRadius_coordinate_derivative_bounds
    {depth : (X dim) → ℝ} (ht : ContDiff ℝ ∞ depth) {K : Set (X dim)} (hK : IsCompact K)
    {m : ℝ} (hm : 0 < m) {ρ ε : ℝ} (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {y : (X dim)}, y ∈ K → ∀ (γ : (MetricField dim)),
      m ≤ Real.sqrt (covectorSq γ depth y) → ∀ {R δ : ℝ}, 0 < R → δ ∈ Ioc (0 : ℝ) 1 →
      ∀ {p : ℕ}, 1 ≤ p →
      let r := shrinkingRadius R p depth δ
      r y ≤ ρ → r y * (beta γ r y)^2 ≤ ε →
      (∀ j, |coordDeriv j r y| ≤ B) ∧ (∀ i j, |coordDeriv i (coordDeriv j r) y| ≤ B) := by
  obtain ⟨T,hT⟩ := hK.exists_bound_of_continuousOn ht.continuous.continuousOn
  obtain ⟨J,hJ,hJb⟩ := exists_log_radius_jet_bounds ht hK (N := 2) hm
    (fun y hy => (le_abs_self _).trans (hT y hy))
  refine ⟨max (J * ((ρ+ε)/2)) ((J+J^2)*ε), ?_, ?_⟩
  · exact le_trans (mul_nonneg hJ (by positivity)) (le_max_left _ _)
  intro y hy γ hcov R δ hR hδ p hp r hry hrb
  let f := fun x => Real.log (r x)
  let b := beta γ r y
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hrpos (x : (X dim)) : 0 < r x := shrinkingRadius_pos hR hδ.1 p depth x
  have hr : ContDiff ℝ ∞ r := contDiff_shrinkingRadius ht R p δ
  have hf : ContDiff ℝ ∞ f := smooth_log_shrinkingRadius ht hR hδ.1 p
  have hf₁ (j : (I dim)) : ContDiff ℝ ∞ (coordDeriv j f) := Carleman.contDiff_pd hf
  have he (j : (I dim)) : coordDeriv j r = fun x => r x * coordDeriv j f x := by
    funext x
    have h := Carleman.pd_exp (i := j) hf x
    have hfexp : (fun z => Real.exp (f z)) = r := funext (fun z => Real.exp_log (hrpos z))
    change coordDeriv j (fun z => Real.exp (f z)) x = Real.exp (f x) * coordDeriv j f x at h
    rwa [hfexp,Real.exp_log (hrpos x)] at h
  have he₁ (j : (I dim)) : ProfileCovariant.coordinatePartialJet f 1 (fun _ => j) = coordDeriv j f := by
    funext x
    exact iteratedFDeriv_one_apply (fun _ => axis j)
  have h₁ (j : (I dim)) : |coordDeriv j f y| ≤ J*b := by
    rw [← he₁ j]
    exact (ProfileCovariant.abs_coordinatePartialJet_le f 1 (fun _ => j) y).trans
      (by simpa only [pow_one] using hJb hy γ hcov hR hδ hp 1 (by omega) (by omega))
  have h₂ (i j : (I dim)) : |coordDeriv i (coordDeriv j f) y| ≤ J*b^2 := by
    rw [← he₁ j]
    change |fderiv ℝ (ProfileCovariant.coordinatePartialJet f 1 (fun _ => j)) y (axis i)| ≤ _
    rw [ProfileCovariant.fderiv_coordinatePartialJet_apply f hf]
    exact (ProfileCovariant.abs_coordinatePartialJet_le f 2 _ y).trans
      (hJb hy γ hcov hR hδ hp 2 (by omega) (by omega))
  have hweighted : r y * b ≤ (ρ+ε)/2 := by
    have h := mul_nonneg (hrpos y).le (sq_nonneg (b-1))
    nlinarith only [h,hry,hrb]
  have hsecond (i j : (I dim)) : coordDeriv i (coordDeriv j r) y =
      r y * (coordDeriv i (coordDeriv j f) y + coordDeriv i f y * coordDeriv j f y) := by
    rw [he j]
    change Carleman.pd i (fun x => r x * coordDeriv j f x) y = _
    rw [Carleman.pd_mul hr (hf₁ j)]
    change coordDeriv i r y * coordDeriv j f y + r y * coordDeriv i (coordDeriv j f) y = _
    rw [he i]
    ring
  constructor
  · intro j
    rw [he j,abs_mul,abs_of_pos (hrpos y)]
    calc
      _ ≤ r y * (J*b) := mul_le_mul_of_nonneg_left (h₁ j) (hrpos y).le
      _ = J * (r y * b) := by ring
      _ ≤ J * ((ρ+ε)/2) := mul_le_mul_of_nonneg_left hweighted hJ
      _ ≤ _ := le_max_left _ _
  · intro i j
    rw [hsecond i j,abs_mul,abs_of_pos (hrpos y)]
    calc
      _ ≤ r y * (|coordDeriv i (coordDeriv j f) y| + |coordDeriv i f y| * |coordDeriv j f y|) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans_eq (by rw [abs_mul])) (hrpos y).le
      _ ≤ r y * (J*b^2 + (J*b)*(J*b)) :=
        mul_le_mul_of_nonneg_left (add_le_add (h₂ i j)
          (mul_le_mul (h₁ i) (h₁ j) (abs_nonneg _) (mul_nonneg hJ hb))) (hrpos y).le
      _ = (J+J^2) * (r y * b^2) := by ring
      _ ≤ (J+J^2)*ε := mul_le_mul_of_nonneg_left hrb (add_nonneg hJ (sq_nonneg _))
      _ ≤ _ := le_max_right _ _

/-- The protected profile constants are uniform in the shrinking parameter
and the amplitude. The chosen reference metric and a bounded frame family
are kept fixed before (p) is chosen. -/
theorem exists_conformal_shrinkingRadius_profile
    {K : Set (X dim)} (hK : IsCompact K) {g : (MetricField dim)}
    (hg : SmoothMetric univ g) (hunit : g 0 = 1)
    (e : ℝ → (Frame dim)) {E : ℝ} (hE : 0 ≤ E)
    (hframe : ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ y ∈ K, ∀ i j, |e lam y i j| ≤ E) :
    ∃ c c₀ M T : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 < M ∧ ∃ Cj : Fin 9 → ℝ,
      ∀ᶠ lam in 𝓝 (0 : ℝ), 0 < lam → ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ {p : ℕ}, 2 ≤ p →
        ∀ R : ℝ, 0 < R →
          let γ := conformalReference (depthScale normal 4) g lam
          let r := shrinkingRadius R p (conformalDepth normal 4) δ
          Profile K γ (e lam) r (c * (p : ℝ)) c₀ Cj ∧
            ∀ y ∈ K, r y * (beta γ r y)^2 ≤
              R * (p : ℝ)^2 * M^2 * (Real.log (1 + Real.exp T))^(p - 2) := by
  let depth := conformalDepth normal 4
  let γ := conformalReference (depthScale normal 4) g
  have ht : ContDiff ℝ ∞ depth := (contDiff_conformalDepth (normal := normal)) 4
  obtain ⟨m, M, hm, hM, hcov⟩ :=
    (exists_uniform_conformalDepth_covector_bounds (normal := normal)) isOpen_univ (mem_univ _) hK hg (by norm_num : 0 < (4 : ℝ))
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn ht.continuous.continuousOn
  have hT' (y : (X dim)) (hy : y ∈ K) : depth y ≤ T := (le_abs_self _).trans (hT y hy)
  let a₀ := 1 / (1 + Real.log (1 + Real.exp T))
  have ha₀ : 0 < a₀ := by
    have h := SoftplusProfile.log_exp_add_one_pos T
    dsimp only [a₀]
    positivity
  let c := a₀ * m
  have hc : 0 < c := mul_pos ha₀ hm
  let B := max 1 (1 / c)
  have hB : 1 ≤ B := le_max_left _ _
  have hBc : 1 ≤ B * c := by
    exact (div_le_iff₀ hc).mp (le_max_right (1 : ℝ) (1 / c))
  let Γ : ProfileCovariant.CoordinateConnectionFamily dim :=
    fun k i j q => christoffel (γ q.1) q.2 k i j
  have hγ (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j) univ := by
    simpa only [mem_univ, ofPred_true] using
      contDiffOn_conformalReference_family_entry hg ((contDiff_depthScale (normal := normal)) 4) i j
  have hγpos (q : ℝ × (X dim)) (_ : q ∈ (univ : Set (ℝ × (X dim)))) : (γ q.1 q.2).PosDef :=
    (hg.2 _ (mem_univ _)).smul ((depthScale_pos (normal := normal)) 4 q.2)
  have hΓ (k i j : (I dim)) : ContDiff ℝ ∞ (Γ k i j) :=
    contDiffOn_univ.mp (contDiffOn_christoffel_slice isOpen_univ hγ hγpos k i j)
  obtain ⟨J, hJ, hJb⟩ := exists_log_radius_jet_bounds ht hK (N := 8) hm hT'
  have horder (j : Fin 9) (hj : 1 ≤ j.val) :=
    ProfileCovariant.exists_covariantCoordinateJet_compact_bound Γ hΓ j.val hj K hK
  let A (j : Fin 9) : ℝ := if hj : 1 ≤ j.val then Classical.choose (horder j hj) else 0
  let Cj (j : Fin 9) : ℝ :=
    Real.sqrt (Fintype.card (Fin j.val → (I dim))) *
      ((Fintype.card (Fin j.val → (I dim)) : ℝ) * (A j * J * B^j.val) * E^j.val)
  refine ⟨c, M⁻¹, M, T, hc, inv_pos.mpr hM, hM, Cj, ?_⟩
  have hstrict := (eventually_conformalDepth_strict (normal := normal)) isOpen_univ (mem_univ _) hK hg hunit
  filter_upwards [hcov, hstrict, hframe, Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)]
    with lam hcov hstrict hframe hlam hpos δ hδ p hp R hR
  let r := shrinkingRadius R p depth δ
  let f := fun z => Real.log (r z)
  have hf : ContDiff ℝ ∞ f := smooth_log_shrinkingRadius ht hR hδ.1 p
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  refine ⟨⟨(contDiff_shrinkingRadius ht R p δ).contDiffOn, ?_⟩, ?_⟩
  · intro y hy
    obtain ⟨_, hlow, hupp⟩ := hcov y hy
    have hbeta₀ : c * (p : ℝ) ≤ beta (γ lam) r y := by
      have ha := SoftplusProfile.logSlope_uniform_lower_bound δ (depth y) T hδ.1 hδ.2 (hT' y hy)
      rw [beta_shrinkingRadius (ht.differentiable (by simp) y) hR hδ.1]
      calc
        _ = (p : ℝ) * a₀ * m := by dsimp only [c]; ring
        _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _))
          hlow hm.le (mul_nonneg (Nat.cast_nonneg _) (SoftplusProfile.logSlope_pos δ _ hδ.1).le)
    have hb : c ≤ beta (γ lam) r y := by
      exact (le_mul_of_one_le_right hc.le hpR).trans hbeta₀
    have hBb : 1 ≤ B * beta (γ lam) r y := hBc.trans
      (mul_le_mul_of_nonneg_left hb (zero_le_one.trans hB))
    refine ⟨shrinkingRadius_pos hR hδ.1 p depth y, hbeta₀, ?_, ?_⟩
    · intro v
      have h := log_shrinkingRadius_concave isOpen_univ ht.contDiffOn (mem_univ y)
        hR hδ.1 (c := 1) zero_le_one hM p (γ lam) hupp v
        (metricPair_nonneg_of_posDef (hγpos (lam,y) (mem_univ _)) v)
        (by simpa only [neg_one_mul] using (hstrict y hy).2 v)
      simpa only [one_div] using h
    · intro j hj
      have hA := Classical.choose_spec (horder j hj)
      have hAn : 0 ≤ A j := by simpa only [A, dite_eq_left hj] using hA.1
      have hbound (idx : Fin j.val → (I dim)) :
          |covJet (γ lam) f j.val y idx| ≤ A j * J * B^j.val * (beta (γ lam) r y)^j.val := by
        have he := ProfileCovariant.covJet_eq_on isOpen_univ (γ lam) Γ lam
          (fun _ _ _ _ _ => rfl) f j.val idx (mem_univ y)
        change covJet (γ lam) f j.val y idx =
          ProfileCovariant.covariantCoordinateJet Γ f lam j.val y idx at he
        rw [he, show A j = Classical.choose (horder j hj) from dite_eq_left hj]
        exact hA.2 lam ⟨hpos.le, hlam.le⟩ y hy idx f hf _ B J
          (Real.sqrt_nonneg _) hB hBb hJ
          (fun i hi hj' => hJb hy (γ lam) hlow hR hδ (by omega) i hi
            (hj'.trans (by have := j.isLt; omega)))
      have hbnonneg : 0 ≤ beta (γ lam) r y := Real.sqrt_nonneg _
      have hmul := jetNorm_le_of_component_bound (γ lam) (e lam) f y j.val
        (A := A j * J * B^j.val * (beta (γ lam) r y)^j.val)
        (by positivity) hE (hframe hpos y hy) hbound
      convert hmul using 1
      dsimp only [Cj]
      ring
  · intro y hy
    exact shrinkingRadius_mul_beta_sq_le (ht.differentiable (by simp) y) hR hδ.1 hδ.2
      (hT' y hy) hM.le hp (γ lam) (hcov y hy).2.2

end CalderonN
