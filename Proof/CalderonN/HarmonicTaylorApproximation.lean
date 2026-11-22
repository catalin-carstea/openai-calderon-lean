module

public import Proof.CalderonN.HarmonicJetEvaluation
public import Proof.CalderonN.CrossRestrictionSpectrum
public import Proof.CalderonN.CountedFloorGrid

import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Tactic

public section

/-! Cellwise Taylor approximation adapts `C3Jets` at anisotropic-calderon-lean
revision `d6704c49395a38eb07e0249afeb8ea83d67971cc` to the current chart and
the harmonic L² space. -/

noncomputable section
open Set MeasureTheory Metric Filter
open scoped ContDiff Topology ENNReal InnerProductSpace NNReal Nat

namespace CalderonN.HarmonicTaylor

variable {dim : ℕ} [NeZero dim]

/- Translation of the pointwise Taylor remainder on a compact segment. -/

theorem harmonicRep_taylor_remainder_of_bound (D : Set (X dim)) (hD : IsOpen D)
    (g : (MetricField dim))
    (hg : SmoothMetric D g) (K : Set (X dim)) (hKD : K ⊆ D) (s : ℕ)
    (L : ℝ) (_hL : 0 ≤ L)
    (hbound : ∀ (u : ChartL2 (d := dim) D) (f : (X dim) → ℝ), Harmonic D g f →
      (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict D] f →
        ∀ x ∈ K, ‖iteratedFDeriv ℝ (s+1) f x‖ ≤ L*‖u‖) :
    ∀ u : harmonicL2Space hD hg, ∀ c h : (X dim),
      (∀ t ∈ Icc (0 : ℝ) 1, c + t • h ∈ K) →
      |harmonicRepresentative u (c + h) -
          ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
            iteratedFDeriv ℝ k (harmonicRepresentative u) c (fun _ => h)|
        ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * ‖h‖ ^ (s + 1)) := by
  intro u c h hseg
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (n := s)
    (f := harmonicRepresentative u) (x := c) (y := h)
    (fun t ht => harmonicRep_contDiffAt hD hg u (s + 1) (hKD (hseg t ht)))
  rw [hT, add_sub_cancel_left, smul_eq_mul, abs_mul, abs_inv, Nat.abs_cast]
  gcongr
  rw [← Real.norm_eq_abs]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := L * ‖u‖ * ‖h‖ ^ (s + 1))
    (f := fun t => (1 - t) ^ s • iteratedFDeriv ℝ (s + 1)
      (harmonicRepresentative u) (c + t • h) (fun _ => h)) (by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have h1 : ‖(1 - t) ^ s‖ ≤ 1 := by
        rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
        exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
      have h2 : ‖iteratedFDeriv ℝ (s + 1) (harmonicRepresentative u) (c + t • h)
          (fun _ => h)‖ ≤ L * ‖u‖ * ‖h‖ ^ (s + 1) := by
        refine ((iteratedFDeriv ℝ (s + 1) (harmonicRepresentative u)
          (c + t • h)).le_opNorm _).trans ?_
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        gcongr
        exact hbound u.1 _ (harmonicRepresentative_spec u).1
          (harmonicRepresentative_spec u).2 _ (hseg t ht')
      rw [norm_smul]
      calc ‖(1 - t) ^ s‖ * _ ≤ 1 * (L * ‖u‖ * ‖h‖ ^ (s + 1)) :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
  simpa only [sub_zero, abs_one, mul_one] using hI

theorem harmonicRep_taylor_remainder (D : Set (X dim)) (hD : IsOpen D)
    (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (K : Set (X dim)) (hK : IsCompact K) (hKD : K ⊆ D) (s : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : harmonicL2Space hD hg, ∀ c h : (X dim),
      (∀ t ∈ Icc (0 : ℝ) 1, c + t • h ∈ K) →
      |harmonicRepresentative u (c + h) -
          ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
            iteratedFDeriv ℝ k (harmonicRepresentative u) c (fun _ => h)|
        ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * ‖h‖ ^ (s + 1)) := by
  obtain ⟨L,hL,h⟩ := hjet K hK hKD (s+1)
  exact ⟨L,hL,harmonicRep_taylor_remainder_of_bound D hD g hg K hKD s L hL h⟩

/-! ### C3-D3: the actual cellwise Taylor finite-rank operator -/

/-- The fixed orthonormal coordinate basis of `(X dim)`. -/
abbrev coordBasis (dim : ℕ) : OrthonormalBasis (Fin dim) ℝ (X dim) := EuclideanSpace.basisFun (Fin dim) ℝ

/-- Coordinate monomial of a basis word. -/
def wordMono {k : ℕ} (w : Fin k → Fin dim) (y : (X dim)) : ℝ :=
  ∏ j, inner ℝ (coordBasis dim (w j)) y

theorem continuous_wordMono {k : ℕ} (w : Fin k → Fin dim) (c : (X dim)) :
    Continuous fun x : (X dim) => wordMono w (x - c) :=
  continuous_finsetProd _ fun _ _ => continuous_const.inner (continuous_id.sub continuous_const)

theorem abs_wordMono_le {k : ℕ} (w : Fin k → Fin dim) (y : (X dim)) :
    |wordMono w y| ≤ ‖y‖ ^ k := by
  rw [wordMono, Finset.abs_prod]
  calc ∏ j, |inner ℝ (coordBasis dim (w j)) y| ≤ ∏ _j : Fin k, ‖y‖ := by
        gcongr with j
        exact (abs_real_inner_le_norm _ _).trans
          (by rw [(coordBasis dim).orthonormal.1 (w j), one_mul])
    _ = ‖y‖ ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact basis-word expansion of a multilinear diagonal value (`dim^k` coefficients). -/
theorem multilinear_diag_expand {k : ℕ}
    (m : ContinuousMultilinearMap ℝ (fun _ : Fin k => (X dim)) ℝ) (y : (X dim)) :
    m (fun _ => y) = ∑ w : Fin k → Fin dim, m (fun j => coordBasis dim (w j)) * wordMono w y := by
  have hy : (fun _ : Fin k => y) =
      fun _ => ∑ i, inner ℝ (coordBasis dim i) y • coordBasis dim i := by
    funext _
    exact ((coordBasis dim).sum_repr' y).symm
  rw [hy, m.map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [m.map_smul_univ, smul_eq_mul, mul_comm]
  rfl

/-- The `dim^k` actual jet coefficients at a point of `D`, as one CLM. -/
def harmonicCoeffCLM (D : Set (X dim)) (hD : IsOpen D) (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (k : ℕ) (x : (X dim)) (hx : x ∈ D) :
    harmonicL2Space hD hg →L[ℝ] ((Fin k → Fin dim) → ℝ) :=
  ContinuousLinearMap.pi fun w =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => (X dim)) ℝ
      (fun j => coordBasis dim (w j))).comp (harmonicJetCLM hD hg hjet k x hx)

/-- The actual restriction CLM `E → L²(S)` of ER446. -/

theorem cellMono_memLp (S : Set (X dim)) [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)]
    (Q : Set (X dim)) (hQ : MeasurableSet Q) (c : (X dim)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQδ : ∀ x ∈ Q, ‖x - c‖ ≤ δ) {k : ℕ} (w : Fin k → Fin dim) :
    MemLp (fun x => Q.indicator (fun x => (k ! : ℝ)⁻¹ * wordMono w (x - c)) x) 2
      ((volume : Measure (X dim)).restrict S) := by
  have hcont : Continuous fun x : (X dim) => (k ! : ℝ)⁻¹ * wordMono w (x - c) :=
    continuous_const.mul (continuous_wordMono w c)
  refine MemLp.of_bound ((hcont.aestronglyMeasurable).indicator hQ) ((k ! : ℝ)⁻¹ * δ ^ k)
    (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Q
  · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
    gcongr
    exact (abs_wordMono_le w _).trans (pow_le_pow_left₀ (norm_nonneg _) (hQδ x hx) k)
  · rw [indicator_of_notMem hx, norm_zero]
    positivity

/-- The finite coefficient space: `dim^k` coefficients per cell and degree `k ≤ s`. -/
abbrev CoeffSpace (dim N s : ℕ) : Type := ∀ p : Fin N × Fin (s + 1), (Fin p.2 → Fin dim) → ℝ

theorem coeffSpace_finrank (N s : ℕ) :
    Module.finrank ℝ (CoeffSpace dim N s) = N * ∑ k ∈ Finset.range (s + 1), dim ^ k := by
  rw [Module.finrank_pi_fintype]
  calc ∑ p : Fin N × Fin (s + 1), Module.finrank ℝ ((Fin p.2 → Fin dim) → ℝ)
      = ∑ p : Fin N × Fin (s + 1), dim ^ (p.2 : ℕ) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin]
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          Fin.sum_univ_eq_sum_range (fun k => dim ^ k) (s + 1)]

/-- One cell monomial `1_{Q_i}(x)·(k!)⁻¹·(x−c_i)^w`. -/
def cellPhi {N s : ℕ} (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (p : Fin N × Fin (s + 1))
    (w : Fin p.2 → Fin dim) (x : (X dim)) : ℝ :=
  (Q p.1).indicator (fun x => (((p.2 : ℕ)) ! : ℝ)⁻¹ * wordMono w (x - c p.1)) x

/-- The cellwise polynomial with coefficient vector `a`. -/
def cellFun {N s : ℕ} (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (a : CoeffSpace dim N s)
    (x : (X dim)) : ℝ :=
  ∑ p, ∑ w, a p w * cellPhi Q c p w x

theorem cellFun_memLp (S : Set (X dim)) [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)]
    {N s : ℕ} (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ)
    (a : CoeffSpace dim N s) :
    MemLp (cellFun Q c a) 2 ((volume : Measure (X dim)).restrict S) := by
  unfold cellFun cellPhi
  exact memLp_finsetSum _ fun p _ => memLp_finsetSum _ fun w _ =>
    (cellMono_memLp S (Q p.1) (hQ p.1) (c p.1) δ hδ (hQδ p.1) w).const_mul (a p w)

/-- The actual finite-dimensional synthesis map into `L²(S)`. -/
def cellV (S : Set (X dim)) [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)]
    {N : ℕ} (s : ℕ) (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ) :
    CoeffSpace dim N s →ₗ[ℝ] Lp ℝ 2 ((volume : Measure (X dim)).restrict S) where
  toFun a := (cellFun_memLp S Q c δ hδ hQ hQδ a).toLp (cellFun Q c a)
  map_add' a a' := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [cellFun, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [cellFun, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem cellV_ae (S : Set (X dim)) [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)]
    {N s : ℕ} (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ)
    (a : CoeffSpace dim N s) :
    (cellV S s Q c δ hδ hQ hQδ a : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict S]
      cellFun Q c a :=
  (cellFun_memLp S Q c δ hδ hQ hQδ a).coeFn_toLp

theorem cellFun_eq_of_mem {N s : ℕ} (Q : Fin N → Set (X dim)) (c : Fin N → (X dim))
    (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j))) (a : CoeffSpace dim N s) (x : (X dim))
    (i0 : Fin N) (hx : x ∈ Q i0) :
    cellFun Q c a x = ∑ k : Fin (s + 1), (((k : ℕ)) ! : ℝ)⁻¹ *
      ∑ w : Fin k → Fin dim, a (i0, k) w * wordMono w (x - c i0) := by
  simp only [cellFun, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i0]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [cellPhi, indicator_of_mem hx]
    ring
  · intro i _ hi
    have hxi : x ∉ Q i := fun h => Set.disjoint_left.mp (hdisj hi) h hx
    simp only [cellPhi, indicator_of_notMem hxi, mul_zero, Finset.sum_const_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- All actual jet coefficients at all cell centres, as one CLM. -/
def coeffAll (D : Set (X dim)) (hD : IsOpen D) (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (N s : ℕ) (c : Fin N → (X dim)) (hc : ∀ i, c i ∈ D) :
    harmonicL2Space hD hg →L[ℝ] CoeffSpace dim N s :=
  ContinuousLinearMap.pi fun p => harmonicCoeffCLM D hD g hg hjet p.2 (c p.1) (hc p.1)

theorem coeffAll_apply (D : Set (X dim)) (hD : IsOpen D) (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (N s : ℕ) (c : Fin N → (X dim)) (hc : ∀ i, c i ∈ D) (u : harmonicL2Space hD hg)
    (p : Fin N × Fin (s + 1)) (w : Fin p.2 → Fin dim) :
    coeffAll D hD g hg hjet N s c hc u p w =
      iteratedFDeriv ℝ p.2 (harmonicRepresentative u) (c p.1)
        (fun j => coordBasis dim (w j)) := by
  change harmonicJetCLM hD hg hjet p.2 (c p.1) (hc p.1) u _ = _
  rw [harmonicJetCLM_apply]


/-- C3-D3 error: the actual cell operator against the actual restriction, pointwise in `u`. -/
theorem cell_taylor_error (D : Set (X dim)) (hD : IsOpen D) (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (S : Set (X dim)) (hS : MeasurableSet S) (hSD : S ⊆ D)
    [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)]
    (K : Set (X dim)) (s : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hrem : ∀ u : harmonicL2Space hD hg, ∀ c h : (X dim),
      (∀ t ∈ Icc (0 : ℝ) 1, c + t • h ∈ K) →
      |harmonicRepresentative u (c + h) -
          ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
            iteratedFDeriv ℝ k (harmonicRepresentative u) c (fun _ => h)|
        ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * ‖h‖ ^ (s + 1)))
    {N : ℕ} (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ) (hδ : 0 ≤ δ)
    (hQ : ∀ i, MeasurableSet (Q i)) (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hcover : S ⊆ ⋃ i, Q i) (hc : ∀ i, c i ∈ D)
    (hgeom : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ K)
    (u : harmonicL2Space hD hg) :
    ‖harmonicRestrict hD hg hSD u -
        cellV S s Q c δ hδ hQ (fun i x hx => (hgeom i x hx).1)
          (coeffAll D hD g hg hjet N s c hc u)‖ ≤
      ((measureUnivNNReal ((volume : Measure (X dim)).restrict S) ^
        ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) *
        ((s ! : ℝ)⁻¹ * (L * ‖u‖ * δ ^ (s + 1))) := by
  have hC : 0 ≤ (s ! : ℝ)⁻¹ * (L * ‖u‖ * δ ^ (s + 1)) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg hL (norm_nonneg _)) (pow_nonneg hδ _))
  refine Lp.norm_le_of_ae_bound hC ?_
  have hRu := harmonicRestrict_ae hD hg hSD u
  have hPu := cellV_ae S Q c δ hδ hQ (fun i x hx => (hgeom i x hx).1)
    (coeffAll D hD g hg hjet N s c hc u)
  have hrep := ae_restrict_of_ae_restrict_of_subset hSD
    (harmonicRepresentative_spec u).2
  filter_upwards [Lp.coeFn_sub (harmonicRestrict hD hg hSD u)
      (cellV S s Q c δ hδ hQ (fun i x hx => (hgeom i x hx).1)
        (coeffAll D hD g hg hjet N s c hc u)), hRu, hPu, hrep,
    ae_restrict_mem hS] with x h1 h2 h3 h4 hxS
  obtain ⟨i0, hx0⟩ := mem_iUnion.mp (hcover hxS)
  obtain ⟨hδx, hseg⟩ := hgeom i0 x hx0
  have hpoly : cellFun Q c (coeffAll D hD g hg hjet N s c hc u) x =
      ∑ k ∈ Finset.range (s + 1), (k ! : ℝ)⁻¹ •
        iteratedFDeriv ℝ k (harmonicRepresentative u) (c i0) (fun _ => x - c i0) := by
    rw [cellFun_eq_of_mem Q c hdisj _ x i0 hx0, ← Fin.sum_univ_eq_sum_range (fun k => (k ! : ℝ)⁻¹ •
      iteratedFDeriv ℝ k (harmonicRepresentative u) (c i0) (fun _ => x - c i0)) (s + 1)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_eq_mul, multilinear_diag_expand]
    simp only [coeffAll_apply]
  rw [h1, Pi.sub_apply, h2, h3, h4, hpoly, Real.norm_eq_abs]
  have hr := hrem u (c i0) (x - c i0) hseg
  rw [add_sub_cancel] at hr
  refine hr.trans ?_
  gcongr

/-- The cell error has a geometric volume factor and the Taylor factorial. -/
private def cellTaylorNormFactor (S : Set (X dim))
    [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)] (s : ℕ) : ℝ :=
  ((measureUnivNNReal ((volume : Measure (X dim)).restrict S) ^
    ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ) * (s ! : ℝ)⁻¹

private theorem cellTaylorNormFactor_nonneg (S : Set (X dim))
    [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)] (s : ℕ) :
    0 ≤ cellTaylorNormFactor S s :=
  mul_nonneg (NNReal.coe_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem cell_taylor_finite_rank_of_bound (D : Set (X dim)) (hD : IsOpen D)
    (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (S : Set (X dim)) (hS : MeasurableSet S) (hSD : S ⊆ D)
    [IsFiniteMeasure ((volume : Measure (X dim)).restrict S)]
    (K : Set (X dim)) (hKD : K ⊆ D) (s : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ (u : ChartL2 (d := dim) D) (f : (X dim) → ℝ), Harmonic D g f →
      (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict D] f →
        ∀ x ∈ K, ‖iteratedFDeriv ℝ (s+1) f x‖ ≤ L*‖u‖) :
    ∀ (N : ℕ) (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ), 0 ≤ δ →
      (∀ i, MeasurableSet (Q i)) → Pairwise (fun i j => Disjoint (Q i) (Q j)) →
      S ⊆ ⋃ i, Q i → (∀ i, c i ∈ K) →
      (∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ K) →
      ∃ P : harmonicL2Space hD hg →L[ℝ] Lp ℝ 2 ((volume : Measure (X dim)).restrict S),
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤
            N * ∑ k ∈ Finset.range (s + 1), dim ^ k ∧
          ‖harmonicRestrict hD hg hSD - P‖ ≤
            cellTaylorNormFactor S s * L * δ ^ (s + 1) := by
  classical
  have hrem := harmonicRep_taylor_remainder_of_bound D hD g hg K hKD s L hL hbound
  let M : ℝ := ((measureUnivNNReal ((volume : Measure (X dim)).restrict S) ^
    ((2 : ℝ≥0∞).toReal⁻¹) : NNReal) : ℝ)
  have hM : 0 ≤ M := NNReal.coe_nonneg _
  intro N Q c δ hδ hQ hdisj hcover hcK hgeom
  have hQδ : ∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ := fun i x hx => (hgeom i x hx).1
  let V := cellV S s Q c δ hδ hQ hQδ
  let Jall := coeffAll D hD g hg hjet N s c (fun i => hKD (hcK i))
  let P : harmonicL2Space hD hg →L[ℝ] Lp ℝ 2 ((volume : Measure (X dim)).restrict S) :=
    ⟨V.comp (Jall : harmonicL2Space hD hg →ₗ[ℝ] CoeffSpace dim N s),
      (LinearMap.continuous_of_finiteDimensional V).comp Jall.continuous⟩
  have hle : LinearMap.range P.toLinearMap ≤ LinearMap.range V :=
    LinearMap.range_comp_le_range _ _
  refine ⟨P, ?_, ?_, ?_⟩
  · -- C3-D3′: actual finite-range witness through the finite synthesis `V`
    have : FiniteDimensional ℝ (LinearMap.range V) := LinearMap.finiteDimensional_range V
    exact Submodule.finiteDimensional_of_le hle
  · -- explicit rank count through the finite coefficient space
    calc Module.finrank ℝ (LinearMap.range P.toLinearMap)
        ≤ Module.finrank ℝ (LinearMap.range V) := Submodule.finrank_mono hle
      _ ≤ Module.finrank ℝ (CoeffSpace dim N s) := LinearMap.finrank_range_le V
      _ = N * ∑ k ∈ Finset.range (s + 1), dim ^ k := coeffSpace_finrank (dim := dim) N s
  · -- operator-norm error from the pointwise native Taylor remainder
    have hbound : ∀ u : harmonicL2Space hD hg,
        ‖harmonicRestrict hD hg hSD u - P u‖ ≤
          M * ((s ! : ℝ)⁻¹ * (L * ‖u‖ * δ ^ (s + 1))) := fun u =>
      cell_taylor_error D hD g hg hjet S hS hSD K s L hL hrem Q c δ hδ hQ hdisj hcover
        (fun i => hKD (hcK i)) hgeom u
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (cellTaylorNormFactor_nonneg S s) hL) (pow_nonneg hδ _)) fun u => ?_
    rw [sub_apply]
    refine (hbound u).trans (le_of_eq ?_)
    change _ = (M*(s ! : ℝ)⁻¹)*L*δ^(s+1)*‖u‖
    ring


/-- C3-D3: for a fixed scalar coefficient, compact buffer `K ⊆ D` and order `s`, the constant
`L` is chosen first; then for EVERY finite measurable partition of `S` into cells of radius
`δ` with centres in `K` and segments in `K`, the actual cellwise Taylor operator `P` has range
dimension `≤ N·Σ_{k≤s} 3^k` and `‖R − P‖ ≤ L·δ^(s+1)`. No approximation premise is used. -/
theorem exists_cell_taylor_finite_rank (D : Set (X dim)) (hD : IsOpen D)
    (g : (MetricField dim))
    (hg : SmoothMetric D g) (hjet : HarmonicInteriorJets D g)
    (S : Set (X dim)) (hS : MeasurableSet S) (hSD : S ⊆ D) (hSfin : volume S ≠ ⊤)
    (K : Set (X dim)) (hK : IsCompact K) (hKD : K ⊆ D) (s : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (N : ℕ) (Q : Fin N → Set (X dim)) (c : Fin N → (X dim)) (δ : ℝ), 0 ≤ δ →
      (∀ i, MeasurableSet (Q i)) → Pairwise (fun i j => Disjoint (Q i) (Q j)) →
      S ⊆ ⋃ i, Q i → (∀ i, c i ∈ K) →
      (∀ i, ∀ x ∈ Q i, ‖x - c i‖ ≤ δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, c i + t • (x - c i) ∈ K) →
      ∃ P : harmonicL2Space hD hg →L[ℝ] Lp ℝ 2 ((volume : Measure (X dim)).restrict S),
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤
            N * ∑ k ∈ Finset.range (s + 1), dim ^ k ∧
          ‖harmonicRestrict hD hg hSD - P‖ ≤ L * δ ^ (s + 1) := by
  have : IsFiniteMeasure ((volume : Measure (X dim)).restrict S) := isFiniteMeasure_restrict.mpr hSfin
  obtain ⟨L,hL,h⟩ := hjet K hK hKD (s+1)
  exact ⟨cellTaylorNormFactor S s * L,
    mul_nonneg (cellTaylorNormFactor_nonneg S s) hL,
    cell_taylor_finite_rank_of_bound D hD g hg hjet S hS hSD K hKD s L hL h⟩


end CalderonN.HarmonicTaylor

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Every order of the counted restriction approximation follows from
the chart interior derivative estimates and smooth representatives. -/
theorem exists_counted_harmonic_restrictionApprox {D : Set (X dim)} (hD : IsOpen D)
    {g : (MetricField dim)} (hg : SmoothMetric D g)
    (hjet : HarmonicInteriorJets D g)
    {S K : Set (X dim)} (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K) (hKD : K ⊆ D)
    (s : ℕ) : ∃ (B : ℝ) (N A₀ : ℕ),
      HasRestrictionApprox hD hg (hSK.trans hKD) s N A₀ B := by
  obtain ⟨d, hd, hdD⟩ := hK.exists_cthickening_subset_open hD hKD
  obtain ⟨L, hL, hP⟩ := HarmonicTaylor.exists_cell_taylor_finite_rank D hD g hg hjet
    S hS (hSK.trans hKD) ((measure_mono hSK).trans_lt hK.measure_lt_top).ne
    (cthickening d K) hK.cthickening hdD s
  exact counted_approx_of_cell_taylor
    (harmonicRestrict hD hg (hSK.trans hKD)) S K hS hSK hK d hd s L hL hP

/-- The finite-rank restriction estimates share their rank count and error
constant over a family with uniform chart interior bounds. -/
theorem exists_uniform_counted_harmonic_restrictionApprox
    {ι : Type*} {D : Set (X dim)} (hD : IsOpen D)
    {g : ι → (MetricField dim)} (hg : ∀ p, SmoothMetric D (g p))
    (hjet : ∀ p, HarmonicInteriorJets D (g p))
    (hUniform : ∀ (K : Set (X dim)), IsCompact K → K ⊆ D → ∀ k : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ p (u : ChartL2 (d := dim) D) (f : (X dim) → ℝ), Harmonic D (g p) f →
        (u : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict D] f →
          ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ L*‖u‖)
    {S K : Set (X dim)} (hS : MeasurableSet S) (hK : IsCompact K) (hSK : S ⊆ K) (hKD : K ⊆ D)
    (s : ℕ) : ∃ (B : ℝ) (N A₀ : ℕ),
      ∀ p, HasRestrictionApprox hD (hg p) (hSK.trans hKD) s N A₀ B := by
  obtain ⟨d,hd,hdD⟩ := hK.exists_cthickening_subset_open hD hKD
  have : IsFiniteMeasure ((volume : Measure (X dim)).restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSK).trans_lt hK.measure_lt_top).ne
  obtain ⟨L,hL,h⟩ := hUniform (cthickening d K) hK.cthickening hdD (s+1)
  exact counted_approx_of_cell_taylor_family
    (fun p => harmonicRestrict hD (hg p) (hSK.trans hKD)) S K hS hSK hK d hd s
    (HarmonicTaylor.cellTaylorNormFactor S s * L)
    (mul_nonneg (HarmonicTaylor.cellTaylorNormFactor_nonneg S s) hL)
    (fun p => HarmonicTaylor.cell_taylor_finite_rank_of_bound D hD (g p) (hg p) (hjet p)
      S hS (hSK.trans hKD) (cthickening d K) hdD s L hL (h p))

end CalderonN
