module

public import Proof.Manuscript.MovingTrace.CompactNormalMetricFamily
public import Proof.CalderonN.GreenWeak
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Proof.CalderonN.ChartGeometry

@[expose] public section

noncomputable section

open Set Filter Metric CalderonN Matrix
open scoped ContDiff Topology

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false

variable {dim : ℕ} [NeZero dim]

/-- A jointly smooth symmetric metric family positive on a compact set
admits a positive global extension which agrees on a neighborhood. -/
theorem exists_global_spd_symmetrizedMetric_near_compact
    {γ : ℝ → MetricField dim} (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => γ q.1 q.2 i j))
    {J : Set (ℝ × X dim)} (hJ : IsCompact J) (hPos : ∀ p ∈ J, (γ p.1 p.2).PosDef) :
    ∃ γ' : ℝ → MetricField dim,
      (∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => γ' q.1 q.2 i j)) ∧
      (∀ lam y, (γ' lam y).PosDef) ∧
      ∃ O : Set (ℝ × X dim), IsOpen O ∧ J ⊆ O ∧
        EqOn (fun p : ℝ × X dim => γ' p.1 p.2)
          (fun p : ℝ × X dim => (1/2 : ℝ) • (γ p.1 p.2 + (γ p.1 p.2)ᵀ)) O := by
  let Q (p : ℝ × X dim) := (1/2 : ℝ) • (γ p.1 p.2 + (γ p.1 p.2)ᵀ)
  let U := {p | (Q p).PosDef}
  have hQ (i j : I dim) : ContDiff ℝ ∞ (fun p => Q p i j) :=
    ((hγ i j).add (hγ j i)).const_smul (1/2 : ℝ)
  have hSym (p : ℝ × X dim) : (Q p).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Q,Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_transpose,add_comm]
  have hU : IsOpen U := isOpen_posDef_of_continuous_entries Q (fun i j => (hQ i j).continuous) hSym
  have hJU : J ⊆ U := by
    intro p hp
    have hs := (hPos p hp).isHermitian.isSymm.eq
    have hq : Q p = γ p.1 p.2 := by
      dsimp only [Q]
      rw [hs,← two_smul ℝ,smul_smul]
      norm_num
    change (Q p).PosDef
    rw [hq]
    exact hPos p hp
  obtain ⟨χ,hχ,hχ01,hJO,_,hχU⟩ := hJ.exists_contDiff_cutoff hU hJU
  let g (p : ℝ × X dim) := χ p • Q p + (1-χ p) • (1 : Mat dim)
  have hg (i j : I dim) : ContDiff ℝ ∞ (fun p => g p i j) :=
    (hχ.mul (hQ i j)).add ((contDiff_const.sub hχ).mul contDiff_const)
  have hgPos (p : ℝ × X dim) : (g p).PosDef := by
    by_cases hz : χ p = 0
    · simpa [g,hz] using (Matrix.PosDef.one : (1 : Mat dim).PosDef)
    · have hp := hχU (subset_tsupport χ hz)
      have hχp := hχ01 (mem_range_self p)
      exact ((show (Q p).PosDef from hp).smul (lt_of_le_of_ne hχp.1 (Ne.symm hz))).add_posSemidef
        (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hχp.2))
  refine ⟨fun lam y => g (lam,y),hg,fun lam y => hgPos (lam,y),interior (χ ⁻¹' {1}),
    isOpen_interior,hJO,fun p hp => ?_⟩
  have hp' : p ∈ χ ⁻¹' {1} := interior_subset hp
  have he : χ p = 1 := mem_singleton_iff.mp hp'
  simp only [g,he,one_smul,sub_self,zero_smul,add_zero,Q]

omit [NeZero dim] in
/-- Smooth extension of the background preserves the scaled velocity at
any center where the two metrics agree as germs. -/
theorem scaledNormalTraceVelocity_congr_metric_near_center
    {g γ : MetricField dim} {O : Set (X dim)} (hO : IsOpen O) (hEq : EqOn g γ O)
    {y : X dim} (hy : y ∈ O) (E : X dim × X dim → X dim) (e : Frame dim)
    (s b : ℝ) (z a : X dim) :
    scaledNormalTraceVelocity g E e y s b z a = scaledNormalTraceVelocity γ E e y s b z a := by
  have hD (i j k : I dim) : coordDeriv i (fun x => g x j k) y =
      coordDeriv i (fun x => γ x j k) y :=
    eqOn_coordDeriv hO (fun x hx => congrArg (fun A : Mat dim => A j k) (hEq hx)) i hy
  have hΓ (k i j : I dim) : christoffel g y k i j = christoffel γ y k i j := by
    simp only [christoffel,hEq hy,hD]
  simp only [scaledNormalTraceVelocity,connection,hΓ]

variable [Nontrivial (Fin dim)]

set_option maxHeartbeats 2000000 in
/-- A common signed parameter tube for the actual moving-ball velocity.
The slope is an independent bounded parameter and the extension agrees
with the original physical operator at all compact centers. -/
theorem exists_global_spd_normalVelocity_tube
    {Y Ω : Set (X dim)} (hY : IsCompact Y) {ρ : ℝ} (_hρ : 0 < ρ)
    {γ : ℝ → MetricField dim}
    (hγ : ∀ lam ∈ Icc (0 : ℝ) 1, SmoothMetric univ (γ lam))
    (hG : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => γ q.1 q.2 i j))
    {E : ℝ → X dim × X dim → X dim} (hE : ContDiff ℝ ∞ (fun q : ℝ × (X dim × X dim) => E q.1 q.2))
    (hN : ∀ lam ∈ Icc (0 : ℝ) 1, NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    {e : ℝ → Frame dim} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X dim => e q.1 q.2 i))
    (hFrame : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ Y, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0) (b₀ : ℝ) :
    let P := NormalMetricParameter dim × ℝ
    let J : Set P := (Icc (0 : ℝ) 1 ×ˢ (Y ×ˢ Icc (0 : ℝ) ρ)) ×ˢ Icc (-b₀) b₀
    let V (g : ℝ → MetricField dim) (i : I dim) (q : P × X dim) :=
      scaledNormalTraceVelocity (g q.1.1.1) (E q.1.1.1) (e q.1.1.1) q.1.1.2.1
        q.1.1.2.2 q.1.2 q.2 (axis i)
    ∃ (γ' : ℝ → MetricField dim) (U : Set P) (A : Set (X dim)),
      (∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X dim => γ' q.1 q.2 i j)) ∧
      (∀ lam y, (γ' lam y).PosDef) ∧ IsOpen U ∧ IsOpen A ∧ J ⊆ U ∧
      closedBall (0 : X dim) 1 ⊆ A ∧
      (∀ i, ContDiffOn ℝ ∞ (V γ' i) (U ×ˢ A)) ∧
      ∀ i (q : P × X dim), q.1.1.1 ∈ Icc 0 1 → q.1.1.2.1 ∈ Y →
        V γ' i q = V γ i q := by
  dsimp only
  let P := NormalMetricParameter dim × ℝ
  let J : Set P := (Icc (0 : ℝ) 1 ×ˢ (Y ×ˢ Icc (0 : ℝ) ρ)) ×ˢ Icc (-b₀) b₀
  have hJ : IsCompact J := (isCompact_Icc.prod (hY.prod isCompact_Icc)).prod isCompact_Icc
  obtain ⟨γ',hγ',hγPos,O,hO,hJO,hEq⟩ := exists_global_spd_symmetrizedMetric_near_compact hG
    (isCompact_Icc.prod hY) (fun q hq => (hγ q.1 hq.1).2 _ (mem_univ _))
  let L (q : P × X dim) : NormalVelocityParameter dim :=
    (q.1.1.1,(q.1.1.2.1,(q.1.1.2.2,(q.1.2,q.2))))
  have hL : ContDiff ℝ ∞ L := contDiff_fst.fst.fst.prodMk
    (contDiff_fst.fst.snd.fst.prodMk (contDiff_fst.fst.snd.snd.prodMk (contDiff_fst.snd.prodMk contDiff_snd)))
  let B (q : P × X dim) := (q.1.1.1,(q.1.1.2.1,(q.1.1.2.2,q.2)))
  have hB : ContDiff ℝ ∞ B := contDiff_fst.fst.fst.prodMk
    (contDiff_fst.fst.snd.fst.prodMk (contDiff_fst.fst.snd.snd.prodMk contDiff_snd))
  let D (q : P × X dim) := coordinateMatrix (normalizedBallDerivative (E q.1.1.1) (e q.1.1.1)
    q.1.1.2.1 q.1.1.2.2 q.2)
  have hD (i j : I dim) : ContDiff ℝ ∞ (fun q => D q i j) :=
    (contDiff_normalizedBallDerivative_family_entry hE he i j).comp hB
  let T : Set (P × X dim) := {q | (D q).det ≠ 0}
  have hT : IsOpen T := isOpen_ne_fun (contDiffOn_univ.mp
    (contDiffOn_det_of_entries (fun i j => (hD i j).contDiffOn))).continuous continuous_const
  have hJT : J ×ˢ closedBall (0 : X dim) 1 ⊆ T := by
    rintro ⟨⟨⟨lam,y,s⟩,b⟩,z⟩ ⟨⟨⟨hl,hy,hs⟩,hb⟩,hz⟩
    have hd : s • frameVector (e lam) y z ∈ disk (γ lam) y ρ := by
      change metricPair (γ lam) y (s • frameVector (e lam) y z) (s • frameVector (e lam) y z) ≤ ρ^2
      rw [metricPair_scaled_frameVector _ _ _ (hFrame lam hl y hy)]
      exact (mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hz))).trans
        (pow_le_pow_left₀ hs.1 hs.2 2)
    exact normalizedBallDerivative_det_of_disk (hN lam hl) hy (hFrame lam hl y hy) s z hd
  obtain ⟨U,A,hU,hA,hJU,hBA,hUA⟩ := generalized_tube_lemma hJ (isCompact_closedBall (0 : X dim) 1) hT hJT
  refine ⟨γ',U,A,hγ',hγPos,hU,hA,hJU,hBA,?_,?_⟩
  · intro i
    let Z' : Set (NormalVelocityParameter dim) := {q | (coordinateMatrix (normalizedBallDerivative
      (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2.2)).det ≠ 0}
    let V (q : NormalVelocityParameter dim) : X dim :=
      scaledNormalTraceVelocity (γ' q.1) (E q.1) (e q.1) q.2.1
        q.2.2.1 q.2.2.2.1 q.2.2.2.2 (axis i)
    have hLocal : ContDiffOn ℝ ∞ V Z' :=
      contDiffOn_scaledNormalTraceVelocity_family (γ := γ') (E := E) (e := e)
        hγ' hγPos hE he (axis i) (U := Z') (fun _ hq => hq)
    have hLmap : MapsTo L (U ×ˢ A) Z' := fun _ hq => hUA hq
    have hV : ContDiffOn ℝ ∞ (V ∘ L) (U ×ˢ A) := hLocal.comp hL.contDiffOn hLmap
    exact hV
  · intro i q hl hy
    let O' : Set (X dim) := (Prod.mk q.1.1.1) ⁻¹' O
    have hO' : IsOpen O' := hO.preimage (continuous_const.prodMk continuous_id)
    have hyO' : q.1.1.2.1 ∈ O' := hJO ⟨hl,hy⟩
    have heq : EqOn (γ' q.1.1.1) (γ q.1.1.1) O' := by
      intro x hx
      have hSym := ((hγ q.1.1.1 hl).2 x (mem_univ _)).isHermitian.isSymm.eq
      have hPoint : γ' q.1.1.1 x = (1/2 : ℝ) • (γ q.1.1.1 x + (γ q.1.1.1 x)ᵀ) :=
        hEq (show (q.1.1.1,x) ∈ O from hx)
      rw [hPoint,hSym,← two_smul ℝ,smul_smul]
      norm_num
    exact scaledNormalTraceVelocity_congr_metric_near_center hO' heq hyO' _ _ _ _ _ _

end CalderonPaper
