module

public import Proof.Manuscript.MovingTrace.RadializedCollar
public import Proof.CalderonN.NormalChartFamilies
public import Proof.CalderonN.NormalizedVelocityAtZero
public import Proof.CalderonN.MetricPair
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Matrix Filter
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

variable {d : ℕ} [NeZero d]

private theorem matrix_posDef_of_test_unit {A : Mat d} (hA : A.IsHermitian)
    (hQ : ∀ v ∈ standardSphere d, 0 < metricPair (fun _ => A) 0 v v) :
    A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA (fun w hw => ?_)
  let v : X d := WithLp.toLp 2 w
  have hv : v ≠ 0 := by
    intro h
    apply hw
    exact (WithLp.toLp_injective 2) h
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let e := ‖v‖⁻¹ • v
  have he : e ∈ standardSphere d := by
    apply mem_sphere_zero_iff_norm.mpr
    rw [show e = ‖v‖⁻¹ • v from rfl,norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ hnv.ne']
  have hq := hQ e he
  have hV : v = ‖v‖ • e := by
    rw [show e = ‖v‖⁻¹ • v from rfl,smul_inv_smul₀ hnv.ne']
  have h : 0 < metricPair (fun _ => A) 0 v v := by
    rw [hV,metricPair_smul_same]
    exact mul_pos (pow_pos hnv 2) hq
  simpa only [v,metricPair_eq_dotProduct,WithLp.ofLp_toLp,star_trivial] using h

/-- Positive definiteness of a continuous, globally symmetric matrix
family holds on an open parameter set. -/
theorem isOpen_posDef_of_continuous_entries {P : Type*} [TopologicalSpace P]
    (g : P → Mat d) (hg : ∀ i j, Continuous (fun q => g q i j))
    (hSym : ∀ q, (g q).IsHermitian) :
    IsOpen {q | (g q).PosDef} := by
  let Q (q : P × X d) := metricPair (fun _ => g q.1) 0 q.2 q.2
  have hCoord (i : I d) : Continuous (fun q : P × X d => q.2 i) :=
    (EuclideanSpace.proj i : X d →L[ℝ] ℝ).continuous.comp continuous_snd
  have hEnt (i j : I d) : Continuous (fun q : P × X d => g q.1 i j) :=
    (hg i j).comp continuous_fst
  have hSum : Continuous (fun q : P × X d => ∑ i : I d, ∑ j : I d,
      g q.1 i j * q.2 i * q.2 j) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
      ((hEnt i j).mul (hCoord i)).mul (hCoord j)))
  have hQ : Continuous Q := hSum
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hO : IsOpen {p | 0 < Q p} := isOpen_lt continuous_const hQ
  have hProd : {q} ×ˢ standardSphere d ⊆ {p | 0 < Q p} := by
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    change 0 < metricPair (fun _ => g p) 0 z z
    rw [show p = q from mem_singleton_iff.mp hp]
    exact metricPair_pos_of_posDef (g := fun _ => g q) (y := 0) hq (norm_ne_zero_iff.mp
      ((mem_sphere_zero_iff_norm.mp hz).trans_ne one_ne_zero))
  obtain ⟨V,W,hV,_,hqV,hSW,hVW⟩ := generalized_tube_lemma (isCompact_singleton (x := q))
    (isCompact_sphere (0 : X d) 1) hO hProd
  have hVQ : V ⊆ {p : P | (g p).PosDef} := by
    intro p hp
    apply matrix_posDef_of_test_unit (hSym p)
    intro z hz
    have h : (p,z) ∈ {p : P × X d | 0 < Q p} := hVW ⟨hp,hSW hz⟩
    exact h
  exact mem_of_superset (hV.mem_nhds (hqV (mem_singleton q))) hVQ

abbrev NormalMetricParameter (d : ℕ) := ℝ × (X d × ℝ)

def symmetrizedNormalMetric (g : ℝ → MetricField d) (E : ℝ → X d × X d → X d)
    (e : ℝ → Frame d) (q : NormalMetricParameter d × X d) : Mat d :=
  let A := normalizedBallMetric (g q.1.1) (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2 q.2
  (1/2 : ℝ) • (A + Aᵀ)

theorem symmetrizedNormalMetric_eq
    {g : ℝ → MetricField d} {E : ℝ → X d × X d → X d}
    {e : ℝ → Frame d} {q : NormalMetricParameter d × X d}
    (hSym : (normalizedBallMetric (g q.1.1) (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2 q.2).IsSymm) :
    symmetrizedNormalMetric g E e q =
      normalizedBallMetric (g q.1.1) (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2 q.2 := by
  dsimp only [symmetrizedNormalMetric]
  rw [hSym.eq,← two_smul ℝ,smul_smul,one_div_mul_cancel (by norm_num),one_smul]

theorem contDiff_symmetrizedNormalMetric_entry
    {g : ℝ → MetricField d} (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X d => g q.1 q.2 i j))
    {E : ℝ → X d × X d → X d} (hE : ContDiff ℝ ∞ (fun q : ℝ × (X d × X d) => E q.1 q.2))
    {e : ℝ → Frame d} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X d => e q.1 q.2 i))
    (i j : I d) : ContDiff ℝ ∞ (fun q : NormalMetricParameter d × X d =>
      symmetrizedNormalMetric g E e q i j) := by
  let reshape (q : NormalMetricParameter d × X d) := (q.1.1,(q.1.2.1,(q.1.2.2,q.2)))
  have hrec : ContDiff ℝ ∞ reshape := contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk contDiff_snd))
  have hi := (contDiff_normalizedBallMetric_family_entry hE he hg i j).comp hrec
  have hj := (contDiff_normalizedBallMetric_family_entry hE he hg j i).comp hrec
  exact (hi.add hj).const_smul (1/2 : ℝ)

theorem symmetrizedNormalMetric_isHermitian
    (g : ℝ → MetricField d) (E : ℝ → X d × X d → X d)
    (e : ℝ → Frame d) (q : NormalMetricParameter d × X d) :
    (symmetrizedNormalMetric g E e q).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [symmetrizedNormalMetric,Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_transpose,add_comm]

theorem normalizedBallDerivative_det_of_disk [Nontrivial (Fin d)]
    {Y Ω : Set (X d)} {γ : MetricField d} {E : X d × X d → X d} {R : X d → ℝ}
    (hN : NormalCoordinates Y Ω γ E R) {y : X d} (hy : y ∈ Y)
    {e : Frame d} (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (r : ℝ) (z : X d) (hDisk : r • frameVector e y z ∈ disk γ y (R y)) :
    (coordinateMatrix (normalizedBallDerivative E e y r z)).det ≠ 0 := by
  have hD : Function.Bijective (fderiv ℝ (fun v => E (y,v)) (r • frameVector e y z)) :=
    ((hN.2 y hy).2.2 _ hDisk).2.1
  have hF : Function.Bijective (frameVectorL (e y)) := by
    change Function.Bijective (fun z => frameVectorL (e y) z)
    simp_rw [frameVectorL_apply_frame]
    exact bijective_frameVector γ e y he
  have hB := hD.comp hF
  let D : X d →L[ℝ] X d := normalizedBallDerivative E e y r z
  have hEq : Function.Bijective D := hB
  let q : X d ≃L[ℝ] X d := (LinearEquiv.ofBijective D.toLinearMap hEq).toContinuousLinearEquiv
  have hQ : q.toContinuousLinearMap = D := by ext; rfl
  change (coordinateMatrix D).det ≠ 0
  rw [← hQ]
  exact coordinateMatrix_det_ne_zero q

/-- Build a fixed compact parameter tube containing the closed normal
balls, including the terminal allowed radius and zero. -/
theorem compactNormalMetricParameter_exists_open [Nontrivial (Fin d)]
    {Y Ω : Set (X d)} (hY : IsCompact Y) {ρ : ℝ} (hρ : 0 < ρ)
    {γ g : ℝ → MetricField d}
    (hg : ∀ lam ∈ Icc (0 : ℝ) 1, SmoothMetric univ (g lam))
    (hG : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × X d => g q.1 q.2 i j))
    {E : ℝ → X d × X d → X d} (hE : ContDiff ℝ ∞ (fun q : ℝ × (X d × X d) => E q.1 q.2))
    (hN : ∀ lam ∈ Icc (0 : ℝ) 1, NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    {e : ℝ → Frame d} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X d => e q.1 q.2 i))
    (hFrame : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ Y, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0) :
    let J : Set (NormalMetricParameter d) := Icc 0 1 ×ˢ (Y ×ˢ Icc 0 ρ)
    ∃ V : Set (NormalMetricParameter d), ∃ W : Set (X d),
      IsOpen V ∧ IsOpen W ∧ J ⊆ V ∧ closedBall (0 : X d) 1 ⊆ W ∧
      ∀ q ∈ V ×ˢ W, (symmetrizedNormalMetric g E e q).PosDef := by
  dsimp only
  let J : Set (NormalMetricParameter d) := Icc 0 1 ×ˢ (Y ×ˢ Icc 0 ρ)
  let S : Set (NormalMetricParameter d × X d) := {q | (symmetrizedNormalMetric g E e q).PosDef}
  have hJ : IsCompact J := isCompact_Icc.prod (hY.prod isCompact_Icc)
  have hS : IsOpen S := isOpen_posDef_of_continuous_entries _ (fun i j =>
    (contDiff_symmetrizedNormalMetric_entry hG hE he i j).continuous) (symmetrizedNormalMetric_isHermitian g E e)
  apply generalized_tube_lemma hJ (isCompact_closedBall (0 : X d) 1) hS
  rintro ⟨⟨lam,y,r⟩,z⟩ ⟨⟨hlam,hy,hr⟩,hz⟩
  have hDisk : r • frameVector (e lam) y z ∈ disk (γ lam) y ρ := by
    change metricPair (γ lam) y (r • frameVector (e lam) y z) (r • frameVector (e lam) y z) ≤ ρ^2
    rw [metricPair_scaled_frameVector _ _ _ (hFrame lam hlam y hy)]
    have hnorm : ‖z‖ ≤ 1 := by simpa [mem_closedBall,dist_zero_right] using hz
    have hr₂ : r^2 ≤ ρ^2 := pow_le_pow_left₀ hr.1 hr.2 2
    exact (mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hnorm)).trans hr₂
  have hD := normalizedBallDerivative_det_of_disk (hN lam hlam) hy (hFrame lam hlam y hy) r z hDisk
  have hPos := normalizedBallMetric_posDef ((hg lam hlam).2 _ (mem_univ _)) hD
  change (symmetrizedNormalMetric g E e ((lam,y,r),z)).PosDef
  rw [symmetrizedNormalMetric_eq hPos.isHermitian.isSymm]
  exact hPos

end CalderonPaper
