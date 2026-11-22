module

public import Proof.Manuscript.MovingTrace.CompactBallCoefficientTube
public import Proof.Manuscript.MovingTrace.CompactNormalMetricFamily
public import Proof.Manuscript.MovingTrace.CollarPoissonTransport
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4800000

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

def radializedNormalFamily (g : P × Z → Mat (n+1)) : P × Z → Mat (n+1) :=
  fun q => radializedMetric radialCutoff (fun z => g (q.1,z)) q.2

/-- Enlarge the fixed ball into a signed collar inside a compact
parameter tube. The common divergence coefficient agrees on that open
tube, so the exact forcing can be computed just outside the sphere. -/
theorem exists_radialized_ballPoissonTube
    {J : Set P} (hJ : IsCompact J) {O : Set (P × Z)} (hO : IsOpen O)
    (hJO : J ×ˢ closedBall (0 : Z) 1 ⊆ O)
    (g : P × Z → Mat (n+1)) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) O)
    (hPos : ∀ q ∈ O, (g q).PosDef) :
    ∃ G : BallPoissonTube P (n+1), J ⊆ G.V ∧ G.g = radializedNormalFamily g ∧
      ∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v := by
  let m := radializedNormalFamily g
  have hm (i j : I (n+1)) : ContDiffOn ℝ ∞ (fun q => m q i j) O :=
    contDiffOn_radializedMetric_entries hO hg i j
  have hmP (q) (hq : q ∈ O) : (m q).PosDef :=
    radializedMetric_posDef (radialCutoff_range q.2) (hPos q hq)
  obtain ⟨V,W,a,Ka,lo,hi,hV,hW,hJV,hCW,hVW,ha,hKa,hA0,hAe,hEll⟩ :=
    exists_compactBallCoefficient_tube hO hJ hJO m hm hmP
  let G : BallPoissonTube P (n+1) :=
    ⟨V,hV,V ×ˢ W,hV.prod hW,Set.prod_mono Subset.rfl hCW,m,
      fun i j => (hm i j).mono hVW,fun q hq => hmP q (hVW hq),
      a,ha,Ka,hKa,hA0,hAe,lo,hi,hEll⟩
  obtain ⟨ε,hε,hεW⟩ := (isCompact_closedBall (0 : Z) 1).exists_cthickening_subset_open hW hCW
  rw [cthickening_closedBall hε.le zero_le_one] at hεW
  let δ := min ε (1/16)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ₁ : δ ≤ 1/16 := min_le_right _ _
  have hδW : closedBall (0 : Z) (1+δ) ⊆ W :=
    (closedBall_subset_closedBall (by dsimp [δ]; linarith [min_le_left ε (1/16:ℝ)] : 1+δ ≤ ε+1)).trans hεW
  refine ⟨G,hJV,rfl,fun v => ?_⟩
  refine ⟨⟨v,δ,hδ,hδ₁,Set.prod_mono Subset.rfl hδW,?_⟩,rfl⟩
  intro p hp x t ht j
  exact radializedMetric_signedCollar_mixed_zero (fun z => g (p,z)) v x t
    (ht.2.le.trans (by linarith)) j

/-- The independent slope parameter does not enter the exact normalized
metric. Its compact interval is retained for the subsequent amplitudes. -/
theorem exists_normalMetric_slope_ballPoissonTube
    {Y Ω : Set Z} (hY : IsCompact Y) {ρ : ℝ} (hρ : 0 < ρ)
    {γ g : ℝ → MetricField (n+1)}
    (hg : ∀ lam ∈ Icc (0:ℝ) 1, SmoothMetric univ (g lam))
    (hG : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × Z => g q.1 q.2 i j))
    {E : ℝ → Z × Z → Z} (hE : ContDiff ℝ ∞ (fun q : ℝ × (Z × Z) => E q.1 q.2))
    (hN : ∀ lam ∈ Icc (0:ℝ) 1, NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    {e : ℝ → Frame (n+1)} (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × Z => e q.1 q.2 i))
    (hFrame : ∀ lam ∈ Icc (0:ℝ) 1, ∀ y ∈ Y, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (b₀ : ℝ) :
    let J : Set (NormalMetricParameter (n+1) × ℝ) :=
      (Icc (0:ℝ) 1 ×ˢ (Y ×ˢ Icc (0:ℝ) ρ)) ×ˢ Icc (-b₀) b₀
    ∃ G : BallPoissonTube (NormalMetricParameter (n+1) × ℝ) (n+1),
      J ⊆ G.V ∧ G.g = radializedNormalFamily (fun q => symmetrizedNormalMetric g E e (q.1.1,q.2)) ∧
      ∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v := by
  dsimp only
  obtain ⟨V,W,hV,hW,hJV,hCW,hPos⟩ :=
    compactNormalMetricParameter_exists_open hY hρ hg hG hE hN he hFrame
  let P := NormalMetricParameter (n+1) × ℝ
  let J : Set P := (Icc (0:ℝ) 1 ×ˢ (Y ×ˢ Icc (0:ℝ) ρ)) ×ˢ Icc (-b₀) b₀
  let g' (q : P × Z) := symmetrizedNormalMetric g E e (q.1.1,q.2)
  let O : Set (P × Z) := (V ×ˢ (univ : Set ℝ)) ×ˢ W
  have hO : IsOpen O := (hV.prod isOpen_univ).prod hW
  have hJO : J ×ˢ closedBall (0:Z) 1 ⊆ O :=
    fun q hq => ⟨⟨hJV hq.1.1,mem_univ _⟩,hCW hq.2⟩
  have hJ : IsCompact J := (isCompact_Icc.prod (hY.prod isCompact_Icc)).prod isCompact_Icc
  have hg' (i j : I (n+1)) : ContDiff ℝ ∞ (fun q => g' q i j) :=
    (contDiff_symmetrizedNormalMetric_entry hG hE he i j).comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact exists_radialized_ballPoissonTube hJ hO hJO g' (fun i j => (hg' i j).contDiffOn)
    (fun q hq => hPos (q.1.1,q.2) ⟨hq.1.1,hq.2⟩)

end CalderonPaper
