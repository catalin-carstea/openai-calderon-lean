module

public import Proof.Manuscript.LowerGreen.BallCutoffChains
public import Proof.CalderonN.ParametricMetricBallDirichlet

import Proof.CalderonN.CompactSmoothExtension
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

public section

noncomputable section

open Set Metric Filter CalderonN CalderonN.BallDirichlet
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

set_option maxHeartbeats 2100000 in
/-- One compactly supported smooth divergence family on an open tube
around a compact set of normalized metric parameters. -/
theorem exists_supportedBallFamily_of_metric
    {J : Set P} (hJ : IsCompact J) {U : Set (P × X n)} (hU : IsOpen U)
    (hCU : J ×ˢ closedBall (0 : X n) 1 ⊆ U)
    {g : P × X n → Mat n}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) :
    ∃ (F : SupportedBallFamily P n) (W : Set (X n)),
      J ⊆ F.V ∧ IsOpen W ∧ closedBall (0 : X n) 1 ⊆ W ∧ F.V ×ˢ W ⊆ U ∧
        ∀ p ∈ F.V, ∀ z ∈ W, ∀ i j, F.a (p,z) i j =
          divergenceCoeff (fun x => g (p,x)) z i j := by
  let A (q : P × X n) : Mat n := fun i j => divergenceCoeff (fun z => g (q.1,z)) q.2 i j
  have hA : ContDiffOn ℝ ∞ A U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact ((contDiffOn_det_of_entries hg).sqrt (fun q hq => (hPos q hq).det_pos.ne')).mul
      (contDiffOn_inv_entry_of_entries hg (fun q hq => (hPos q hq).det_pos.ne') i j)
  obtain ⟨a,ha,haK,U',hU',hCU',hU'U,haE⟩ := exists_contDiff_extension_near_compact hU
    (hJ.prod (isCompact_closedBall (0 : X n) 1)) hCU hA
  obtain ⟨V,W,hV,hW,hJV,hCW,hVW⟩ := generalized_tube_lemma
    hJ (isCompact_closedBall (0 : X n) 1) hU' hCU'
  let K : Set (X n) := Prod.snd '' tsupport a
  have hK : IsCompact K := haK.isCompact.image continuous_snd
  have hAK (p : P) (z : X n) (hz : z ∉ K) : a (p,z) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (mem_image_of_mem Prod.snd h))
  have hPosA (p : P) (hp : p ∈ V) (z : X n) (hz : z ∈ closedBall (0 : X n) 1) :
      (a (p,z)).PosDef := by
    have hq := hVW (show (p,z) ∈ V ×ˢ W from ⟨hp,hCW hz⟩)
    rw [haE hq]
    exact divergenceMatrix_posDef (fun x => g (p,x)) z (hPos _ (hU'U hq))
  have hEll (p : P) (hp : p ∈ V) : ∃ lo hi,
      TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) lo hi :=
    exists_uniformEllipticOn_fixedBall (fun z => a (p,z))
      (ha.continuous.comp (continuous_const.prodMk continuous_id)) (fun z hz => hPosA p hp z hz)
  choose l L hEL using hEll
  classical
  let lo (p : P) := if hp : p ∈ V then l p hp else 1
  let hi (p : P) := if hp : p ∈ V then L p hp else 1
  let F : SupportedBallFamily P n :=
    { a := a, smooth := ha, K := K, compact := hK, support := hAK,
      V := V, openV := hV, lo := lo, hi := hi,
      elliptic := fun p hp => by simpa only [lo,hi,dite_eq_left hp] using hEL p hp,
      symmetry := fun p hp z hz => (hPosA p hp z (ball_subset_closedBall hz)).isHermitian.isSymm }
  refine ⟨F,W,hJV,hW,hCW,hVW.trans hU'U,fun p hp z hz i j => ?_⟩
  exact congrArg (fun M : Mat n => M i j) (haE (hVW ⟨hp,hz⟩))

end CalderonPaper.LowerGreen

end
