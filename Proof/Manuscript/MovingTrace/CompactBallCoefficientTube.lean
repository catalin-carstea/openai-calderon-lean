module

public import Proof.CalderonN.ParametricMetricBallDirichlet
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 1800000

open CalderonN Set Metric
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPaper

variable {d : ℕ} [NeZero d] [Nontrivial (Fin d)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Fix one smooth compactly supported divergence coefficient for the
normal-ball family on a common neighborhood of the selected compact
parameter set and the closed unit ball. -/
theorem exists_compactBallCoefficient_tube
    {O : Set (P × X d)} (hO : IsOpen O) {J : Set P} (hJ : IsCompact J)
    (hCO : J ×ˢ closedBall (0:X d) 1 ⊆ O)
    (g : P × X d → Mat d) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) O)
    (hPos : ∀ q ∈ O, (g q).PosDef) :
    ∃ (V : Set P) (W : Set (X d)) (a : P × X d → Mat d) (Ka : Set (X d)) (lo hi : P → ℝ),
      IsOpen V ∧ IsOpen W ∧ J ⊆ V ∧ closedBall (0:X d) 1 ⊆ W ∧ V ×ˢ W ⊆ O ∧
      ContDiff ℝ ∞ a ∧ IsCompact Ka ∧ (∀ p z, z ∉ Ka → a (p,z) = 0) ∧
      (∀ q ∈ V ×ˢ W, ∀ i j, a q i j = divergenceCoeff (fun z => g (q.1,z)) q.2 i j) ∧
      ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens d : Set (X d))
        (fun z => a (p,z)) (lo p) (hi p) := by
  classical
  let A (q : P × X d) : Mat d := fun i j => divergenceCoeff (fun z => g (q.1,z)) q.2 i j
  have hA : ContDiffOn ℝ ∞ A O := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact ((contDiffOn_det_of_entries hg).sqrt (fun q hq => (hPos q hq).det_pos.ne')).mul
      (contDiffOn_inv_entry_of_entries hg (fun q hq => (hPos q hq).det_pos.ne') i j)
  obtain ⟨a,ha,haK,U,hU,hCU,hUO,haE⟩ := exists_contDiff_extension_near_compact hO
    (hJ.prod (isCompact_closedBall (0 : X d) 1)) hCO hA
  obtain ⟨V,W,hV,hW,hJV,hCW,hVW⟩ := generalized_tube_lemma hJ (isCompact_closedBall (0 : X d) 1) hU hCU
  let K := Prod.snd '' tsupport a
  have hK : IsCompact K := haK.isCompact.image continuous_snd
  have hAK (p : P) (z : X d) (hz : z ∉ K) : a (p,z) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (mem_image_of_mem Prod.snd h))
  have hEll (p : P) (hp : p ∈ V) : ∃ lo hi,
      TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens d : Set (X d)) (fun z => a (p,z)) lo hi :=
    exists_uniformEllipticOn_fixedBall (fun z => a (p,z))
      (ha.continuous.comp (continuous_const.prodMk continuous_id)) (by
        intro z hz
        have ht := hVW (show (p,z) ∈ V ×ˢ W from ⟨hp,hCW hz⟩)
        rw [haE ht]
        exact divergenceMatrix_posDef (fun x => g (p,x)) z (hPos (p,z) (hUO ht)))
  choose l L hEL using hEll
  let lo (p : P) := if hp : p ∈ V then l p hp else 1
  let hi (p : P) := if hp : p ∈ V then L p hp else 1
  refine ⟨V,W,a,K,lo,hi,hV,hW,hJV,hCW,hVW.trans hUO,ha,hK,hAK,?_,?_⟩
  · intro q hq i j
    exact congrArg (fun M : Mat d => M i j) (haE (hVW hq))
  · intro p hp
    simpa only [lo,hi,dite_eq_left hp] using hEL p hp

end CalderonPaper
