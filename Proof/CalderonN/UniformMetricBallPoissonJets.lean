module

public import Proof.CalderonN.UniformBallPoissonJets
public import Proof.CalderonN.ParametricBallConormal

import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

/-! Adapted from `UniformMetricBallPoissonJets` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open CalderonN.BallDirichlet

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The uniform estimates for the coefficient-field Poisson operator
also give estimates for representatives of the actual metric solution. -/
theorem exists_uniform_metricBallPoisson_jet_bounds
    (s : ℕ) {U : Set (P × (X dim))} (hU : IsOpen U) {J : Set P} (hJ : IsCompact J)
    (hJU : J ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) :
    ∃ V : Set P, IsOpen V ∧ J ⊆ V ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (d : P × (X dim) → ℝ) (hd : ContDiff ℝ ∞ d) (L : Set (X dim)) (hL : IsCompact L),
      (∀ p z, z ∉ L → d (p,z) = 0) →
      ∃ b : P → (X dim) → ℝ,
      (∀ p, ContDiff ℝ ∞ (b p)) ∧
      (∀ p ∈ V, FixedBallSolution (fun z => g (p,z)) (fun z => d (p,z)) (b p)) ∧
      (∀ p ∈ V, ∃ W : Set (X dim), IsOpen W ∧ closedBall (0 : (X dim)) 1 ⊆ W ∧
        SmoothMetric W (fun z => g (p,z))) ∧
      (∀ k : ℕ, k ≤ s → ∀ z ∈ closedBall (0 : (X dim)) 1,
        ContDiffOn ℝ ∞ (fun p => iteratedFDeriv ℝ k (b p) z) V) ∧
      ∀ p ∈ J, ∀ v M N, 0 ≤ M → 0 ≤ N →
        (∀ k : ℕ, k ≤ s+dim+2 → ∀ z, ‖iteratedFDeriv ℝ k (fun x => d (p,x)) z‖ ≤ M) →
        (∀ k : ℕ, k ≤ s+dim+2 → ∀ z,
          ‖fderiv ℝ (fun q : P => iteratedFDeriv ℝ k (fun x => d (q,x)) z) p v‖ ≤ N) →
        ∀ k : ℕ, k ≤ s → ∀ z ∈ closedBall (0 : (X dim)) 1,
          ‖iteratedFDeriv ℝ k (b p) z‖ ≤ C*M ∧
          ‖fderiv ℝ (fun q => iteratedFDeriv ℝ k (b q) z) p v‖ ≤ C*(N+M*‖v‖) := by
  classical
  let C := closedBall (0 : (X dim)) 1
  let A (q : P × (X dim)) : (Mat dim) := fun i j => divergenceCoeff (fun z => g (q.1,z)) q.2 i j
  have hA : ContDiffOn ℝ ∞ A U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact ((contDiffOn_det_of_entries hg).sqrt (fun q hq => (hPos q hq).det_pos.ne')).mul
      (contDiffOn_inv_entry_of_entries hg (fun q hq => (hPos q hq).det_pos.ne') i j)
  obtain ⟨a,ha,haK,U',hU',hCU',hU'U,haE⟩ := exists_contDiff_extension_near_compact hU
    (hJ.prod (isCompact_closedBall (0 : (X dim)) 1)) hJU hA
  obtain ⟨V,W,hV,hW,hJV,hCW,hVW⟩ := generalized_tube_lemma
    hJ (isCompact_closedBall (0 : (X dim)) 1) hU' hCU'
  let K : Set (X dim) := Prod.snd '' tsupport a
  have hK : IsCompact K := haK.isCompact.image continuous_snd
  have hAK (p : P) (z : (X dim)) (hz : z ∉ K) : a (p,z) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (mem_image_of_mem Prod.snd h))
  have hEll (p : P) (hp : p ∈ V) : ∃ lo hi,
      TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (fun z => a (p,z)) lo hi :=
    exists_uniformEllipticOn_fixedBall (fun z => a (p,z))
      (ha.continuous.comp (continuous_const.prodMk continuous_id)) (by
        intro z hz
        have ht := hVW (show (p,z) ∈ V ×ˢ W from ⟨hp,hCW hz⟩)
        rw [haE ht]
        exact divergenceMatrix_posDef (fun x => g (p,x)) z (hPos (p,z) (hU'U ht)))
  choose l L hEL using hEll
  let lo (p : P) := if hp : p ∈ V then l p hp else 1
  let hi (p : P) := if hp : p ∈ V then L p hp else 1
  obtain ⟨B,hB,hP⟩ := exists_uniform_ballPoisson_replacement_jet_bounds s a ha K hK hAK
    hV hJ hJV lo hi (fun p hp => by simpa only [lo,hi,dite_eq_left hp] using hEL p hp)
  have hgW (p : P) (hp : p ∈ V) : SmoothMetric W (fun x => g (p,x)) :=
    ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => hU'U (hVW ⟨hp,hx⟩)),fun x hx => hPos _ (hU'U (hVW ⟨hp,hx⟩))⟩
  refine ⟨V,hV,hJV,B,hB,?_⟩
  intro d hd S hS hSupp
  obtain ⟨b,hb,hbA,hbJ,hEst⟩ := hP d hd S hS hSupp
  refine ⟨b,hb,?_,fun p hp => ⟨W,hW,hCW,hgW p hp⟩,hbJ,hEst⟩
  intro p hp
  refine ⟨hb p,(hbA p hp).1,?_⟩
  intro z hz
  have hAE (x : (X dim)) (hx : x ∈ W) (i j : (I dim)) :
      a (p,x) i j = divergenceCoeff (fun z => g (p,z)) x i j := by
    have he : a (p,x) = A (p,x) := haE (hVW ⟨hp,hx⟩)
    exact congrArg (fun M : (Mat dim) => M i j) he
  have hzW : z ∈ W := hCW (ball_subset_closedBall hz)
  have hDg := negativeBallDivergence_eq_neg_laplace hW (hgW p hp) hAE (hb p).contDiffOn hzW
  have hZero : negativeBallDivergence (fun x => a (p,x)) (b p) z = 0 := (hbA p hp).2 hz
  rw [hZero] at hDg
  exact (mul_eq_zero.mp (neg_eq_zero.mp hDg.symm)).resolve_left
    (Real.sqrt_pos.mpr ((hgW p hp).2 z hzW).det_pos).ne'

end CalderonN
