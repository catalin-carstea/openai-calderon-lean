module

public import Proof.CalderonN.ParametricClassicalBallRepresentative
public import Proof.CalderonN.MetricBallDirichlet

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

/-! Adapted from `ParametricMetricBallDirichlet` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]



variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

set_option maxHeartbeats 1500000 in
/-- A nonhomogeneous smooth boundary family is solved by subtracting a
smooth extension of its data and using the zero-Dirichlet inverse. -/
theorem exists_parametric_classical_ballDirichlet
    {V : Set P} (hV : IsOpen V)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (d : P × (X dim) → ℝ) (hd : ContDiff ℝ ∞ d)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ∃ b : P → (X dim) → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
      (∀ p ∈ V, EqOn (b p) (fun z => d (p,z)) (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => a (p,z)) (b p)) 0 (ball (0 : (X dim)) 1)) ∧
      ContDiffOn ℝ ∞ (fun q : P × (X dim) => b q.1 q.2) (V ×ˢ closedBall (0 : (X dim)) 1) ∧
      ContDiffOn ℝ ∞ (fun q : P × (X dim) => fderiv ℝ (b q.1) q.2) (V ×ˢ closedBall (0 : (X dim)) 1) := by
  let f (q : P × (X dim)) := -negativeBallDivergence (fun z => a (q.1,z)) (fun z => d (q.1,z)) q.2
  have hf : ContDiff ℝ ∞ f := (contDiff_negativeBallDivergence_family ha hd).neg
  have hfSupp (p : P) (z : (X dim)) (hz : z ∉ K) : f (p,z) = 0 := by
    have he (i : (I dim)) : (fun x => ∑ j : (I dim), a (p,x) i j * coordDeriv j (fun v => d (p,v)) x)
        =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with x hx
      simp [hSupp p x hx]
    have hD (i : (I dim)) : coordDeriv i (fun x => ∑ j : (I dim),
        a (p,x) i j * coordDeriv j (fun v => d (p,v)) x) z = 0 := by
      rw [coordDeriv,(he i).fderiv_eq]
      simp
    simp only [f,negativeBallDivergence,Elliptic.Lop,Elliptic.pd,hD,Finset.sum_const_zero,neg_zero]
  obtain ⟨u,hu,hP,hJ⟩ := exists_parametric_classical_zeroDirichlet hV
    a ha K hK hSupp f hf K hK hfSupp lo hi hEll
  let b (p : P) (x : (X dim)) := u p x + d (p,x)
  let C := closedBall (0 : (X dim)) 1
  have hds (p : P) : ContDiff ℝ ∞ (fun x => d (p,x)) := hd.comp (contDiff_const.prodMk contDiff_id)
  have h₀ : ContDiffOn ℝ ∞ (fun q : P × (X dim) => u q.1 q.2) (V ×ˢ C) := by
    have h := (continuousMultilinearCurryFin0 ℝ (X dim) ℝ).contDiff.comp_contDiffOn (hJ 0)
    apply h.congr
    intro q _
    change u q.1 q.2 = (iteratedFDeriv ℝ 0 (u q.1) q.2).curry0
    simp [ContinuousMultilinearMap.curry0]
  have h₁ : ContDiffOn ℝ ∞ (fun q : P × (X dim) => fderiv ℝ (u q.1) q.2) (V ×ˢ C) := by
    have h := (continuousMultilinearCurryFin1 ℝ (X dim) ℝ).contDiff.comp_contDiffOn (hJ 1)
    apply h.congr
    intro q _
    ext v
    exact (iteratedFDeriv_one_apply (f := u q.1) (x := q.2) (fun _ => v)).symm
  refine ⟨b,fun p => (hu p).add (hds p),fun p hp => ?_,h₀.add hd.contDiffOn,?_⟩
  · constructor
    · intro x hx
      change u p x + d (p,x) = _
      rw [show u p x = 0 from (hP p hp).1 hx,zero_add]
    · intro x hx
      let D := fun z : (X dim) => d (p,z)
      let A := fun z : (X dim) => a (p,z)
      have hA : ContDiff ℝ ∞ A := ha.comp (contDiff_const.prodMk contDiff_id)
      change negativeBallDivergence A (u p+D) x = 0
      rw [negativeBallDivergence_add hA (hu p) (hds p),(hP p hp).2 hx]
      exact neg_add_cancel _
  have hd' (p : P) (x : (X dim)) : fderiv ℝ (fun z => d (p,z)) x =
      (fderiv ℝ d (p,x)).comp (ContinuousLinearMap.inr ℝ P (X dim)) := by
    exact ((hd.differentiable (by simp) (p,x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right p x)).fderiv
  have hD' : ContDiff ℝ ∞ (fun q : P × (X dim) => fderiv ℝ (fun z => d (q.1,z)) q.2) := by
    simp only [hd']
    exact (hd.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  refine (h₁.add hD'.contDiffOn).congr (fun q _ => ?_)
  exact fderiv_fun_add ((hu q.1).differentiable (by simp) q.2)
    ((hds q.1).differentiable (by simp) q.2)

/-- Local smooth dependence on a metric and boundary family known near
the ball and the sphere respectively. The solution on each slice is
smooth on an ambient neighborhood of the closed ball. -/
theorem exists_local_parametric_metricBallDirichlet
    {U T : Set (P × (X dim))} (hU : IsOpen U) (hT : IsOpen T) (p₀ : P)
    (hCU : {p₀} ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    (hST : {p₀} ×ˢ (standardSphere dim) ⊆ T)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) {d : P × (X dim) → ℝ} (hd : ContDiffOn ℝ ∞ d T) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧
      ∃ b : P → (X dim) → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
        (∀ p ∈ V, EqOn (b p) (fun z => d (p,z)) (standardSphere dim) ∧
          ∀ z ∈ ball (0 : (X dim)) 1, laplace (fun x => g (p,x)) (b p) z = 0) ∧
        ContDiffOn ℝ ∞ (fun q : P × (X dim) => b q.1 q.2) (V ×ˢ closedBall (0 : (X dim)) 1) ∧
        ContDiffOn ℝ ∞ (fun q : P × (X dim) => fderiv ℝ (b q.1) q.2) (V ×ˢ closedBall (0 : (X dim)) 1) := by
  classical
  let C := closedBall (0 : (X dim)) 1
  let S := (standardSphere dim)
  let A (q : P × (X dim)) : (Mat dim) := fun i j => divergenceCoeff (fun z => g (q.1,z)) q.2 i j
  have hA : ContDiffOn ℝ ∞ A U := by
    apply contDiffOn_pi.mpr
    intro i
    apply contDiffOn_pi.mpr
    intro j
    exact ((contDiffOn_det_of_entries hg).sqrt (fun q hq => (hPos q hq).det_pos.ne')).mul
      (contDiffOn_inv_entry_of_entries hg (fun q hq => (hPos q hq).det_pos.ne') i j)
  obtain ⟨a,ha,haK,U',hU',hCU',hU'U,haE⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_singleton.prod (isCompact_closedBall (0 : (X dim)) 1)) hCU hA
  obtain ⟨d',hd',_,T',hT',hST',_,hdE⟩ := exists_contDiff_extension_near_compact hT
    (isCompact_singleton.prod (isCompact_sphere (0 : (X dim)) 1)) hST hd
  obtain ⟨V₁,W,hV₁,hW,hpW,hCW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p₀)) (isCompact_closedBall (0 : (X dim)) 1) hU' hCU'
  obtain ⟨V₂,Z,hV₂,hZ,hpZ,hSZ,hVZ⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p₀)) (isCompact_sphere (0 : (X dim)) 1) hT' hST'
  let V := V₁ ∩ V₂
  have hV : IsOpen V := hV₁.inter hV₂
  have hPW : V ×ˢ W ⊆ U' := fun q hq => hVW ⟨hq.1.1,hq.2⟩
  have hPZ : V ×ˢ Z ⊆ T' := fun q hq => hVZ ⟨hq.1.2,hq.2⟩
  let K : Set (X dim) := Prod.snd '' tsupport a
  have hK : IsCompact K := haK.isCompact.image continuous_snd
  have hAK (p : P) (z : (X dim)) (hz : z ∉ K) : a (p,z) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hz (mem_image_of_mem Prod.snd h))
  have hEll (p : P) (hp : p ∈ V) : ∃ lo hi,
      TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim)) (fun z => a (p,z)) lo hi :=
    exists_uniformEllipticOn_fixedBall (fun z => a (p,z))
      (ha.continuous.comp (continuous_const.prodMk continuous_id)) (by
        intro z hz
        have ht := hPW (show (p,z) ∈ V ×ˢ W from ⟨hp,hCW hz⟩)
        rw [haE ht]
        exact divergenceMatrix_posDef (fun x => g (p,x)) z (hPos (p,z) (hU'U ht)))
  choose l L hEL using hEll
  let lo (p : P) := if hp : p ∈ V then l p hp else 1
  let hi (p : P) := if hp : p ∈ V then L p hp else 1
  obtain ⟨b,hb,hB,hC,hD⟩ := exists_parametric_classical_ballDirichlet hV
    a ha K hK hAK d' hd' lo hi (fun p hp => by simpa only [lo,hi,dite_eq_left hp] using hEL p hp)
  refine ⟨V,hV,⟨hpW (mem_singleton _),hpZ (mem_singleton _)⟩,b,hb,fun p hp => ?_,hC,hD⟩
  refine ⟨fun z hz => ((hB p hp).1 hz).trans (hdE (hPZ ⟨hp,hSZ hz⟩)),fun z hz => ?_⟩
  have hBW : ball (0 : (X dim)) 1 ⊆ W := ball_subset_closedBall.trans hCW
  have hgW : SmoothMetric W (fun x => g (p,x)) := by
    refine ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x hx => hU'U (hPW ⟨hp,hx⟩)),fun x hx => hPos _ (hU'U (hPW ⟨hp,hx⟩))⟩
  have hAE (x : (X dim)) (hx : x ∈ W) (i j : (I dim)) :
      a (p,x) i j = divergenceCoeff (fun z => g (p,z)) x i j := by
    have he : a (p,x) = A (p,x) := haE (hPW ⟨hp,hx⟩)
    exact congrArg (fun M : (Mat dim) => M i j) he
  have hDg := negativeBallDivergence_eq_neg_laplace hW hgW hAE (hb p).contDiffOn (hBW hz)
  have hZero : negativeBallDivergence (fun x => a (p,x)) (b p) z = 0 := (hB p hp).2 hz
  rw [hZero] at hDg
  exact (mul_eq_zero.mp (neg_eq_zero.mp hDg.symm)).resolve_left
    (Real.sqrt_pos.mpr (hgW.2 z (hBW hz)).det_pos).ne'

end CalderonN
