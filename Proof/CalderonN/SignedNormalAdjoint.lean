module

public import Proof.CalderonN.MovingBallFamilies

import Proof.CalderonN.NormalizedVelocityAtZero
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

/-! Adapted from `SignedNormalAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 3500000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- Dilation, center, signed radius and coordinate gradient of the radius. -/
abbrev SignedNormalParameter (dim : ℕ) := ℝ × ((X dim) × (ℝ × ((I dim) → ℝ)))

@[expose] def signedNormalMetric (g : ℝ → (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim))
    (q : (SignedNormalParameter dim) × (X dim)) : (Mat dim) :=
  normalizedBallMetric (g q.1.1) (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2.1 q.2

@[expose] def signedNormalVelocity (γ : ℝ → (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim))
    (i : (I dim)) (q : (SignedNormalParameter dim) × (X dim)) : (X dim) :=
  scaledNormalTraceVelocity (γ q.1.1) (E q.1.1) (e q.1.1)
    q.1.2.1 q.1.2.2.1 (q.1.2.2.2 i) q.2 (axis i)

@[expose] def signedNormalNondegenerate (E : ℝ → (X dim) × (X dim) → (X dim)) (e : ℝ → (Frame dim)) :
    Set ((SignedNormalParameter dim) × (X dim)) :=
  {q | (coordinateMatrix (normalizedBallDerivative (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2.1 q.2)).det ≠ 0}

@[expose] def signedNormalFirstAdjoint (γ g : ℝ → (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (e : ℝ → (Frame dim)) (j : (I dim)) : (SignedNormalParameter dim) × (X dim) → ℝ :=
  parametricBallVelocityAdjoint (signedNormalMetric g E e) (signedNormalVelocity γ E e j) (fun _ => 1)

@[expose] def signedNormalAdjointRemainder (γ g : ℝ → (MetricField dim)) (E : ℝ → (X dim) × (X dim) → (X dim))
    (e : ℝ → (Frame dim)) (i j : (I dim)) (q : (SignedNormalParameter dim) × (X dim)) : ℝ :=
  parametricBallVelocityAdjoint (signedNormalMetric g E e) (signedNormalVelocity γ E e i)
    (signedNormalFirstAdjoint γ g E e j) q - q.1.2.2.2 i * signedNormalFirstAdjoint γ g E e j q

variable {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}

private def signedNormalForgetGradient
    (q : (SignedNormalParameter dim) × (X dim)) : ℝ × ((X dim) × (ℝ × (X dim))) :=
  (q.1.1,(q.1.2.1,(q.1.2.2.1,q.2)))

private theorem contDiff_signedNormalForgetGradient :
    ContDiff ℝ ∞ (signedNormalForgetGradient (dim := dim)) :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
    (contDiff_fst.snd.snd.fst.prodMk contDiff_snd))

theorem signedNormalNondegenerate_isOpen
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i)) :
    IsOpen (signedNormalNondegenerate E e) := by
  let A (q : (SignedNormalParameter dim) × (X dim)) := coordinateMatrix
    (normalizedBallDerivative (E q.1.1) (e q.1.1) q.1.2.1 q.1.2.2.1 q.2)
  have hA (i j : (I dim)) : ContDiff ℝ ∞ (fun q => A q i j) :=
    (contDiff_normalizedBallDerivative_family_entry hE he i j).comp contDiff_signedNormalForgetGradient
  exact isOpen_ne_fun
    (contDiffOn_univ.mp (contDiffOn_det_of_entries (fun i j => (hA i j).contDiffOn))).continuous
    continuous_const

theorem contDiff_signedNormalMetric_entry
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i)) (i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : (SignedNormalParameter dim) × (X dim) => signedNormalMetric g E e q i j) := by
  let f (q : ℝ × ((X dim) × (ℝ × (X dim)))) :=
    normalizedBallMetric (g q.1) (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2 i j
  have hf : ContDiff ℝ ∞ f := contDiff_normalizedBallMetric_family_entry hE he hg i j
  change ContDiff ℝ ∞ (f ∘ signedNormalForgetGradient)
  exact hf.comp contDiff_signedNormalForgetGradient

theorem signedNormalMetric_posDef (hg : ∀ lam y, (g lam y).PosDef)
    {q : (SignedNormalParameter dim) × (X dim)} (hq : q ∈ signedNormalNondegenerate E e) :
    (signedNormalMetric g E e q).PosDef :=
  normalizedBallMetric_posDef (hg _ _) hq

theorem contDiffOn_signedNormalVelocity
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i)) (i : (I dim)) :
    ContDiffOn ℝ ∞ (signedNormalVelocity γ E e i) (signedNormalNondegenerate E e) := by
  let T (q : (SignedNormalParameter dim) × (X dim)) : (NormalVelocityParameter dim) :=
    (q.1.1,(q.1.2.1,(q.1.2.2.1,(q.1.2.2.2 i,q.2))))
  let U : Set (NormalVelocityParameter dim) := {q |
    (coordinateMatrix (normalizedBallDerivative (E q.1) (e q.1)
      q.2.1 q.2.2.1 q.2.2.2.2)).det ≠ 0}
  have hTi : ContDiff ℝ ∞ (fun q : (SignedNormalParameter dim) × (X dim) => q.1.2.2.2 i) :=
    (contDiff_apply ℝ ℝ i).comp contDiff_fst.snd.snd.snd
  have hT : ContDiff ℝ ∞ T := contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.fst.prodMk
      (hTi.prodMk contDiff_snd)))
  let F (q : (NormalVelocityParameter dim)) := scaledNormalTraceVelocity (γ q.1) (E q.1)
    (e q.1) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 (axis i)
  have hf : ContDiffOn ℝ ∞ F U :=
    contDiffOn_scaledNormalTraceVelocity_family hγ hγPos hE he (axis i) (fun _ hq => hq)
  change ContDiffOn ℝ ∞ (F ∘ T) (signedNormalNondegenerate E e)
  exact hf.comp hT.contDiffOn (fun _ hq => hq)

/-- Positive admissible radii and the limiting radius zero belong to the
same open coefficient domain. -/
theorem signedNormalNondegenerate_of_nonneg_radius
    {lam : ℝ} {y : (X dim)} {s ρ : ℝ} (b : (I dim) → ℝ) {Y Ω : Set (X dim)}
    (hE : ContDiff ℝ ∞ (E lam))
    (hN : NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ)) (hy : y ∈ Y)
    (he : ∀ i j, metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (hs : s ∈ Ico 0 ρ) :
    {(lam,(y,(s,b)))} ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e := by
  rintro ⟨p,w⟩ hp
  obtain ⟨hp,hw⟩ := hp
  rw [mem_singleton_iff] at hp
  change p = (lam,(y,(s,b))) at hp
  subst p
  change (coordinateMatrix (normalizedBallDerivative (E lam) (e lam) y s w)).det ≠ 0
  rcases hs.1.eq_or_lt with hzero | hpos
  · subst s
    exact normalizedBallDerivative_det_at_zero hE hN hy he w
  · obtain ⟨_,_,hBij⟩ := normalBallChartMap_on_openBall hE hN hy he hpos
    have hC : closedBall (0 : (X dim)) 1 ⊆ ball 0 (ρ/s) :=
      closedBall_subset_ball ((lt_div_iff₀ hpos).2 (by simpa using hs.2))
    exact normalizedBallDerivative_det_ne_zero hE (e lam) y (hBij w (hC hw))

/-- Both successive angular adjoints are smooth on fixed neighborhoods
of every admissible parameter, including a neighborhood of radius zero. -/
theorem exists_smooth_signedNormalAdjoints
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i))
    (p : (SignedNormalParameter dim))
    (hp : {p} ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e) (i j : (I dim)) :
    ∃ W : Set (SignedNormalParameter dim), IsOpen W ∧ p ∈ W ∧
      ContDiffOn ℝ ∞ (signedNormalFirstAdjoint γ g E e j) (W ×ˢ ({0}ᶜ : Set (X dim))) ∧
      ContDiffOn ℝ ∞ (signedNormalAdjointRemainder γ g E e i j) (W ×ˢ ({0}ᶜ : Set (X dim))) := by
  let U := signedNormalNondegenerate E e
  let N : Set (X dim) := ({0}ᶜ : Set (X dim))
  have hU : IsOpen U := signedNormalNondegenerate_isOpen hE he
  have hN : IsOpen N := isClosed_singleton.isOpen_compl
  have hS : {p} ×ˢ (standardSphere dim) ⊆ U :=
    fun q hq => hp ⟨hq.1,sphere_subset_closedBall hq.2⟩
  have hm (i j : (I dim)) := (contDiff_signedNormalMetric_entry hg hE he i j).contDiffOn (s := U)
  have hmPos (q : (SignedNormalParameter dim) × (X dim)) (hq : q ∈ U) := signedNormalMetric_posDef hgPos hq
  have hV (k : (I dim)) := contDiffOn_signedNormalVelocity hγ hγPos hE he k
  obtain ⟨J,hJ,hpJ,hα⟩ := exists_contDiffOn_parametricBallVelocityAdjoint
    hU hU p hp hS hm hmPos (hV j) contDiffOn_const
  let T := U ∩ J ×ˢ N
  have hT : IsOpen T := hU.inter (hJ.prod hN)
  have hST : {p} ×ˢ (standardSphere dim) ⊆ T := by
    intro q hq
    refine ⟨hS hq,mem_singleton_iff.mp hq.1 ▸ hpJ,?_⟩
    have hn := mem_sphere_zero_iff_norm.mp hq.2
    change q.2 ≠ 0
    intro hz
    simp [hz] at hn
  obtain ⟨L,hL,hpL,hβ⟩ := exists_contDiffOn_parametricBallVelocityAdjoint hU hT p hp hST
    hm hmPos ((hV i).mono inter_subset_left) (hα.mono inter_subset_right)
  let W := J ∩ L
  have hα' : ContDiffOn ℝ ∞ (signedNormalFirstAdjoint γ g E e j) (W ×ˢ N) :=
    hα.mono (fun _ hq => ⟨hq.1.1,hq.2⟩)
  have hb : ContDiff ℝ ∞ (fun q : (SignedNormalParameter dim) × (X dim) => q.1.2.2.2 i) :=
    (contDiff_apply ℝ ℝ i).comp contDiff_fst.snd.snd.snd
  refine ⟨W,hJ.inter hL,⟨hpJ,hpL⟩,hα',?_⟩
  exact (hβ.mono (fun _ hq => ⟨hq.1.2,hq.2⟩)).sub (hb.contDiffOn.mul hα')

end CalderonN
