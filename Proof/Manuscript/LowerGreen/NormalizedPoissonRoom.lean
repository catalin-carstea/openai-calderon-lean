module

public import Proof.CalderonN.MovingGreenConormalComparison

import Proof.CalderonN.SignedNormalAdjoint
import Mathlib.Tactic

public section

open Set Metric CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

/-- The normalized metric for the real unit ball is a smooth elliptic
family on a common neighborhood of the compact nonnegative-radius
parameters, including the flat normalization at radius zero. -/
theorem exists_open_normalGreenMetric_room
    {γ g : ℝ → MetricField n} {E : ℝ → (X n × X n) → X n} {e : ℝ → Frame n}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × X n => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × (X n × X n) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × X n => e q.1 q.2 i))
    {S : Set ℝ} {K Y Ω : Set (X n)} (hKY : K ⊆ Y) {ρ : ℝ} (hρ : 0 < ρ)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ S, ∀ y ∈ K, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i = j then 1 else 0) :
    let J : Set (NormalGreenParameter n) := S ×ˢ (K ×ˢ Icc 0 (ρ/2))
    ∃ U : Set (NormalGreenParameter n × X n), IsOpen U ∧
      J ×ˢ closedBall (0 : X n) 1 ⊆ U ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun q => normalGreenMetric g E e q i j) U) ∧
      ∀ q ∈ U, (normalGreenMetric g E e q).PosDef := by
  intro J
  let U' := signedNormalNondegenerate E e
  let I₀ (q : NormalGreenParameter n × X n) : SignedNormalParameter n × X n :=
    ((q.1.1,(q.1.2.1,(q.1.2.2,0))),q.2)
  have hI₀ : ContDiff ℝ ∞ I₀ :=
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.fst.prodMk
      (contDiff_fst.snd.snd.prodMk contDiff_const))).prodMk contDiff_snd
  let U := I₀ ⁻¹' U'
  refine ⟨U,(signedNormalNondegenerate_isOpen hE he).preimage hI₀.continuous,?_,?_,?_⟩
  · rintro ⟨⟨lam,y,s⟩,w⟩ ⟨⟨hl,hy,hs⟩,hw⟩
    have hAdmissible : {(lam,(y,(s,0)))} ×ˢ closedBall (0 : X n) 1 ⊆ U' :=
      signedNormalNondegenerate_of_nonneg_radius (0 : I n → ℝ)
        (hE.comp (contDiff_const.prodMk contDiff_id))
        (hNormal lam hl) (hKY hy) (hFrame lam hl y hy)
        ⟨hs.1,hs.2.trans_lt (half_lt_self hρ)⟩
    exact hAdmissible ⟨mem_singleton _,hw⟩
  · intro i j
    change ContDiffOn ℝ ∞ (fun q => signedNormalMetric g E e (I₀ q) i j) U
    exact ((contDiff_signedNormalMetric_entry hg hE he i j).comp hI₀).contDiffOn
  · intro q hq
    change (signedNormalMetric g E e (I₀ q)).PosDef
    exact signedNormalMetric_posDef (g := g) (E := E) (e := e) (q := I₀ q) hgPos hq

end CalderonPaper.LowerGreen
