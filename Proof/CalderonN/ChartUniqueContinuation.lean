module

public import Proof.CalderonN.GreenCross

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.UniqueContinuation
import Proof.CalderonN.HarmonicL2Space
import Proof.CalderonN.MetricDivergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic.Ring

public section

noncomputable section
open Set Filter
open scoped ContDiff BigOperators Topology Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Weak unique continuation for the actual chart Laplace--Beltrami
operator. The divergence coefficient includes the metric volume. -/
theorem harmonic_eq_zero_of_eqOn_open {U V : Set (X dim)}
    (hU : IsOpen U) (hconn : IsConnected U) (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {u : (X dim) → ℝ} (hu : Harmonic U g u)
    (hz : EqOn u 0 V) : EqOn u 0 U := by
  let A (x : (X dim)) : (Mat dim) := fun i j => divergenceCoeff g x i j
  have hA : ContDiffOn ℝ ∞ A U :=
    contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => contDiffOn_divergenceCoeff hg i j
  have hpos (x : (X dim)) (hx : x ∈ U) : (A x).PosDef :=
    (hg.2 x hx).inv.smul (Real.sqrt_pos.mpr (hg.2 x hx).det_pos)
  have hP (x : (X dim)) (hx : x ∈ U) : Carleman.divCoeffGrad A u x = 0 := by
    change (∑ i, coordDeriv i (fun z => divergenceFlux g u z i) x) = 0
    rw [← chartVolume_mul_laplace_eq_divergence hU hg hu.1 hx, hu.2 x hx, mul_zero]
  exact Carleman.uniqueContinuation (d := dim) U hU hconn A hA hpos u hu.1 hP V hV hVne hVU hz

theorem harmonic_eqOn_of_eqOn_open {U V : Set (X dim)}
    (hU : IsOpen U) (hconn : IsConnected U) (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {u v : (X dim) → ℝ}
    (hu : Harmonic U g u) (hv : Harmonic U g v) (heq : EqOn u v V) : EqOn u v U := by
  have hz := harmonic_eq_zero_of_eqOn_open hU hconn hV hVne hVU hg (hu.sub hU hv)
    (fun x hx => sub_eq_zero.mpr (heq hx))
  exact fun x hx => sub_eq_zero.mp (hz hx)

theorem ProductSolutionOn.harmonic_left {A B : Set (X dim)} {g₁ g₂ : (MetricField dim)} {F : (X dim) × (X dim) → ℝ}
    (h : ProductSolutionOn g₁ g₂ (A ×ˢ B) F) {y : (X dim)} (hy : y ∈ B) :
    Harmonic A g₁ (fun x => F (x, y)) :=
  ⟨h.1.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => ⟨hx, hy⟩),
    fun x hx => h.2.1 (x, y) ⟨hx, hy⟩⟩

theorem ProductSolutionOn.harmonic_right {A B : Set (X dim)} {g₁ g₂ : (MetricField dim)} {F : (X dim) × (X dim) → ℝ}
    (h : ProductSolutionOn g₁ g₂ (A ×ˢ B) F) {x : (X dim)} (hx : x ∈ A) :
    Harmonic B g₂ (fun y => F (x, y)) :=
  ⟨h.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => ⟨hx, hy⟩),
    fun y hy => h.2.2 (x, y) ⟨hx, hy⟩⟩

theorem product_eqOn_of_rectangle {A B A₀ B₀ : Set (X dim)}
    (hA : IsOpen A) (hAc : IsConnected A) (hB : IsOpen B) (hBc : IsConnected B)
    (hA₀ : IsOpen A₀) (hB₀ : IsOpen B₀) (hAne : A₀.Nonempty) (hBne : B₀.Nonempty)
    (hAsub : A₀ ⊆ A) (hBsub : B₀ ⊆ B)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric A g₁) (hg₂ : SmoothMetric B g₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ (A ×ˢ B) F)
    (hG : ProductSolutionOn g₁ g₂ (A ×ˢ B) G) (heq : EqOn F G (A₀ ×ˢ B₀)) :
    EqOn F G (A ×ˢ B) := by
  have hleft (y : (X dim)) (hy : y ∈ B₀) : EqOn (fun x => F (x, y)) (fun x => G (x, y)) A :=
    harmonic_eqOn_of_eqOn_open hA hAc hA₀ hAne hAsub hg₁
      (hF.harmonic_left (hBsub hy)) (hG.harmonic_left (hBsub hy)) (fun x hx => heq ⟨hx, hy⟩)
  intro q hq
  exact harmonic_eqOn_of_eqOn_open hB hBc hB₀ hBne hBsub hg₂
    (hF.harmonic_right hq.1) (hG.harmonic_right hq.1)
    (fun y hy => hleft y hy hq.1) hq.2

/-- A product solution is determined on a connected open region by its
germ on any nonempty open part. The proof applies the two scalar
continuation theorems on each product box. -/
theorem product_eqOn_of_eqOn_open {Ω₁ Ω₂ : Set (X dim)} {U V : Set ((X dim) × (X dim))}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hprod : U ⊆ Ω₁ ×ˢ Ω₂)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric Ω₁ g₁) (hg₂ : SmoothMetric Ω₂ g₂)
    {F G : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ U F) (hG : ProductSolutionOn g₁ g₂ U G)
    (hfg : EqOn F G V) : EqOn F G U := by
  let Z := {q : (X dim) × (X dim) | F =ᶠ[𝓝 q] G}
  have hZ : IsOpen Z := isOpen_iff_mem_nhds.mpr fun x hx => eventually_eventually_nhds.mpr hx
  have hVZ : V ⊆ Z := fun x hx => Filter.mem_of_superset (hV.mem_nhds hx) hfg
  have hclose : U ∩ closure Z ⊆ Z := by
    intro q hq
    obtain ⟨r, hr, hbig⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq.1)
    let A := Metric.ball q.1 r
    let B := Metric.ball q.2 r
    have hbox : A ×ˢ B ⊆ U := by
      change Metric.ball q.1 r ×ˢ Metric.ball q.2 r ⊆ U
      rw [ball_prod_same]
      exact hbig
    have hA : IsOpen A := Metric.isOpen_ball
    have hB : IsOpen B := Metric.isOpen_ball
    have hqA : q.1 ∈ A := Metric.mem_ball_self hr
    have hqB : q.2 ∈ B := Metric.mem_ball_self hr
    have hboxnb := (hA.prod hB).mem_nhds (show q ∈ A ×ˢ B from ⟨hqA, hqB⟩)
    obtain ⟨p, hpZ, hpbox⟩ :=
      ((mem_closure_iff_frequently.mp hq.2).and_eventually hboxnb).exists
    have hnb : (A ×ˢ B) ∩ {p : (X dim) × (X dim) | F p = G p} ∈ 𝓝 p :=
      inter_mem ((hA.prod hB).mem_nhds hpbox) hpZ
    obtain ⟨s, hs, hsmall⟩ := Metric.mem_nhds_iff.mp hnb
    let A₀ := Metric.ball p.1 s
    let B₀ := Metric.ball p.2 s
    have hsub : A₀ ×ˢ B₀ ⊆ (A ×ˢ B) ∩ {p : (X dim) × (X dim) | F p = G p} := by
      change Metric.ball p.1 s ×ˢ Metric.ball p.2 s ⊆ _
      rw [ball_prod_same]
      exact hsmall
    have hAs : A₀ ⊆ A := fun x hx => (hsub (show (x, p.2) ∈ A₀ ×ˢ B₀ from
      ⟨hx, Metric.mem_ball_self hs⟩)).1.1
    have hBs : B₀ ⊆ B := fun y hy => (hsub (show (p.1, y) ∈ A₀ ×ˢ B₀ from
      ⟨Metric.mem_ball_self hs, hy⟩)).1.2
    have ha : A ⊆ Ω₁ := fun x hx => (hprod (hbox (show (x, q.2) ∈ A ×ˢ B from ⟨hx, hqB⟩))).1
    have hb : B ⊆ Ω₂ := fun y hy => (hprod (hbox (show (q.1, y) ∈ A ×ˢ B from ⟨hqA, hy⟩))).2
    have hboxeq : EqOn F G (A ×ˢ B) := product_eqOn_of_rectangle
      hA (Metric.isConnected_ball hr) hB (Metric.isConnected_ball hr)
      Metric.isOpen_ball Metric.isOpen_ball ⟨_, Metric.mem_ball_self hs⟩ ⟨_, Metric.mem_ball_self hs⟩
      hAs hBs ⟨fun i j => (hg₁.1 i j).mono ha, fun x hx => hg₁.2 x (ha hx)⟩
      ⟨fun i j => (hg₂.1 i j).mono hb, fun y hy => hg₂.2 y (hb hy)⟩
      (hF.mono hbox) (hG.mono hbox) (fun _ hp => (hsub hp).2)
    exact Filter.mem_of_superset hboxnb hboxeq
  have hcover : U ⊆ Z ∪ (closure Z)ᶜ := fun x hx =>
    or_iff_not_imp_right.mpr (fun hn => hclose ⟨hx, not_not.mp hn⟩)
  have hdis : U ∩ (Z ∩ (closure Z)ᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun _ hx => hx.2.2 (subset_closure hx.2.1)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hUc) Z (closure Z)ᶜ
    hZ isClosed_closure.isOpen_compl hcover hdis with h | h
  · exact fun x hx => (h hx).eq_of_nhds
  · obtain ⟨x, hx⟩ := hVne
    exact ((h (hVU hx)) (subset_closure (hVZ hx))).elim

end CalderonN
