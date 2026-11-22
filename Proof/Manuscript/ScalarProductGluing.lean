module

public import Proof.Manuscript.ScalarCrossExtension

import Mathlib.Analysis.Normed.Module.Connected
import Proof.CalderonN.ProductGluing
import Mathlib.Tactic

public section

open Set Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

theorem ProductSolvesOn.mono {L₁ L₂ : ScalarElliptic n} {U V : Set (X n × X n)}
    {F : X n × X n → ℝ} (hF : L₁.ProductSolvesOn L₂ U F) (hVU : V ⊆ U) :
    L₁.ProductSolvesOn L₂ V F :=
  ⟨hF.1.mono hVU,fun z hz => hF.2.1 z (hVU hz),fun z hz => hF.2.2 z (hVU hz)⟩

/-- The scalar equation is local in the ordinary germ of the solution. -/
theorem apply_congr_of_eventuallyEq {L : ScalarElliptic n} {f g : X n → ℝ} {x : X n}
    (heq : f =ᶠ[𝓝 x] g) :
    L.apply f x = L.apply g x := by
  have h₁ (j : I n) : coordDeriv j f =ᶠ[𝓝 x] coordDeriv j g := by
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : X n →L[ℝ] ℝ => A (axis j)) hy
  have h₂ (i j : I n) :
      coordDeriv i (coordDeriv j f) x = coordDeriv i (coordDeriv j g) x :=
    congrArg (fun A : X n →L[ℝ] ℝ => A (axis i)) (h₁ j).fderiv_eq
  change (∑ i, ∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j f) x) +
    (∑ i, L.first x i * coordDeriv i f x) + L.zeroth x * f x =
      (∑ i, ∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j g) x) +
      (∑ i, L.first x i * coordDeriv i g x) + L.zeroth x * g x
  simp only [h₂, (h₁ _).eq_of_nhds, heq.eq_of_nhds]

/-- A smooth scalar product solution is unchanged by changing its
representative off the open set. -/
theorem ProductSolvesOn.congr {L₁ L₂ : ScalarElliptic n} {U : Set (X n × X n)}
    {F G : X n × X n → ℝ} (hF : L₁.ProductSolvesOn L₂ U F)
    (hU : IsOpen U) (hFG : EqOn G F U) : L₁.ProductSolvesOn L₂ U G := by
  refine ⟨hF.1.congr hFG,?_,?_⟩
  · intro z hz
    have hN : ∀ᶠ x in 𝓝 z.1, (x,z.2) ∈ U :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hz)
    have he : (fun x => G (x,z.2)) =ᶠ[𝓝 z.1] fun x => F (x,z.2) :=
      hN.mono fun _ hx => hFG hx
    rw [apply_congr_of_eventuallyEq he]
    exact hF.2.1 z hz
  · intro z hz
    have hN : ∀ᶠ y in 𝓝 z.2, (z.1,y) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hz)
    have he : (fun y => G (z.1,y)) =ᶠ[𝓝 z.2] fun y => F (z.1,y) :=
      hN.mono fun _ hy => hFG hy
    rw [apply_congr_of_eventuallyEq he]
    exact hF.2.2 z hz

/- The rectangle, connected-component, interval and union arguments use the
same geometry as the checked ChartUniqueContinuation and ProductGluing
modules, with the actual scalar unique-continuation theorem in each factor. -/
theorem scalar_product_eqOn_of_rectangle {A B A₀ B₀ : Set (X n)}
    (hA : IsOpen A) (hAc : IsConnected A) (hB : IsOpen B) (hBc : IsConnected B)
    (hA₀ : IsOpen A₀) (hB₀ : IsOpen B₀) (hAne : A₀.Nonempty) (hBne : B₀.Nonempty)
    (hAsub : A₀ ⊆ A) (hBsub : B₀ ⊆ B)
    {g₁ g₂ : ScalarElliptic n} (hg₁ : g₁.SmoothOn A) (hg₂ : g₂.SmoothOn B)
    {F G : (X n) × (X n) → ℝ} (hF : ProductSolvesOn g₁ g₂ (A ×ˢ B) F)
    (hG : ProductSolvesOn g₁ g₂ (A ×ˢ B) G) (heq : EqOn F G (A₀ ×ˢ B₀)) :
    EqOn F G (A ×ˢ B) := by
  have hleft (y : (X n)) (hy : y ∈ B₀) : EqOn (fun x => F (x, y)) (fun x => G (x, y)) A :=
    eqOn_of_solutions_eqOn_open hA hAc hA₀ hAne hAsub hg₁
      (hF.leftSlice (hBsub hy)) (hG.leftSlice (hBsub hy)) (fun x hx => heq ⟨hx, hy⟩)
  intro q hq
  exact eqOn_of_solutions_eqOn_open hB hBc hB₀ hBne hBsub hg₂
    (hF.rightSlice hq.1) (hG.rightSlice hq.1)
    (fun y hy => hleft y hy hq.1) hq.2

/-- A product solution is determined on a connected open region by its
germ on any nonempty open part. The proof applies the two scalar
continuation theorems on each product box. -/
theorem scalar_product_eqOn_of_eqOn_open {Ω₁ Ω₂ : Set (X n)} {U V : Set ((X n) × (X n))}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hprod : U ⊆ Ω₁ ×ˢ Ω₂)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U)
    {g₁ g₂ : ScalarElliptic n} (hg₁ : g₁.SmoothOn Ω₁) (hg₂ : g₂.SmoothOn Ω₂)
    {F G : (X n) × (X n) → ℝ} (hF : ProductSolvesOn g₁ g₂ U F) (hG : ProductSolvesOn g₁ g₂ U G)
    (hfg : EqOn F G V) : EqOn F G U := by
  let Z := {q : (X n) × (X n) | F =ᶠ[𝓝 q] G}
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
    have hnb : (A ×ˢ B) ∩ {p : (X n) × (X n) | F p = G p} ∈ 𝓝 p :=
      inter_mem ((hA.prod hB).mem_nhds hpbox) hpZ
    obtain ⟨s, hs, hsmall⟩ := Metric.mem_nhds_iff.mp hnb
    let A₀ := Metric.ball p.1 s
    let B₀ := Metric.ball p.2 s
    have hsub : A₀ ×ˢ B₀ ⊆ (A ×ˢ B) ∩ {p : (X n) × (X n) | F p = G p} := by
      change Metric.ball p.1 s ×ˢ Metric.ball p.2 s ⊆ _
      rw [ball_prod_same]
      exact hsmall
    have hAs : A₀ ⊆ A := fun x hx => (hsub (show (x, p.2) ∈ A₀ ×ˢ B₀ from
      ⟨hx, Metric.mem_ball_self hs⟩)).1.1
    have hBs : B₀ ⊆ B := fun y hy => (hsub (show (p.1, y) ∈ A₀ ×ˢ B₀ from
      ⟨Metric.mem_ball_self hs, hy⟩)).1.2
    have ha : A ⊆ Ω₁ := fun x hx => (hprod (hbox (show (x, q.2) ∈ A ×ˢ B from ⟨hx, hqB⟩))).1
    have hb : B ⊆ Ω₂ := fun y hy => (hprod (hbox (show (q.1, y) ∈ A ×ˢ B from ⟨hqA, hy⟩))).2
    have hboxeq : EqOn F G (A ×ˢ B) := scalar_product_eqOn_of_rectangle
      hA (Metric.isConnected_ball hr) hB (Metric.isConnected_ball hr)
      Metric.isOpen_ball Metric.isOpen_ball ⟨_, Metric.mem_ball_self hs⟩ ⟨_, Metric.mem_ball_self hs⟩
      hAs hBs (hg₁.restrict ha) (hg₂.restrict hb)
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


/-- Agreement at the initial point follows from one interval path
inside the overlap to an open region of agreement. -/
theorem scalar_product_eq_at_of_interval_to_seed
    {U V : Set ((X n) × (X n))}
    {A₁ A₂ : Set (X n)} (hU : IsOpen U) (hV : IsOpen V)
    (hsub : U ⊆ A₁ ×ˢ A₂)
    {g₁ g₂ : ScalarElliptic n} (hg₁ : g₁.SmoothOn A₁) (hg₂ : g₂.SmoothOn A₂)
    {F G : (X n) × (X n) → ℝ} (hF : ProductSolvesOn g₁ g₂ U F) (hG : ProductSolvesOn g₁ g₂ U G)
    (heq : EqOn F G V)
    {z : (X n) × (X n)} (hz : z ∈ U)
    (hpath : ∃ (a b : ℝ) (f : ℝ → (X n) × (X n)),
      ContinuousOn f (uIcc a b) ∧ f a = z ∧ MapsTo f (uIcc a b) U ∧ f b ∈ V) :
    F z = G z := by
  let C := connectedComponentIn U z
  have hC : IsOpen C := hU.connectedComponentIn
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hz
  have hCU : C ⊆ U := connectedComponentIn_subset U z
  obtain ⟨a, b, f, hf, hstart, hinside, hend⟩ := hpath
  have himg : f '' uIcc a b ⊆ C :=
    (isPreconnected_uIcc.image f hf).subset_connectedComponentIn
      ⟨a, left_mem_uIcc, hstart⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hinside ht)
  have hseed : (C ∩ V).Nonempty := ⟨f b, himg ⟨b, right_mem_uIcc, rfl⟩, hend⟩
  exact scalar_product_eqOn_of_eqOn_open hC hCconn.isPreconnected (hCU.trans hsub) (hC.inter hV) hseed
    inter_subset_left hg₁ hg₂ (hF.mono hCU) (hG.mono hCU) (fun q hq => heq hq.2)
    (mem_connectedComponentIn hz)

/-- Agreement on a common open seed propagates along actual interval
paths lying in the overlap. -/
theorem scalar_product_eqOn_of_interval_to_seed
    {U V : Set ((X n) × (X n))}
    {A₁ A₂ : Set (X n)} (hU : IsOpen U) (hV : IsOpen V)
    (hsub : U ⊆ A₁ ×ˢ A₂)
    {g₁ g₂ : ScalarElliptic n} (hg₁ : g₁.SmoothOn A₁) (hg₂ : g₂.SmoothOn A₂)
    {F G : (X n) × (X n) → ℝ} (hF : ProductSolvesOn g₁ g₂ U F) (hG : ProductSolvesOn g₁ g₂ U G)
    (heq : EqOn F G V)
    (hpath : ∀ z ∈ U, ∃ (a b : ℝ) (f : ℝ → (X n) × (X n)),
      ContinuousOn f (uIcc a b) ∧ f a = z ∧ MapsTo f (uIcc a b) U ∧ f b ∈ V) :
    EqOn F G U := by
  intro z hz
  exact scalar_product_eq_at_of_interval_to_seed hU hV hsub hg₁ hg₂ hF hG heq hz (hpath z hz)

/-- Compatible local solutions glue to a single product solution on the
actual union of their open domains. -/
theorem exists_scalar_productSolution_iUnion {ι : Type*} {g₁ g₂ : ScalarElliptic n}
    (U : ι → Set ((X n) × (X n))) (hU : ∀ i, IsOpen (U i))
    (F : ι → (X n) × (X n) → ℝ) (hF : ∀ i, ProductSolvesOn g₁ g₂ (U i) (F i))
    (hcompat : ∀ i j, EqOn (F i) (F j) (U i ∩ U j)) :
    ∃ G : (X n) × (X n) → ℝ, ProductSolvesOn g₁ g₂ (⋃ i, U i) G ∧ ∀ i, EqOn G (F i) (U i) := by
  classical
  let G (z : (X n) × (X n)) := if h : ∃ i, z ∈ U i then F (Classical.choose h) z else 0
  have heq (i : ι) : EqOn G (F i) (U i) := by
    intro z hz
    have h : ∃ j, z ∈ U j := ⟨i,hz⟩
    dsimp only [G]
    rw [dite_eq_left h]
    exact hcompat (Classical.choose h) i ⟨Classical.choose_spec h,hz⟩
  have hsol (i : ι) : ProductSolvesOn g₁ g₂ (U i) G :=
    (hF i).congr (hU i) (heq i)
  refine ⟨G, ⟨?_, ?_, ?_⟩, heq⟩
  · refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨U i, hU i, hi, (hsol i).1.mono inter_subset_right⟩
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (hsol i).2.1 z hi
  · intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact (hsol i).2.2 z hi

end CalderonPaper.ScalarElliptic
