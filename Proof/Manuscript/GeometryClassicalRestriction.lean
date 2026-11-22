module

public import Proof.Manuscript.GeometricMixedJetPullback
public import Proof.Manuscript.MovingTraceSymbols
public import Proof.Manuscript.SymbolOrderReduction

import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter MeasureTheory Set
open scoped ContDiff Topology
set_option maxHeartbeats 1800000

namespace CalderonPaper

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {T : Type} {dim : ℕ}

/-- Uniform jets before evaluating the independent geometry parameters on a
moving radius profile. The angular coordinates are still independent. -/
def GeometryAngularJetBounds {B E : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : Set P) (S : Set B) (W : Set E) (weight : E → ℝ)
    (a : P × B → E → ℂ) : Prop :=
  ∀ j l : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ∈ S, ∀ ξ ∈ W,
    ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*weight ξ

variable {Y : Set (X dim)} {U J : Set P} {β : T → X dim → ℝ} {p : T → X dim → P}

/-- Restrict the joint estimate to an actual geometry profile. Only the six
base derivatives spend geometry jets. The angular derivative orders are unrestricted. -/
theorem GeometryAngularJetBounds.pullback
    {B E : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set B} {W : Set E} {weight : E → ℕ → ℝ}
    {a : P × B → E → ℂ}
    (hB : ∀ l, ∀ ξ ∈ W, 0 ≤ weight ξ l)
    {O : Set ((P × B) × E)} (hO : IsOpen O)
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) O)
    (hMem : ∀ q ∈ J, ∀ x ∈ S, ∀ ξ ∈ W, ((q,x),ξ) ∈ O)
    (hJet : ∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ∈ S, ∀ ξ ∈ W,
      ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*weight ξ l)
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n) :
    ∀ j k l : ℕ, j ≤ 6 → ∃ C > (0:ℝ), ∀ t y, y ∈ Y → ∀ x ∈ S, ∀ ξ ∈ W,
      ‖iteratedFDeriv ℝ j (fun b => iteratedFDeriv ℝ k
        (fun x' => iteratedFDeriv ℝ l (a (p t b,x')) ξ) x) y‖ ≤ C*(β t y)^j*weight ξ l := by
  intro j k l hj
  choose C hC hCJet using hJet l
  let A : ℝ := 1 + ∑ n : Fin (j+k+1), C n
  have hA : 0 < A := by
    dsimp [A]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun n _ => (hC n).le))
  refine ⟨j.factorial*A*D^j, by positivity, ?_⟩
  intro t y hy x hx ξ hξ
  have hEst (n : ℕ) (hn : n ≤ j+k) : ‖angularMixedJet n l a (p t y,x) ξ‖ ≤ A*weight ξ l := by
    have h₂ : C n ≤ A := by
      let u : Fin (j+k+1) := ⟨n,Nat.lt_add_one_of_le hn⟩
      have hh := Finset.single_le_sum (f := fun u : Fin (j+k+1) => C u)
        (fun u _ => (hC u).le) (Finset.mem_univ u)
      exact hh.trans (le_add_of_nonneg_left zero_le_one)
    exact (hCJet n _ (hJ t hy) x hx ξ hξ).trans (mul_le_mul_of_nonneg_right h₂ (hB l ξ hξ))
  have h := geometricMixedJet_pullback_le hO ha (hp t).contDiffAt x ξ (hMem _ (hJ t hy) x hx ξ hξ)
    (hβ t y hy) hD j k l (fun n hn => hP t y hy n (hn.trans hj)) hEst
  exact h.trans_eq (by ring)

/-- An order-m symbol of a smooth operator family in the independent
geometry parameters. -/
@[expose] def UniformGeometryClassicalAngularSymbol (U J : Set P) (order : ℤ)
    (a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ) ∧
  (∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
    ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((order:ℝ)-l)) ∧
  ∃ (χ : AngularCoordinates dim → ℝ)
    (b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ),
    ContDiff ℝ ∞ χ ∧ (∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0) ∧ (∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1) ∧
    (∀ j, ContDiffOn ℝ ∞ (Function.uncurry (b j)) ((U ×ˢ univ) ×ˢ {0}ᶜ)) ∧
    (∀ j q, q ∈ U → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      b j (q,x) (r • ξ) = ((r^((order:ℝ)-j) : ℝ) : ℂ)*b j (q,x) ξ) ∧
    ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((order-(N:ℤ):ℝ)-l)

theorem contDiffOn_geometryCutoffRemainder
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ} {U : Set P}
    (hU : IsOpen U) (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    {χ : AngularCoordinates dim → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχ₀ : ∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0)
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (hb : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (b j)) ((U ×ˢ univ) ×ˢ {0}ᶜ)) (N : ℕ) :
    ContDiffOn ℝ ∞ (Function.uncurry fun q ξ => a q ξ - (χ ξ : ℂ) *
      ∑ j ∈ Finset.range N, b j q ξ) ((U ×ˢ univ) ×ˢ univ) := by
  intro q hq
  have h := ha.contDiffAt (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds hq)
  by_cases hz : q.2 = 0
  · apply ContDiffAt.contDiffWithinAt
    apply h.congr_of_eventuallyEq
    have hsmall : ∀ᶠ r in 𝓝 q, ‖r.2‖ < 1 :=
      (continuous_norm.comp continuous_snd).continuousAt.eventually
        (eventually_lt_nhds (by simp [hz]))
    filter_upwards [hsmall] with r hr
    simp only [Function.uncurry, hχ₀ _ hr.le, Complex.ofReal_zero, zero_mul, sub_zero]
  · apply ContDiffAt.contDiffWithinAt
    have hOpen : IsOpen ((U ×ˢ (univ : Set (AngularCoordinates dim))) ×ˢ
        ({0}ᶜ : Set (AngularCoordinates dim))) :=
      (hU.prod isOpen_univ).prod isClosed_singleton.isOpen_compl
    have hMem : q ∈ ((U ×ˢ (univ : Set (AngularCoordinates dim))) ×ˢ {0}ᶜ) :=
      ⟨hq.1,hz⟩
    have hsum : ContDiffAt ℝ ∞ (fun r => ∑ j ∈ Finset.range N, b j r.1 r.2) q :=
      ContDiffAt.sum (fun j _ => (hb j).contDiffAt (hOpen.mem_nhds hMem))
    have hχ' : ContDiffAt ℝ ∞ (fun r : (P × AngularCoordinates dim) × AngularCoordinates dim =>
        (χ r.2 : ℂ)) q := Complex.ofRealCLM.contDiff.contDiffAt.comp q
          (hχ.contDiffAt.comp q contDiffAt_snd)
    exact h.sub (hχ'.mul hsum)


/-- Pull back a specified classical expansion, retaining its exact cutoff and
homogeneous coefficients as witnesses. -/
theorem geometryClassicalSymbol_pullback_witness
    (hU : IsOpen U) (hJU : J ⊆ U) {m : ℤ}
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    {χ : AngularCoordinates dim → ℝ}
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hA : ∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((m:ℝ)-l))
    (hχ : ContDiff ℝ ∞ χ) (hχ₀ : ∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0)
    (hb : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (b j)) ((U ×ˢ univ) ×ˢ {0}ᶜ))
    (hHom : ∀ j q, q ∈ U → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      b j (q,x) (r • ξ) = ((r^((m:ℝ)-j) : ℝ) : ℂ)*b j (q,x) ξ)
    (hRest : ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l))
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n) :
    let a' : LocalAngularSymbol T dim := fun t y x ξ => a (p t y,x) ξ
    let b' (j : ℕ) : LocalAngularSymbol T dim := fun t y x ξ => b j (p t y,x) ξ
    (∀ t, ContDiffOn ℝ ∞ (fun q : X dim × (AngularCoordinates dim × AngularCoordinates dim) =>
      a' t q.1 q.2.1 q.2.2) (Y ×ˢ univ)) ∧
    SymbolSeminormBounds Y β m a' ∧
    (∀ j t, ContDiffOn ℝ ∞
      (fun q : X dim × (AngularCoordinates dim × AngularCoordinates dim) => b' j t q.1 q.2.1 q.2.2)
      (Y ×ˢ (univ ×ˢ ({0}ᶜ : Set (AngularCoordinates dim))))) ∧
    (∀ j t y, y ∈ Y → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      b' j t y x (r • ξ) = ((r^((m:ℝ)-j) : ℝ) : ℂ)*b' j t y x ξ) ∧
    ∀ N : ℕ, SymbolSeminormBounds Y β (m-(N:ℤ))
      (fun t y x ξ => a' t y x ξ - (χ ξ : ℂ) * ∑ j ∈ Finset.range N, b' j t y x ξ) := by
  let E := AngularCoordinates dim
  let input (t : T) (z : X dim × (E × E)) : (P × E) × E :=
    ((p t z.1,z.2.1),z.2.2)
  have hInput (t : T) : ContDiff ℝ ∞ (input t) :=
    (((hp t).comp contDiff_fst).prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  have hOpen : IsOpen ((U ×ˢ (univ : Set E)) ×ˢ (univ : Set E)) :=
    (hU.prod isOpen_univ).prod isOpen_univ
  have hSeminorms (o : ℤ) (q : P × E → E → ℂ)
      (hQs : ContDiffOn ℝ ∞ (Function.uncurry q) ((U ×ˢ univ) ×ˢ univ))
      (hQ : ∀ l j, ∃ C > (0:ℝ), ∀ u ∈ J, ∀ x ξ,
        ‖angularMixedJet j l q (u,x) ξ‖ ≤ C*(1+‖ξ‖)^((o:ℝ)-l)) :
      SymbolSeminormBounds Y β o (fun t y x ξ => q (p t y,x) ξ) := by
    have hRaw := GeometryAngularJetBounds.pullback (J := J) (S := (univ : Set E))
      (W := (univ : Set E)) (a := q) (weight := fun ξ l => (1+‖ξ‖)^((o:ℝ)-l))
      (fun l ξ _ => by positivity) hOpen hQs
      (fun u hu x _ ξ _ => ⟨⟨hJU hu,mem_univ x⟩,mem_univ ξ⟩)
      (fun l j => by
        obtain ⟨C,hC,hj⟩ := hQ l j
        exact ⟨C,hC,fun u hu x _ ξ _ => hj u hu x ξ⟩)
      hp hJ hβ hD hP
    intro j k l hj
    obtain ⟨C,hC,hEst⟩ := hRaw j k l hj
    exact ⟨C,hC,fun t y hy x ξ => hEst t y hy x (mem_univ x) ξ (mem_univ ξ)⟩
  refine ⟨?_,hSeminorms m a ha hA,?_,?_,?_⟩
  · intro t
    exact ha.comp (hInput t).contDiffOn
      (fun z hz => ⟨⟨hJU (hJ t hz.1),mem_univ z.2.1⟩,mem_univ z.2.2⟩)
  · intro j t
    exact (hb j).comp (hInput t).contDiffOn
      (fun z hz => ⟨⟨hJU (hJ t hz.1),mem_univ z.2.1⟩,hz.2.2⟩)
  · intro j t y hy x ξ hξ r hr
    exact hHom j (p t y) (hJU (hJ t hy)) x ξ hξ r hr
  · intro N
    let Q (q : P × E) (ξ : E) := a q ξ - (χ ξ : ℂ) * ∑ j ∈ Finset.range N, b j q ξ
    have hQs : ContDiffOn ℝ ∞ (Function.uncurry Q) ((U ×ˢ univ) ×ˢ univ) :=
      contDiffOn_geometryCutoffRemainder hU ha hχ hχ₀ hb N
    have hQj (l j : ℕ) : ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
        ‖angularMixedJet j l Q (q,x) ξ‖ ≤ C*(1+‖ξ‖)^(((m-(N:ℤ):ℤ):ℝ)-l) := by
      simpa only [Q,Int.cast_sub] using hRest N l j
    exact hSeminorms (m-(N:ℤ)) Q hQs hQj

/-- Pull back a classical symbol and every term of its homogeneous expansion
along a geometry profile. The cutoff is unchanged by this pullback. -/
theorem UniformGeometryClassicalAngularSymbol.pullback
    (hU : IsOpen U) (hJU : J ⊆ U) {m : ℤ}
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (ha : UniformGeometryClassicalAngularSymbol U J m a)
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n) :
    UniformClassicalAngularSymbol Y β m (fun t y x ξ => a (p t y,x) ξ) := by
  let E := AngularCoordinates dim
  obtain ⟨ha, hA, χ, b, hχ, hχ₀, hχ₁, hb, hHom, hRest⟩ := ha
  obtain ⟨hS,hJ',hB',hH,hR⟩ := geometryClassicalSymbol_pullback_witness
    hU hJU ha hA hχ hχ₀ hb hHom hRest hp hJ hβ hD hP
  exact ⟨hS,hJ',χ,fun j t y x ξ => b j (p t y,x) ξ,hχ,hχ₀,hχ₁,hB',hH,hR⟩

/-- The order drops when the principal coefficient vanishes after restricting
to the physical geometry. Its auxiliary values in the open parameter set are irrelevant. -/
theorem geometryClassicalSymbol_lower_order_of_principal_zero_pullback
    (hY : IsOpen Y) (hU : IsOpen U) (hJU : J ⊆ U) {m : ℤ}
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    {χ : AngularCoordinates dim → ℝ}
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hA : ∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l a (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((m:ℝ)-l))
    (hχ : ContDiff ℝ ∞ χ) (hχ₀ : ∀ ξ, ‖ξ‖ ≤ 1 → χ ξ = 0)
    (hχ₁ : ∀ ξ, 2 ≤ ‖ξ‖ → χ ξ = 1)
    (hb : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (b j)) ((U ×ˢ univ) ×ˢ {0}ᶜ))
    (hHom : ∀ j q, q ∈ U → ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      b j (q,x) (r • ξ) = ((r^((m:ℝ)-j) : ℝ) : ℂ)*b j (q,x) ξ)
    (hRest : ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => a q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, b j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l))
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n)
    (hZero : ∀ t y, y ∈ Y → ∀ x ξ, ξ ≠ 0 → b 0 (p t y,x) ξ = 0) :
    UniformClassicalAngularSymbol Y β (m-1) (fun t y x ξ => a (p t y,x) ξ) := by
  obtain ⟨hS,_,hB,hH,hR⟩ := geometryClassicalSymbol_pullback_witness
    hU hJU ha hA hχ hχ₀ hb hHom hRest hp hJ hβ hD hP
  exact UniformClassicalAngularSymbol.lower_order_of_principal_zero hY hS hχ hχ₀ hχ₁ hB hH hR hZero

/-- An ambient kernel smooth through every pair of sphere points, with
uniform jets on the relevant compact set of geometry parameters. -/
@[expose] def UniformGeometryAngularSmoothing (U J : Set P)
    (K : P × X dim → X dim → ℂ) : Prop :=
  (∃ O : Set ((P × X dim) × X dim), IsOpen O ∧
    ((U ×ˢ standardSphere dim) ×ˢ standardSphere dim) ⊆ O ∧
    ContDiffOn ℝ ∞ (Function.uncurry K) O) ∧
  ∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ w ∈ standardSphere dim, ∀ z ∈ standardSphere dim,
    ‖angularMixedJet j l K (q,w) z‖ ≤ C

theorem UniformGeometryAngularSmoothing.pullback
    (hJU : J ⊆ U) {K : P × X dim → X dim → ℂ}
    (hK : UniformGeometryAngularSmoothing U J K)
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n) :
    UniformAngularSmoothing Y β (fun t y w z => K (p t y,w) z) := by
  obtain ⟨⟨O,hO,hSub,hSmooth⟩,hBounds⟩ := hK
  let input (t : T) (z : X dim × (X dim × X dim)) : (P × X dim) × X dim :=
    ((p t z.1,z.2.1),z.2.2)
  have hInput (t : T) : ContDiff ℝ ∞ (input t) :=
    (((hp t).comp contDiff_fst).prodMk contDiff_snd.fst).prodMk contDiff_snd.snd
  refine ⟨?_,?_⟩
  · intro t
    refine ⟨input t ⁻¹' O,hO.preimage (hInput t).continuous,?_, ?_⟩
    · intro q hq
      exact hSub ⟨⟨hJU (hJ t hq.1),hq.2.1⟩,hq.2.2⟩
    · exact hSmooth.comp (hInput t).contDiffOn (mapsTo_preimage _ _)
  · have hRaw := GeometryAngularJetBounds.pullback (J := J) (S := standardSphere dim)
      (W := standardSphere dim) (a := K) (weight := fun _ _ => 1)
      (fun _ _ _ => zero_le_one) hO hSmooth
      (fun u hu w hw z hz => hSub ⟨⟨hJU hu,hw⟩,hz⟩)
      (fun l j => by simpa only [mul_one] using hBounds l j)
      hp hJ hβ hD hP
    intro j k l hj
    obtain ⟨C,hC,hEst⟩ := hRaw j k l hj
    refine ⟨C,hC,?_⟩
    intro t y hy w z
    simpa only [mul_one] using hEst t y hy w w.property z z.property

/-- A classical angular operator before evaluating any radius profile.
Both localization identities use the same operator. -/
@[expose] def UniformGeometryClassicalSphereOperator (U J : Set P) (order : ℤ)
    [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)] (A : P → SphereOperator dim) : Prop :=
  (∀ v : ↥(standardSphere dim),
    let κ := stereographic' (dim - 1) v
    ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
      angularSupport χ ⊆ κ.source → angularSupport η ⊆ κ.source →
      ∃ a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ,
        UniformGeometryClassicalAngularSymbol U J order a ∧
        ∀ q ∈ J, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
          ∀ x ∈ κ.target,
            let localizedDatum := fun z : AngularCoordinates dim => η (κ.symm z) * u (κ.symm z)
            let integrand := fun ξ : AngularCoordinates dim =>
              angularFourierPhase x ξ * a (q,x) ξ * angularFourierTransform localizedDatum ξ
            Integrable localizedDatum ∧ Integrable integrand ∧
              χ (κ.symm x) * A q (fun w => η w * u w) (κ.symm x) = ∫ ξ, integrand ξ) ∧
  ∀ χ η : X dim → ℂ, smoothNear χ (standardSphere dim) → smoothNear η (standardSphere dim) →
    Disjoint (angularSupport χ) (angularSupport η) →
    ∃ K : P × X dim → X dim → ℂ, UniformGeometryAngularSmoothing U J K ∧
      ∀ q ∈ J, ∀ u : X dim → ℂ, smoothNear u (standardSphere dim) →
        ∀ w : ↥(standardSphere dim),
          χ w * A q (fun z => η z * u z) w =
            ∫ z : ↥(standardSphere dim), K (q,w) z * u z ∂(sphereProbability dim)

theorem UniformGeometryClassicalSphereOperator.pullback
    [Fact (Module.finrank ℝ (X dim) = dim - 1 + 1)]
    (hU : IsOpen U) (hJU : J ⊆ U) {m : ℤ} {A : P → SphereOperator dim}
    (hA : UniformGeometryClassicalSphereOperator U J m A)
    (hp : ∀ t, ContDiff ℝ ∞ (p t)) (hJ : ∀ t, MapsTo (p t) Y J)
    (hβ : ∀ t y, y ∈ Y → 1 ≤ β t y)
    {D : ℝ} (hD : 1 ≤ D)
    (hP : ∀ t y, y ∈ Y → ∀ n ≤ 6, ‖iteratedFDeriv ℝ n (p t) y‖ ≤ D*(β t y)^n) :
    UniformClassicalSphereOperator Y β m (fun t y => A (p t y)) := by
  refine ⟨?_,?_⟩
  · intro v κ χ η hχ hη hχκ hηκ
    obtain ⟨a,ha,hEq⟩ := hA.1 v χ η hχ hη hχκ hηκ
    refine ⟨fun t y x ξ => a (p t y,x) ξ,ha.pullback hU hJU hp hJ hβ hD hP,?_⟩
    exact fun t y hy => hEq (p t y) (hJ t hy)
  · intro χ η hχ hη hDisjoint
    obtain ⟨K,hK,hEq⟩ := hA.2 χ η hχ hη hDisjoint
    refine ⟨fun t y w z => K (p t y,w) z,hK.pullback hJU hp hJ hβ hD hP,?_⟩
    exact fun t y hy => hEq (p t y) (hJ t hy)


/-- Restrict the set of geometry values on which uniform symbol estimates
are needed, preserving the same smooth domain and witnesses. -/
theorem UniformGeometryClassicalAngularSymbol.restrict_geometry
    {m : ℤ} {K : Set P} {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (hA : UniformGeometryClassicalAngularSymbol U J m a) (hK : K ⊆ J) :
    UniformGeometryClassicalAngularSymbol U K m a := by
  obtain ⟨ha,hA,χ,b,hχ,hχ₀,hχ₁,hB,hHom,hR⟩ := hA
  refine ⟨ha,?_,χ,b,hχ,hχ₀,hχ₁,hB,hHom,?_⟩
  · intro l j
    obtain ⟨C,hC,h⟩ := hA l j
    exact ⟨C,hC,fun p hp => h p (hK hp)⟩
  · intro N l j
    obtain ⟨C,hC,h⟩ := hR N l j
    exact ⟨C,hC,fun p hp => h p (hK hp)⟩

theorem UniformGeometryAngularSmoothing.restrict_geometry
    {K : Set P} {k : P × X dim → X dim → ℂ}
    (hA : UniformGeometryAngularSmoothing U J k) (hK : K ⊆ J) :
    UniformGeometryAngularSmoothing U K k := by
  refine ⟨hA.1,?_⟩
  intro l j
  obtain ⟨C,hC,h⟩ := hA.2 l j
  exact ⟨C,hC,fun p hp => h p (hK hp)⟩

end CalderonPaper
