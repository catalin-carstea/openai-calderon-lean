module

public import Proof.Manuscript.GeometryClassicalPrincipalRestriction

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U J : Set P}

/-- Use a single parameter cutoff for the symbol and every homogeneous
coefficient, with equality on an open neighborhood of the compact data. -/
theorem exists_symbolGeometry_cutoff [FiniteDimensional ℝ P]
    (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ (θ : P → ℝ) (O : Set P), ContDiff ℝ ∞ θ ∧ tsupport θ ⊆ U ∧ IsOpen O ∧
      J ⊆ O ∧ O ⊆ U ∧ EqOn θ (fun _ => 1) O := by
  obtain ⟨W,hW,hJW,hWU,_⟩ := exists_open_between_and_isCompact_closure hJ hU hJU
  obtain ⟨O,hO,hJO,hOW,_⟩ := exists_open_between_and_isCompact_closure hJ hW hJW
  obtain ⟨θ,hθ,_,hSupp,hOne⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW isClosed_closure hOW
  refine ⟨θ,O,hθ,?_,hO,hJO,subset_closure.trans (hOW.trans (subset_closure.trans hWU)),?_⟩
  · exact (closure_mono (hSupp.le)).trans hWU
  · exact fun p hp => (hOne p).1 (subset_closure hp)

variable {B E : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def geometryCutoffSymbol (θ : P → ℝ) (a : P × B → E → ℂ)
    (q : P × B) (ξ : E) : ℂ :=
  θ q.1 • a q ξ

theorem geometryCutoffSymbol_contDiffOn
    {θ : P → ℝ} (hθ : ContDiff ℝ ∞ θ) (hSupp : tsupport θ ⊆ U)
    (hU : IsOpen U) {D : Set E} (hD : IsOpen D) {a : P × B → E → ℂ}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (geometryCutoffSymbol θ a))
      ((univ ×ˢ univ) ×ˢ D) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  by_cases h : q.1.1 ∈ U
  · have hA := ha.contDiffAt (((hU.prod isOpen_univ).prod hD).mem_nhds
      (show q ∈ (U ×ˢ univ) ×ˢ D from ⟨⟨h,mem_univ _⟩,hq.2⟩))
    exact (hθ.contDiffAt.comp q contDiffAt_fst.fst).smul hA
  · have hC : q.1.1 ∈ (tsupport θ)ᶜ := fun h' => h (hSupp h')
    have hN : ∀ᶠ z : (P × B) × E in 𝓝 q, z.1.1 ∉ tsupport θ :=
      (continuous_fst.comp continuous_fst :
        Continuous (fun z : (P × B) × E => z.1.1)).continuousAt.eventually
          ((isClosed_tsupport θ).isOpen_compl.mem_nhds hC)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [hN] with z hz
    have hθ₀ : θ z.1.1 = 0 := by
      by_contra hn
      exact hz (subset_tsupport _ hn)
    exact (show θ z.1.1 • a z.1 z.2 = 0 by rw [hθ₀,zero_smul])

/-- Mixed operator norms can be transferred solely from a neighborhood of the
geometry value. No condition on the frequency outside that neighborhood enters. -/
theorem angularMixedJet_of_germ_geometry
    {a b : P × B → E → ℂ} {O : Set P} (hO : IsOpen O) {p : P} (hp : p ∈ O)
    (h : ∀ q ∈ O, ∀ x ξ, a (q,x) ξ = b (q,x) ξ) (x : B) (ξ : E) (j l : ℕ) :
    angularMixedJet j l a (p,x) ξ = angularMixedJet j l b (p,x) ξ := by
  have he : (fun q : P × B => iteratedFDeriv ℝ l (a q) ξ) =ᶠ[𝓝 (p,x)]
      (fun q : P × B => iteratedFDeriv ℝ l (b q) ξ) := by
    filter_upwards [continuous_fst.continuousAt.eventually (hO.mem_nhds hp)] with q hq
    have heq : a q = b q := funext (h q.1 hq q.2)
    rw [heq]
  exact (he.iteratedFDeriv ℝ j).eq_of_nhds

theorem geometryCutoffSymbol_eq
    {θ : P → ℝ} {O : Set P} (hθ₁ : EqOn θ (fun _ => 1) O) {a : P × B → E → ℂ}
    {p : P} (hp : p ∈ O) (x : B) (ξ : E) :
    geometryCutoffSymbol θ a (p,x) ξ = a (p,x) ξ := by
  rw [geometryCutoffSymbol,hθ₁ hp,one_smul]

theorem geometryCutoffSymbol_classical_data {dim : ℕ} {θ : P → ℝ} {O : Set P}
    (hθ : ContDiff ℝ ∞ θ) (hSupp : tsupport θ ⊆ U) (hU : IsOpen U)
    (hO : IsOpen O) (hJO : J ⊆ O) (hθ₁ : EqOn θ (fun _ => 1) O)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    {χ : AngularCoordinates dim → ℝ}
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (m : ℤ)
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
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l)) :
    let A := geometryCutoffSymbol θ a
    let B (j : ℕ) := geometryCutoffSymbol θ (b j)
    ContDiffOn ℝ ∞ (Function.uncurry A) ((univ ×ˢ univ) ×ˢ univ) ∧
    (∀ l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l A (q,x) ξ‖ ≤ C*(1+‖ξ‖)^((m:ℝ)-l)) ∧
    (∀ j, ContDiffOn ℝ ∞ (Function.uncurry (B j)) ((univ ×ˢ univ) ×ˢ {0}ᶜ)) ∧
    (∀ j q, ∀ x ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
      B j (q,x) (r • ξ) = ((r^((m:ℝ)-j) : ℝ) : ℂ)*B j (q,x) ξ) ∧
    ∀ N l j : ℕ, ∃ C > (0:ℝ), ∀ q ∈ J, ∀ x ξ,
      ‖angularMixedJet j l
        (fun q' ξ' => A q' ξ' - (χ ξ' : ℂ) * ∑ j' ∈ Finset.range N, B j' q' ξ') (q,x) ξ‖
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l) := by
  let A := geometryCutoffSymbol θ a
  let B (j : ℕ) := geometryCutoffSymbol θ (b j)
  refine ⟨geometryCutoffSymbol_contDiffOn hθ hSupp hU isOpen_univ ha,?_,?_,?_,?_⟩
  · intro l j
    obtain ⟨C,hC,hCbd⟩ := hA l j
    refine ⟨C,hC,fun q hq x ξ => ?_⟩
    rw [angularMixedJet_of_germ_geometry (a := A) (b := a) hO (hJO hq)
      (fun p hp x' ξ' => geometryCutoffSymbol_eq hθ₁ hp x' ξ') x ξ j l]
    exact hCbd q hq x ξ
  · intro j
    exact geometryCutoffSymbol_contDiffOn hθ hSupp hU isClosed_singleton.isOpen_compl (hb j)
  · intro j q x ξ hξ r hr
    change θ q • b j (q,x) (r • ξ) = _ * (θ q • b j (q,x) ξ)
    by_cases hq : q ∈ U
    · rw [hHom j q hq x ξ hξ r hr]
      simp only [Complex.real_smul]
      ring
    · have hθ₀ : θ q = 0 := by
        by_contra hn
        exact hq (hSupp (subset_tsupport _ hn))
      rw [hθ₀,zero_smul,zero_smul,mul_zero]
  · intro N l j
    obtain ⟨C,hC,hCbd⟩ := hRest N l j
    refine ⟨C,hC,fun q hq x ξ => ?_⟩
    have he : ∀ p ∈ O, ∀ x ξ,
        A (p,x) ξ - (χ ξ : ℂ) * ∑ k ∈ Finset.range N, B k (p,x) ξ =
          a (p,x) ξ - (χ ξ : ℂ) * ∑ k ∈ Finset.range N, b k (p,x) ξ := by
      intro p hp x ξ
      simp only [A,B,geometryCutoffSymbol_eq hθ₁ hp]
    rw [angularMixedJet_of_germ_geometry
      (a := fun r ν => A r ν - (χ ν : ℂ) * ∑ k ∈ Finset.range N, B k r ν)
      (b := fun r ν => a r ν - (χ ν : ℂ) * ∑ k ∈ Finset.range N, b k r ν)
      hO (hJO hq) he x ξ j l]
    exact hCbd q hq x ξ

/-- All symbol witnesses can be extended by a common geometry cutoff.
The coefficient witnesses remain the actual chosen ones near the compact set. -/
theorem geometryCutoffSymbol_classical_witness {dim : ℕ} {θ : P → ℝ} {O : Set P}
    (hθ : ContDiff ℝ ∞ θ) (hSupp : tsupport θ ⊆ U) (hU : IsOpen U)
    (hO : IsOpen O) (hJO : J ⊆ O) (hθ₁ : EqOn θ (fun _ => 1) O)
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    {χ : AngularCoordinates dim → ℝ}
    {b : ℕ → P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (m : ℤ)
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
      ≤ C*(1+‖ξ‖)^((m-(N:ℤ):ℝ)-l)) :
    UniformGeometryClassicalAngularSymbol univ J m (geometryCutoffSymbol θ a) := by
  obtain ⟨hA,hAb,hB,hHom',hRest'⟩ := geometryCutoffSymbol_classical_data
    hθ hSupp hU hO hJO hθ₁ m ha hA hχ hχ₀ hb hHom hRest
  exact ⟨hA,hAb,χ,fun j => geometryCutoffSymbol θ (b j),hχ,hχ₀,hχ₁,hB,
    fun j q _ => hHom' j q,hRest'⟩

theorem UniformGeometryClassicalAngularSymbol.globalize [FiniteDimensional ℝ P] {dim : ℕ}
    (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U)
    {m : ℤ} {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (ha : UniformGeometryClassicalAngularSymbol U J m a) :
    ∃ (θ : P → ℝ) (O : Set P), IsOpen O ∧ J ⊆ O ∧ EqOn θ (fun _ => 1) O ∧
      UniformGeometryClassicalAngularSymbol univ J m (geometryCutoffSymbol θ a) := by
  obtain ⟨θ,O,hθ,hSupp,hO,hJO,_,hθ₁⟩ := exists_symbolGeometry_cutoff hU hJ hJU
  obtain ⟨ha,hA,χ,b,hχ,hχ₀,hχ₁,hb,hHom,hRest⟩ := ha
  exact ⟨θ,O,hO,hJO,hθ₁,
    geometryCutoffSymbol_classical_witness hθ hSupp hU hO hJO hθ₁ m ha hA hχ hχ₀ hχ₁ hb hHom hRest⟩

theorem GeometryClassicalSymbolPrincipalZero.globalize [FiniteDimensional ℝ P] {dim : ℕ}
    (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U) {Z : Set P}
    {m : ℤ} {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (ha : GeometryClassicalSymbolPrincipalZero U J Z m a) :
    ∃ (θ : P → ℝ) (O : Set P), IsOpen O ∧ J ⊆ O ∧ EqOn θ (fun _ => 1) O ∧
      GeometryClassicalSymbolPrincipalZero univ J Z m (geometryCutoffSymbol θ a) := by
  obtain ⟨θ,O,hθ,hSupp,hO,hJO,_,hθ₁⟩ := exists_symbolGeometry_cutoff hU hJ hJU
  obtain ⟨ha,hA,χ,b,hχ,hχ₀,hχ₁,hb,hHom,hRest,hZero⟩ := ha
  obtain ⟨hA,hAb,hB,hHom',hRest'⟩ := geometryCutoffSymbol_classical_data
    hθ hSupp hU hO hJO hθ₁ m ha hA hχ hχ₀ hb hHom hRest
  refine ⟨θ,O,hO,hJO,hθ₁,hA,hAb,χ,fun j => geometryCutoffSymbol θ (b j),hχ,hχ₀,hχ₁,hB,
    (fun j q _ => hHom' j q),hRest',?_⟩
  intro q hq x ξ hξ
  change θ q • b 0 (q,x) ξ = 0
  rw [hZero q hq x ξ hξ,smul_zero]


/-- Extend a smooth off-diagonal kernel in geometry while preserving
all its values and all of its mixed derivatives near the selected compact. -/
theorem UniformGeometryAngularSmoothing.globalize [FiniteDimensional ℝ P] {dim : ℕ}
    (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U)
    {K : P × X dim → X dim → ℂ} (hK : UniformGeometryAngularSmoothing U J K) :
    ∃ K' : P × X dim → X dim → ℂ, UniformGeometryAngularSmoothing univ J K' ∧
      ∀ p ∈ J, ∀ w z, K' (p,w) z = K (p,w) z := by
  obtain ⟨θ,O,hθ,hSupp,hO,hJO,_,hθ₁⟩ := exists_symbolGeometry_cutoff hU hJ hJU
  obtain ⟨⟨W,hW,hWS,hKS⟩,hKB⟩ := hK
  let K' := geometryCutoffSymbol θ K
  let T := (fun q : (P × X dim) × X dim => q.1.1) ⁻¹' (tsupport θ)ᶜ
  have hT : IsOpen T := (isClosed_tsupport θ).isOpen_compl.preimage
    (continuous_fst.comp continuous_fst)
  have hK₀ : EqOn (Function.uncurry K') (fun _ => (0:ℂ)) T := by
    intro q hq
    have hθ₀ : θ q.1.1 = 0 := by
      by_contra h
      exact hq (subset_tsupport _ h)
    change θ q.1.1 • K q.1 q.2 = 0
    rw [hθ₀,zero_smul]
  have hKWS : ContDiffOn ℝ ∞ (Function.uncurry K') W :=
    ((hθ.comp (contDiff_fst.comp contDiff_fst)).contDiffOn).smul hKS
  have hKTS : ContDiffOn ℝ ∞ (Function.uncurry K') T :=
    contDiffOn_const.congr hK₀
  have hContain : ((univ ×ˢ standardSphere dim) ×ˢ standardSphere dim) ⊆ W ∪ T := by
    intro q hq
    by_cases hp : q.1.1 ∈ U
    · exact Or.inl (hWS ⟨⟨hp,hq.1.2⟩,hq.2⟩)
    · exact Or.inr (fun h => hp (hSupp h))
  have hBoth : ContDiffOn ℝ ∞ (Function.uncurry K') (W ∪ T) := by
    intro q hq
    rcases hq with hw | ht
    · exact (hKWS.contDiffAt (hW.mem_nhds hw)).contDiffWithinAt
    · exact (hKTS.contDiffAt (hT.mem_nhds ht)).contDiffWithinAt
  refine ⟨K',⟨⟨W ∪ T,hW.union hT,hContain,hBoth⟩,?_⟩,
    fun p hp w z => geometryCutoffSymbol_eq hθ₁ (hJO hp) w z⟩
  intro l j
  obtain ⟨C,hC,hBd⟩ := hKB l j
  refine ⟨C,hC,fun p hp w hw z hz => ?_⟩
  rw [angularMixedJet_of_germ_geometry (a := K') (b := K) hO (hJO hp)
    (fun q hq w' z' => geometryCutoffSymbol_eq hθ₁ hq w' z') w z j l]
  exact hBd p hp w hw z hz

end CalderonPaper
