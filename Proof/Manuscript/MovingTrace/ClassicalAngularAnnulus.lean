module

public import Proof.Manuscript.MovingTrace.ReorderedAngularMixedJets
public import Proof.Manuscript.MovingTrace.NormalizedPlaneAmplitude
public import Proof.Manuscript.ClassicalAngularExpansion
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Unweighted local classical symbols before inserting the physical
radius profiles. The joint parameter already includes the output
stereographic coordinate. -/
structure CompactClassicalAngularSymbol
    (U J : Set P) (order : ℤ) (a : P → E → ℂ) where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ)
  cutoff : E → ℝ
  cutoffSmooth : ContDiff ℝ ∞ cutoff
  cutoffZero : ∀ ξ, ‖ξ‖ ≤ 1 → cutoff ξ = 0
  cutoffOne : ∀ ξ, 2 ≤ ‖ξ‖ → cutoff ξ = 1
  coefficient : ℕ → P → E → ℂ
  coefficientSmooth : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (coefficient k)) (U ×ˢ {0}ᶜ)
  homogeneous : ∀ k p, p ∈ U → ∀ ξ, ξ ≠ 0 → ∀ r : ℝ, 0 < r →
    coefficient k p (r • ξ) = (r ^ ((order : ℝ)-k)) • coefficient k p ξ
  remainder : ∀ N j l : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ p ∈ J, ∀ ξ : E,
    ‖angularMixedJet j l (fun p ξ => a p ξ - cutoff ξ • ∑ k ∈ Finset.range N, coefficient k p ξ) p ξ‖ ≤
      B*(1+‖ξ‖) ^ ((order : ℝ)-N-l)

def LocalNormalizedAnnulusJetBounds (U : Set P) (s : P × E → E → ℂ)
    (b : ℕ → P × E → E → ℂ) : Prop :=
  ∀ {J' : Set P}, IsCompact J' → J' ⊆ U → ∀ {Kout : Set E}, IsCompact Kout →
    ∀ N k : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ h ∈ Ioc (0:ℝ) 1,
      ∀ p ∈ J', ∀ x ∈ Kout, ∀ ν ∈ unitAnnulus E, ∀ j ≤ k,
        ‖iteratedFDeriv ℝ j (fun q : (P × E) × E =>
          normalizedAnnulusRemainder s b N h (q.1.1,q.2) q.1.2) ((p,ν),x)‖ ≤ B*h^N

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E]

/-- The annular transport estimates determine the homogeneous expansion
and its exact covector decay. -/
theorem classicalSymbol_of_localAnnulus {U J : Set P} {D Kout : Set E}
    (hU : IsOpen U) (hD : IsOpen D) (hDD : unitAnnulus E ⊆ D)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hOut : IsCompact Kout)
    (s : P × E → E → ℂ) (b : ℕ → P × E → E → ℂ)
    (hVs : ContDiffOn ℝ ∞ (Function.uncurry s) ((U ×ˢ (univ : Set E)) ×ˢ univ))
    (hB : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hRemainder : LocalNormalizedAnnulusJetBounds U s b) :
    ∃ H : CompactClassicalAngularSymbol (U ×ˢ (univ : Set E)) (J ×ˢ Kout) 1 s,
      H.coefficient = homogeneousAngularCoefficient b := by
  let V := U ×ˢ (univ : Set E)
  have hV : IsOpen V := hU.prod isOpen_univ
  have hVJ : J ×ˢ Kout ⊆ V := fun p hp => ⟨hJU hp.1,mem_univ _⟩
  have hAt (p : P × E) (hp : p ∈ V) (ξ : E) :
      ContDiffAt ℝ ∞ (Function.uncurry (s)) (p,ξ) :=
    hVs.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ _⟩)
  have hBAt (p : P × E) (hp : p ∈ V) (k : ℕ) (ν : E) (hν : ‖ν‖ = 1) :
      ContDiffAt ℝ ∞ (Function.uncurry (b k)) (p,ν) :=
    (hB k).contDiffAt ((hV.prod hD).mem_nhds ⟨hp,hDD (unitDirection_mem_unitAnnulus ν hν)⟩)
  have hPoint (p : P × E) (hp : p ∈ V) (ν : E) (hν₁ : (1/2:ℝ) ≤ ‖ν‖) (hν₂ : ‖ν‖ ≤ 2)
      (N : ℕ) : ∃ B : ℝ, ∀ h ∈ Ioc (0:ℝ) 1,
        ‖normalizedAnnulusRemainder (s) b N h p ν‖ ≤ B*h^N := by
    obtain ⟨B,hB,hBd⟩ := hRemainder (J' := {p.1}) isCompact_singleton (singleton_subset_iff.mpr hp.1)
      (Kout := {p.2}) isCompact_singleton N 0
    refine ⟨B,fun h hh => ?_⟩
    simpa only [norm_iteratedFDeriv_zero,Prod.eta] using
      hBd h hh p.1 (mem_singleton _) p.2 (mem_singleton _) ν ⟨hν₁,hν₂⟩ 0 le_rfl
  have hJets (N j l : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ p ∈ J ×ˢ Kout,
      ∀ h ∈ Ioc (0:ℝ) 1, ∀ ν : E, ‖ν‖ = 1 →
        ‖angularMixedJet j l (normalizedAnnulusRemainder (s) b N h) p ν‖ ≤ B*h^N := by
    obtain ⟨B,hB₀,hBd⟩ := hRemainder hJ (hJU) hOut N (j+l)
    refine ⟨B,hB₀,?_⟩
    intro p hp h hh ν hν
    let O : Set ((P × E) × E) := (U ×ˢ D) ×ˢ univ
    let F (q : (P × E) × E) := normalizedAnnulusRemainder (s) b N h
      (q.1.1,q.2) q.1.2
    let L (q : (P × E) × E) := ((q.1.1,q.2),h⁻¹ • q.1.2)
    let M (q : (P × E) × E) := ((q.1.1,q.2),q.1.2)
    have hO : IsOpen O := (hU.prod hD).prod isOpen_univ
    have hL : ContDiff ℝ ∞ L := (contDiff_fst.fst.prodMk contDiff_snd).prodMk
      ((contDiff_const (c := h⁻¹)).smul contDiff_fst.snd)
    have hM : ContDiff ℝ ∞ M := (contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd
    have hS : ContDiffOn ℝ ∞ F O :=
      ((hVs.comp hL.contDiffOn (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩)).const_smul h).sub
        (ContDiffOn.sum (fun k _ => ((hB k).comp hM.contDiffOn
          (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,hq.1.2⟩)).const_smul (h^k)))
    have hνD : ν ∈ D := hDD (unitDirection_mem_unitAnnulus ν hν)
    have hpO : ((p.1,ν),p.2) ∈ O := ⟨⟨hJU hp.1,hνD⟩,mem_univ _⟩
    have hMix := norm_angularMixedJet_le_reordered_joint hO hS p.1 p.2 ν hpO j l
    exact hMix.trans (hBd h hh p.1 hp.1 p.2 hp.2 ν (unitDirection_mem_unitAnnulus ν hν) _ le_rfl)
  obtain ⟨χ,hχ,hχ₀,hχ₁,hCoeff,hHom,hRem⟩ := classicalAngularExpansion_on_compact
    (s) b hV (hJ.prod hOut) hVJ hAt hBAt hPoint hJets
  let H : CompactClassicalAngularSymbol V (J ×ˢ Kout) 1 (s) :=
    ⟨hVs,χ,hχ,hχ₀,hχ₁,homogeneousAngularCoefficient b,
      fun k z hz => (hCoeff k z.1 hz.1 z.2 hz.2).contDiffWithinAt,
      fun k p _ ξ _ r hr => by simpa only [Int.cast_one] using hHom k p ξ hr,
      fun N j l => by
        obtain ⟨B,hB,hBound⟩ := hRem N j l
        refine ⟨B,hB,fun p hp ξ => ?_⟩
        have h := hBound p hp ξ
        unfold cutoffAngularRemainder at h
        simpa only [Int.cast_one] using h⟩
  exact ⟨H,rfl⟩

end CalderonPaper
