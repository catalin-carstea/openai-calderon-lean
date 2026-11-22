module

public import Proof.Manuscript.RadiusReorderedAngular

import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter Set
open scoped ContDiff Topology
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {P Q E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

@[expose] def geometryRadiusScale (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (t : ℝ) (p : P) : P :=
  e ((e.symm p).1,t*(e.symm p).2)

theorem continuous_geometryRadiusScale (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) :
    Continuous (Function.uncurry (geometryRadiusScale e)) :=
  e.continuous.comp
    ((e.symm.continuous.comp continuous_snd).fst.prodMk
      (continuous_fst.mul (e.symm.continuous.comp continuous_snd).snd))

@[expose] def geometryRadiusSegment (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (U : Set P) : Set P :=
  {p | ∀ t ∈ Icc (0:ℝ) 1, geometryRadiusScale e t p ∈ U}

theorem geometryRadiusSegment_open (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) {U : Set P} (hU : IsOpen U) :
    IsOpen (geometryRadiusSegment e U) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let O := Function.uncurry (geometryRadiusScale e) ⁻¹' U
  have hO : IsOpen O := hU.preimage (continuous_geometryRadiusScale e)
  have hpO : Icc (0:ℝ) 1 ×ˢ {p} ⊆ O := by
    rintro ⟨t,q⟩ ⟨ht,hq⟩
    have hq' : q = p := hq
    subst q
    exact hp t ht
  obtain ⟨W,Z,_,hZ,hW,hP,hSub⟩ := generalized_tube_lemma isCompact_Icc
    isCompact_singleton hO hpO
  refine Filter.mem_of_superset (hZ.mem_nhds (hP (mem_singleton _))) ?_
  intro q hq t ht
  exact hSub (show (t,q) ∈ W ×ˢ Z from ⟨hW ht,hq⟩)

theorem geometryRadiusSegment_subset (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (U : Set P) :
    geometryRadiusSegment e U ⊆ U := by
  intro p hp
  have h := hp 1 (by norm_num)
  simpa only [geometryRadiusScale,one_mul,Prod.eta,LinearIsometryEquiv.apply_symm_apply] using h

private def symbolRadiusInput (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (z : (P × E) × E) :
    ((Q × E) × E) × ℝ :=
  ((((e.symm z.1.1).1,z.2),z.1.2),(e.symm z.1.1).2)

private theorem contDiff_symbolRadiusInput (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) :
    ContDiff ℝ ∞ (symbolRadiusInput (E := E) e) := by
  have h := e.symm.toContinuousLinearEquiv.contDiff.comp
    (show ContDiff ℝ ∞ (fun z : (P × E) × E => z.1.1) from contDiff_fst.fst)
  exact ((h.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd).prodMk h.snd

theorem radiusFirstAngular_contDiffOn {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D : Set E}
    (hU : IsOpen U) (hD : IsOpen D) {a : P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (radiusFirstAngular e a)) ((U ×ˢ univ) ×ˢ D) := by
  have hO : IsOpen (radiusAngularDomain e U D (E := E)) :=
    ((hU.prod hD).prod isOpen_univ).preimage (radiusLastAnnulusEquiv e).continuous
  apply (contDiffOn_radialFirstDerivative hO (radiusAngularLift_contDiffOn (e := e) ha)).comp
    (contDiff_symbolRadiusInput e).contDiffOn
  intro z hz
  change ((e ((e.symm z.1.1).1,(e.symm z.1.1).2),z.2),z.1.2) ∈ (U ×ˢ D) ×ˢ univ
  simpa only [Prod.eta,LinearIsometryEquiv.apply_symm_apply] using
    (show ((z.1.1,z.2),z.1.2) ∈ (U ×ˢ D) ×ˢ univ from ⟨⟨hz.1.1,hz.2⟩,mem_univ _⟩)

theorem radiusTaylorAngular_contDiffOn {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D : Set E}
    (hU : IsOpen U) (hD : IsOpen D) {a : P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (radiusTaylorAngular e a))
      ((geometryRadiusSegment e U ×ˢ univ) ×ˢ D) := by
  have hO : IsOpen (radiusAngularDomain e U D (E := E)) :=
    ((hU.prod hD).prod isOpen_univ).preimage (radiusLastAnnulusEquiv e).continuous
  apply (radiusTaylorRemainder_contDiffOn hO (radiusAngularLift_contDiffOn (e := e) ha)).2.comp
    (contDiff_symbolRadiusInput e).contDiffOn
  intro z hz t ht
  exact ⟨⟨hz.1.1 t ht,hz.2⟩,mem_univ _⟩

theorem radiusAngularLift_normalizedAnnulus_contDiffOn
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D : Set E}
    {a : P × E → E → V} {b : ℕ → P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (N : ℕ) (h : ℝ) :
    ContDiffOn ℝ ∞ (radiusAngularLift e (normalizedAnnulusRemainder a b N h))
      (radiusAngularDomain e U D) := by
  let L (q : ((Q × E) × E) × ℝ) :=
    ((e (q.1.1.1,q.2),q.1.2),h⁻¹ • q.1.1.2)
  have hL : ContDiff ℝ ∞ L :=
    ((e.toContinuousLinearEquiv.contDiff.comp (contDiff_fst.fst.fst.prodMk contDiff_snd)).prodMk
      contDiff_fst.snd).prodMk (contDiff_fst.fst.snd.const_smul _)
  exact ((ha.comp hL.contDiffOn (fun z hz => ⟨⟨hz.1.1,mem_univ _⟩,mem_univ _⟩)).const_smul h).sub
    (ContDiffOn.sum (fun k _ => (radiusAngularLift_contDiffOn (hb k)).const_smul (h^k)))

/-- Annular normalized remainders measured in the usual trial ordering. -/
@[expose] def RadiusAngularAnnularBounds (U : Set P) (Band : Set E)
    (a : P × E → E → V) (b : ℕ → P × E → E → V) : Prop :=
  ∀ {J : Set P}, IsCompact J → J ⊆ U → ∀ {K : Set E}, IsCompact K →
    ∀ N k : ℕ, ∃ B > (0:ℝ), ∀ h ∈ Ioc (0:ℝ) 1,
      ∀ p ∈ J, ∀ x ∈ K, ∀ ν ∈ Band, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun q : (P × E) × E =>
        normalizedAnnulusRemainder a b N h (q.1.1,q.2) q.1.2) ((p,ν),x)‖ ≤ B*h^N

/-- The first radius derivative preserves the complete collection of
normalized annular remainder bounds. -/
theorem RadiusAngularAnnularBounds.radialFirst
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D Band : Set E} (hU : IsOpen U) (hD : IsOpen D)
    (hBand : Band ⊆ D) {a : P × E → E → V} {b : ℕ → P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hNB : RadiusAngularAnnularBounds U Band a b) :
    RadiusAngularAnnularBounds U Band (radiusFirstAngular e a) (fun k => radiusFirstAngular e (b k)) := by
  intro J hJ hJU K hK N k
  obtain ⟨B,hB,hBd⟩ := hNB hJ hJU hK N (k+1)
  refine ⟨B,hB,?_⟩
  intro h hh p hp x hx ξ hξ j hj
  let R := radiusLastAnnulusEquiv (E := E) e
  let q := ((p,ξ),x)
  let q' := R.symm q
  let F := radiusAngularLift e (normalizedAnnulusRemainder a b N h)
  let G (z : (P × E) × E) := normalizedAnnulusRemainder
    (radiusFirstAngular e a) (fun k => radiusFirstAngular e (b k)) N h (z.1.1,z.2) z.1.2
  let O := radiusAngularDomain e U D
  have hO : IsOpen O := ((hU.prod hD).prod isOpen_univ).preimage R.continuous
  have hq : q ∈ (U ×ˢ D) ×ˢ univ := ⟨⟨hJU hp,hBand hξ⟩,mem_univ _⟩
  have hq' : q' ∈ O := by
    change R (R.symm q) ∈ (U ×ˢ D) ×ˢ (univ : Set E)
    rwa [R.apply_symm_apply]
  have hF : ContDiffOn ℝ ∞ F O := radiusAngularLift_normalizedAnnulus_contDiffOn ha hb N h
  have he : G =ᶠ[𝓝 q] radialFirstDerivative F ∘ R.symm := by
    filter_upwards [((hU.prod hD).prod isOpen_univ).mem_nhds hq] with z hz
    exact radialFirstDerivative_normalizedAnnulus hU hD ha hb N h hz.1.1 z.2 hz.1.2
  change ‖iteratedFDeriv ℝ j G q‖ ≤ _
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds,
    R.symm.norm_iteratedFDeriv_comp_right (radialFirstDerivative F) q j]
  refine (norm_iteratedFDeriv_radialFirstDerivative_le (hF.contDiffAt (hO.mem_nhds hq')) j).trans ?_
  let F₀ (z : (P × E) × E) := normalizedAnnulusRemainder a b N h (z.1.1,z.2) z.1.2
  change ‖iteratedFDeriv ℝ (j+1) (F₀ ∘ R) q'‖ ≤ _
  rw [R.norm_iteratedFDeriv_comp_right, show R q' = q from R.apply_symm_apply _]
  exact hBd h hh p hp x hx ξ hξ _ (Nat.add_le_add_right hj 1)

/-- Literal Taylor integration retains the same annular remainder powers
with two more joint input derivatives on the compact radius segments. -/
theorem RadiusAngularAnnularBounds.radiusTaylor
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D Band : Set E} (hU : IsOpen U) (hD : IsOpen D)
    (hBand : Band ⊆ D) {a : P × E → E → V} {b : ℕ → P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hNB : RadiusAngularAnnularBounds U Band a b) :
    RadiusAngularAnnularBounds (geometryRadiusSegment e U) Band (radiusTaylorAngular e a)
      (fun k => radiusTaylorAngular e (b k)) := by
  intro J hJ hJU K hK N k
  let J' := Function.uncurry (geometryRadiusScale e) '' (Icc (0:ℝ) 1 ×ˢ J)
  have hJ' : IsCompact J' := (isCompact_Icc.prod hJ).image (continuous_geometryRadiusScale e)
  have hJ'U : J' ⊆ U := by
    rintro _ ⟨⟨t,p⟩,⟨ht,hp⟩,rfl⟩
    exact hJU hp t ht
  obtain ⟨B,hB,hBd⟩ := hNB hJ' hJ'U hK N (k+2)
  refine ⟨B,hB,?_⟩
  intro h hh p hp x hx ξ hξ j hj
  let R := radiusLastAnnulusEquiv (E := E) e
  let q := ((p,ξ),x)
  let q' := R.symm q
  let F := radiusAngularLift e (normalizedAnnulusRemainder a b N h)
  let G (z : (P × E) × E) := normalizedAnnulusRemainder
    (radiusTaylorAngular e a) (fun k => radiusTaylorAngular e (b k)) N h (z.1.1,z.2) z.1.2
  let O := radiusAngularDomain e U D
  have hO : IsOpen O := ((hU.prod hD).prod isOpen_univ).preimage R.continuous
  have hq : q ∈ (geometryRadiusSegment e U ×ˢ D) ×ˢ univ := ⟨⟨hJU hp,hBand hξ⟩,mem_univ _⟩
  have hq' : q' ∈ radiusSegment O := fun t ht => ⟨⟨hJU hp t ht,hBand hξ⟩,mem_univ _⟩
  have hF : ContDiffOn ℝ ∞ F O := radiusAngularLift_normalizedAnnulus_contDiffOn ha hb N h
  have he : G =ᶠ[𝓝 q] radiusTaylorRemainder F ∘ R.symm := by
    filter_upwards [(((geometryRadiusSegment_open e hU).prod hD).prod isOpen_univ).mem_nhds hq] with z hz
    exact radiusTaylor_normalizedAnnulus hU hD ha hb N h hz.1.1 z.2 hz.1.2
  change ‖iteratedFDeriv ℝ j G q‖ ≤ _
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds,
    R.symm.norm_iteratedFDeriv_comp_right (radiusTaylorRemainder F) q j]
  apply radiusTaylorRemainder_jet_le hO hF hq' j _
  intro t ht l hl
  let F₀ (z : (P × E) × E) := normalizedAnnulusRemainder a b N h (z.1.1,z.2) z.1.2
  change ‖iteratedFDeriv ℝ (l+2) (F₀ ∘ R) (q'.1,t*q'.2)‖ ≤ _
  rw [R.norm_iteratedFDeriv_comp_right]
  have hPoint : R (q'.1,t*q'.2) = ((geometryRadiusScale e t p,ξ),x) := rfl
  rw [hPoint]
  have hp' : geometryRadiusScale e t p ∈ J' := ⟨(t,p),⟨ht,hp⟩,rfl⟩
  exact hBd h hh _ hp' x hx ξ hξ _ (Nat.add_le_add_right (hl.trans hj) 2)

end CalderonPaper
