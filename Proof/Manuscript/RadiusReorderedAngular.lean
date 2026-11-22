module

public import Proof.Manuscript.RadiusTaylorCombination
public import Proof.Manuscript.AnnulusExpansion

import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter MeasureTheory Set
open scoped ContDiff Topology
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {P Q E V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem radialFirstDerivative_comp_radiusIndependent
    {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    {a : P × ℝ → V} {g : R → P} {q : R × ℝ}
    (ha : ContDiffAt ℝ ∞ a (g q.1,q.2)) (hg : ContDiffAt ℝ ∞ g q.1) :
    radialFirstDerivative (fun w : R × ℝ => a (g w.1,w.2)) q =
      radialFirstDerivative a (g q.1,q.2) := by
  have hC : ContDiffAt ℝ ∞ (fun w : R × ℝ => (g w.1,w.2)) q :=
    (hg.comp q contDiffAt_fst).prodMk contDiffAt_snd
  exact (hasDerivAt_radialFirstDerivative (ha.comp q hC)).unique
    (hasDerivAt_radialFirstDerivative ha)

private theorem radiusTaylorRemainder_comp_radiusIndependent
    {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] {a : P × ℝ → V} {g : R → P}
    {O : Set (P × ℝ)} (hO : IsOpen O) (ha : ContDiffOn ℝ ∞ a O)
    (hg : ContDiff ℝ ∞ g) {q : R × ℝ} (hq : (g q.1,q.2) ∈ radiusSegment O) :
    radiusTaylorRemainder (fun w : R × ℝ => a (g w.1,w.2)) q =
      radiusTaylorRemainder a (g q.1,q.2) := by
  let A (w : R × ℝ) := (g w.1,w.2)
  have hA : ContDiff ℝ ∞ A := (hg.comp contDiff_fst).prodMk contDiff_snd
  have hPre : IsOpen (A ⁻¹' O) := hO.preimage hA.continuous
  have hEq : EqOn (radialFirstDerivative (a ∘ A)) (radialFirstDerivative a ∘ A) (A ⁻¹' O) :=
    fun w hw => radialFirstDerivative_comp_radiusIndependent
      (ha.contDiffAt (hO.mem_nhds hw)) hg.contDiffAt
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  let w := (q.1,t*q.2)
  have hw : w ∈ A ⁻¹' O := hq t ht
  have he : radialFirstDerivative (a ∘ A) =ᶠ[𝓝 w] radialFirstDerivative a ∘ A :=
    Filter.mem_of_superset (hPre.mem_nhds hw) hEq
  have hEq' := he.fderiv_eq (𝕜 := ℝ)
  have hDiff : radialFirstDerivative (radialFirstDerivative (a ∘ A)) w =
      radialFirstDerivative ((radialFirstDerivative a) ∘ A) w :=
    congrArg (fun L : (R × ℝ) →L[ℝ] V => L (0,1)) hEq'
  change (1-t) • radialFirstDerivative (radialFirstDerivative (a ∘ A)) w =
    (1-t) • radialFirstDerivative (radialFirstDerivative a) (A w)
  rw [hDiff]
  apply congrArg ((1-t) • ·)
  exact radialFirstDerivative_comp_radiusIndependent
    ((contDiffOn_radialFirstDerivative hO ha).contDiffAt (hO.mem_nhds hw)) hg.contDiffAt

/-- Move the independent signed radius to the last coordinate, while
retaining the frequency and output coordinates used in the annulus estimates. -/
@[expose] def radiusLastAnnulusEquiv (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) :
    (((Q × E) × E) × ℝ) ≃ₗᵢ[ℝ] ((P × E) × E) where
  toFun q := ((e (q.1.1.1,q.2),q.1.1.2),q.1.2)
  invFun q := ((((e.symm q.1.1).1,q.1.2),q.2),(e.symm q.1.1).2)
  left_inv q := by simp
  right_inv q := by simp
  map_add' q w := by
    have h := map_add e (q.1.1.1,q.2) (w.1.1.1,w.2)
    simp only [Prod.mk_add_mk] at h
    simp [Prod.mk_add_mk,h]
  map_smul' t q := by
    simp only [RingHom.id_apply, Prod.smul_mk, ← map_smul]
    rfl
  norm_map' q := by
    change ‖((e (q.1.1.1,q.2),q.1.1.2),q.1.2)‖ = ‖q‖
    simp only [Prod.norm_def,LinearIsometryEquiv.norm_map]
    ac_rfl

@[expose] def radiusAngularLift (e : (Q × ℝ) ≃ₗᵢ[ℝ] P)
    (a : P × E → E → V) (q : ((Q × E) × E) × ℝ) : V :=
  a (e (q.1.1.1,q.2),q.1.2) q.1.1.2

@[expose] def radiusFirstAngular (e : (Q × ℝ) ≃ₗᵢ[ℝ] P)
    (a : P × E → E → V) (q : P × E) (ξ : E) : V :=
  radialFirstDerivative (radiusAngularLift e a)
    ((((e.symm q.1).1,ξ),q.2),(e.symm q.1).2)

@[expose] def radiusTaylorAngular (e : (Q × ℝ) ≃ₗᵢ[ℝ] P)
    (a : P × E → E → V) (q : P × E) (ξ : E) : V :=
  radiusTaylorRemainder (radiusAngularLift e a)
    ((((e.symm q.1).1,ξ),q.2),(e.symm q.1).2)

@[expose] def radiusAngularDomain (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (U : Set P) (D : Set E) :
    Set (((Q × E) × E) × ℝ) :=
  radiusLastAnnulusEquiv e ⁻¹' ((U ×ˢ D) ×ˢ univ)

private theorem radiusAngularDomain_open (e : (Q × ℝ) ≃ₗᵢ[ℝ] P)
    {U : Set P} {D : Set E} (hU : IsOpen U) (hD : IsOpen D) :
    IsOpen (radiusAngularDomain e U D) :=
  ((hU.prod hD).prod isOpen_univ).preimage (radiusLastAnnulusEquiv e).continuous

theorem radiusAngularLift_contDiffOn {e : (Q × ℝ) ≃ₗᵢ[ℝ] P}
    {a : P × E → E → V} {U : Set P} {D : Set E}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D)) :
    ContDiffOn ℝ ∞ (radiusAngularLift e a) (radiusAngularDomain e U D) := by
  let L (q : ((Q × E) × E) × ℝ) := ((e (q.1.1.1,q.2),q.1.2),q.1.1.2)
  have hL : ContDiff ℝ ∞ L :=
    ((e.toContinuousLinearEquiv.contDiff.comp
      (contDiff_fst.fst.fst.prodMk contDiff_snd)).prodMk contDiff_fst.snd).prodMk contDiff_fst.fst.snd
  exact ha.comp hL.contDiffOn (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,hq.1.2⟩)

private def scaleAnnulusFrequency (h : ℝ) (q : (Q × E) × E) : (Q × E) × E :=
  ((q.1.1,h⁻¹ • q.1.2),q.2)

private theorem contDiff_scaleAnnulusFrequency (h : ℝ) :
    ContDiff ℝ ∞ (scaleAnnulusFrequency (Q := Q) (E := E) h) :=
  (contDiff_fst.fst.prodMk (contDiff_fst.snd.const_smul _)).prodMk contDiff_snd

/-- The free radius derivative can be taken before or after normalizing any
finite chart-symbol truncation. -/
theorem radialFirstDerivative_normalizedAnnulus {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D : Set E}
    (hU : IsOpen U) (hD : IsOpen D)
    {a : P × E → E → V} {b : ℕ → P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (N : ℕ) (h : ℝ) {p : P} (hp : p ∈ U) (x : E) {ξ : E} (hξ : ξ ∈ D) :
    normalizedAnnulusRemainder (radiusFirstAngular e a) (fun k => radiusFirstAngular e (b k))
      N h (p,x) ξ =
    radialFirstDerivative (radiusAngularLift e (normalizedAnnulusRemainder a b N h))
      ((((e.symm p).1,ξ),x),(e.symm p).2) := by
  let q : ((Q × E) × E) × ℝ := ((((e.symm p).1,ξ),x),(e.symm p).2)
  let O := radiusAngularDomain e U D
  let L := scaleAnnulusFrequency (Q := Q) (E := E) h
  let F (q' : ((Q × E) × E) × ℝ) := radiusAngularLift e a (L q'.1,q'.2)
  have hO := radiusAngularDomain_open e hU hD
  have hq : q ∈ O := by
    change ((e (e.symm p),ξ),x) ∈ (U ×ˢ D) ×ˢ univ
    simpa only [LinearIsometryEquiv.apply_symm_apply] using
      (show ((p,ξ),x) ∈ (U ×ˢ D) ×ˢ univ from ⟨⟨hp,hξ⟩,mem_univ _⟩)
  have hL := contDiff_scaleAnnulusFrequency (Q := Q) (E := E) h
  have hF : ContDiffOn ℝ ∞ F O :=
    (radiusAngularLift_contDiffOn (e := e) ha).comp
      ((hL.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨⟨hz.1.1,mem_univ _⟩,mem_univ _⟩)
  have hB : ∀ k ∈ Finset.range N, ContDiffOn ℝ ∞ (radiusAngularLift e (b k)) O :=
    fun k _ => radiusAngularLift_contDiffOn (hb k)
  have hR := radialFirstDerivative_radiusSubsum hO hF hB h (fun k => h^k) hq
  have hF' := radialFirstDerivative_comp_radiusIndependent
    ((radiusAngularLift_contDiffOn (e := e) ha).contDiffAt
      ((radiusAngularDomain_open e hU isOpen_univ).mem_nhds
        (show (L q.1,q.2) ∈ radiusAngularDomain e U univ from ⟨⟨(show q ∈ O from hq).1.1,mem_univ _⟩,mem_univ _⟩)))
    hL.contDiffAt
  change radialFirstDerivative F q = _ at hF'
  have he : radiusAngularLift e (normalizedAnnulusRemainder a b N h) =
      radiusSubsum (Finset.range N) h (fun k => h^k) F (fun k => radiusAngularLift e (b k)) := rfl
  rw [he,hR]
  change _ = h • radialFirstDerivative F q - _
  rw [hF']
  rfl

set_option maxHeartbeats 3200000 in
/-- The literal, radius-uniform Taylor tail commutes with the normalized
annulus remainder, including its value at zero radius. -/
theorem radiusTaylor_normalizedAnnulus [CompleteSpace V]
    {e : (Q × ℝ) ≃ₗᵢ[ℝ] P} {U : Set P} {D : Set E} (hU : IsOpen U) (hD : IsOpen D)
    {a : P × E → E → V} {b : ℕ → P × E → E → V}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (N : ℕ) (h : ℝ) {p : P}
    (hp : ∀ t ∈ Icc (0:ℝ) 1, e ((e.symm p).1,t*(e.symm p).2) ∈ U)
    (x : E) {ξ : E} (hξ : ξ ∈ D) :
    normalizedAnnulusRemainder (radiusTaylorAngular e a) (fun k => radiusTaylorAngular e (b k))
      N h (p,x) ξ =
    radiusTaylorRemainder (radiusAngularLift e (normalizedAnnulusRemainder a b N h))
      ((((e.symm p).1,ξ),x),(e.symm p).2) := by
  let q : ((Q × E) × E) × ℝ := ((((e.symm p).1,ξ),x),(e.symm p).2)
  let O := radiusAngularDomain e U D
  let L := scaleAnnulusFrequency (Q := Q) (E := E) h
  let F (q' : ((Q × E) × E) × ℝ) := radiusAngularLift e a (L q'.1,q'.2)
  have hO := radiusAngularDomain_open e hU hD
  have hq : q ∈ radiusSegment O := fun t ht => ⟨⟨hp t ht,hξ⟩,mem_univ _⟩
  have hL := contDiff_scaleAnnulusFrequency (Q := Q) (E := E) h
  have hF : ContDiffOn ℝ ∞ F O :=
    (radiusAngularLift_contDiffOn (e := e) ha).comp
      ((hL.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨⟨hz.1.1,mem_univ _⟩,mem_univ _⟩)
  have hB : ∀ k ∈ Finset.range N, ContDiffOn ℝ ∞ (radiusAngularLift e (b k)) O :=
    fun k _ => radiusAngularLift_contDiffOn (hb k)
  have hR := radiusTaylorRemainder_radiusSubsum hO hF hB h (fun k => h^k) hq
  have hScaled : (L q.1,q.2) ∈ radiusSegment (radiusAngularDomain e U (univ : Set E)) :=
    fun t ht => ⟨⟨hp t ht,mem_univ _⟩,mem_univ _⟩
  have hF' : radiusTaylorRemainder F q = radiusTaylorRemainder (radiusAngularLift e a) (L q.1,q.2) :=
    radiusTaylorRemainder_comp_radiusIndependent (g := L) (q := q)
      (radiusAngularDomain_open e hU isOpen_univ) (radiusAngularLift_contDiffOn (e := e) ha)
      hL hScaled
  have he : radiusAngularLift e (normalizedAnnulusRemainder a b N h) =
      radiusSubsum (Finset.range N) h (fun k => h^k) F (fun k => radiusAngularLift e (b k)) := rfl
  rw [he,hR]
  change h • radiusTaylorRemainder (radiusAngularLift e a) (L q.1,q.2) -
    ∑ k ∈ Finset.range N, h^k • radiusTaylorRemainder (radiusAngularLift e (b k)) q =
      h • radiusTaylorRemainder F q -
        ∑ k ∈ Finset.range N, h^k • radiusTaylorRemainder (radiusAngularLift e (b k)) q
  rw [hF']

end CalderonPaper
