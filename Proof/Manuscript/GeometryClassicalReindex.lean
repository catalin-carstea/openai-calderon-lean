module

public import Proof.Manuscript.GeometryClassicalPrincipalRestriction
public import Proof.Manuscript.RadiusAngularAnnularBounds

import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter Set
open scoped ContDiff Topology
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {P Q R E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[expose] def geometryReindexSymbol (L : R →L[ℝ] P) (a : P × E → E → ℂ)
    (q : R × E) (ξ : E) : ℂ :=
  a (L q.1,q.2) ξ

theorem geometryReindexSymbol_contDiffOn
    {L : R →L[ℝ] P} {U : Set P} {D : Set E} {a : P × E → E → ℂ}
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ D)) :
    ContDiffOn ℝ ∞ (Function.uncurry (geometryReindexSymbol L a)) (((L ⁻¹' U) ×ˢ univ) ×ˢ D) := by
  let I (q : (R × E) × E) := ((L q.1.1,q.1.2),q.2)
  have hI : ContDiff ℝ ∞ I :=
    ((L.contDiff.comp contDiff_fst.fst).prodMk contDiff_fst.snd).prodMk contDiff_snd
  exact ha.comp hI.contDiffOn (fun q hq => ⟨⟨hq.1.1,hq.1.2⟩,hq.2⟩)

/-- Linear contraction of the geometry component, with angular variables
unchanged, can only decrease each mixed symbol norm. -/
theorem angularMixedJet_geometryReindex_le
    (L : R →L[ℝ] P) (hL : ‖L‖ ≤ 1) {U : Set P} (hU : IsOpen U)
    {a : P × E → E → ℂ} (ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((U ×ˢ univ) ×ˢ univ))
    (q : R) (hq : L q ∈ U) (x ξ : E) (j l : ℕ) :
    ‖angularMixedJet j l (geometryReindexSymbol L a) (q,x) ξ‖ ≤
      ‖angularMixedJet j l a (L q,x) ξ‖ := by
  let F (z : P × E) := iteratedFDeriv ℝ l (a z) ξ
  let M : (R × E) →L[ℝ] (P × E) := L.prodMap (ContinuousLinearMap.id ℝ E)
  let S := U ×ˢ (univ : Set E)
  have hS : IsOpen S := hU.prod isOpen_univ
  have hPre : IsOpen (M ⁻¹' S) := hS.preimage M.continuous
  have hqM : M (q,x) ∈ S := ⟨hq,mem_univ _⟩
  have hF : ContDiffOn ℝ ∞ F S := by
    intro y hy
    have h := ha.contDiffAt ((hS.prod isOpen_univ).mem_nhds (show (y,ξ) ∈ S ×ˢ univ from ⟨hy,mem_univ ξ⟩))
    exact ((contDiffAt_iteratedFDeriv_snd h l).comp y (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  have hM : ‖M‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    change ‖(L z.1,z.2)‖ ≤ 1 * ‖z‖
    rw [Prod.norm_def,one_mul,Prod.norm_def]
    exact max_le (((L.le_opNorm z.1).trans
      (mul_le_of_le_one_left (norm_nonneg _) hL)).trans (le_max_left _ _)) (le_max_right _ _)
  change ‖iteratedFDeriv ℝ j (F ∘ M) (q,x)‖ ≤ ‖iteratedFDeriv ℝ j F (M (q,x))‖
  rw [← iteratedFDerivWithin_of_isOpen (s := M ⁻¹' S) j hPre hqM,
    ← iteratedFDerivWithin_of_isOpen (s := S) j hS hqM,
    M.iteratedFDerivWithin_comp_right hF hS.uniqueDiffOn hPre.uniqueDiffOn hqM (by simp)]
  exact ((iteratedFDerivWithin ℝ j F S (M (q,x))).norm_compContinuousLinearMap_le
    (fun _ => M)).trans (mul_le_of_le_one_right (norm_nonneg _)
      (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hM)))

/-- Set the independent radius to zero without changing any other geometry
coordinate. The max product norm makes this operation a contraction. -/
@[expose] def geometryZeroRadiusLinear (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) : P →L[ℝ] P :=
  e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.fst ℝ Q ℝ).prod (0 : (Q × ℝ) →L[ℝ] ℝ)).comp
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem geometryZeroRadiusLinear_apply (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) (p : P) :
    geometryZeroRadiusLinear e p = e ((e.symm p).1,0) := rfl

theorem norm_geometryZeroRadiusLinear_le (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) :
    ‖geometryZeroRadiusLinear e‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  rw [geometryZeroRadiusLinear_apply,LinearIsometryEquiv.norm_map,one_mul,Prod.norm_def,norm_zero,
    max_eq_left (norm_nonneg _)]
  exact (norm_fst_le (e.symm p)).trans_eq (e.symm.norm_map p)

theorem geometryZeroRadiusLinear_eq_geometryRadiusScale (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) :
    (geometryZeroRadiusLinear e : P → P) = geometryRadiusScale e 0 := by
  funext p
  rw [geometryZeroRadiusLinear_apply,geometryRadiusScale,zero_mul]


/-- Preserve a specified vanishing locus when reindexing the entire
classical expansion by a linear contraction. -/
theorem GeometryClassicalSymbolPrincipalZero.reindex
    {dim : ℕ} {U J Z : Set P} (hU : IsOpen U) (hJU : J ⊆ U)
    {L : R →L[ℝ] P} (hL : ‖L‖ ≤ 1) {J' Z' : Set R}
    (hJ : MapsTo L J' J) (hZ : MapsTo L Z' Z) {m : ℤ}
    {a : P × AngularCoordinates dim → AngularCoordinates dim → ℂ}
    (hA : GeometryClassicalSymbolPrincipalZero U J Z m a) :
    GeometryClassicalSymbolPrincipalZero (L ⁻¹' U) J' Z' m (geometryReindexSymbol L a) := by
  obtain ⟨ha,hA,χ,b,hχ,hχ₀,hχ₁,hb,hHom,hRest,hZero⟩ := hA
  refine ⟨geometryReindexSymbol_contDiffOn ha,?_,χ,fun j => geometryReindexSymbol L (b j),
    hχ,hχ₀,hχ₁,fun j => geometryReindexSymbol_contDiffOn (hb j),?_,?_,?_⟩
  · intro l j
    obtain ⟨C,hC,hBd⟩ := hA l j
    refine ⟨C,hC,fun q hq x ξ => ?_⟩
    exact (angularMixedJet_geometryReindex_le L hL hU ha q (hJU (hJ hq)) x ξ j l).trans
      (hBd (L q) (hJ hq) x ξ)
  · intro j q hq x ξ hξ r hr
    exact hHom j (L q) hq x ξ hξ r hr
  · intro N l j
    obtain ⟨C,hC,hBd⟩ := hRest N l j
    refine ⟨C,hC,fun q hq x ξ => ?_⟩
    let rem (z : P × AngularCoordinates dim) (ν : AngularCoordinates dim) :=
      a z ν - (χ ν : ℂ) * ∑ k ∈ Finset.range N, b k z ν
    have hRem : ContDiffOn ℝ ∞ (Function.uncurry rem) ((U ×ˢ univ) ×ˢ univ) :=
      contDiffOn_geometryCutoffRemainder hU ha hχ hχ₀ hb N
    exact (angularMixedJet_geometryReindex_le L hL hU hRem q (hJU (hJ hq)) x ξ j l).trans
      (hBd (L q) (hJ hq) x ξ)
  · intro q hq x ξ hξ
    exact hZero (L q) (hZ hq) x ξ hξ

end CalderonPaper
