module

public import Proof.Manuscript.MovingTrace.ClassicalAngularAnnulus
public import Proof.Manuscript.GeometryClassicalReindex
public import Proof.Manuscript.GeometrySymbolGlobalization
public import Proof.Manuscript.RadiusAngularSupportAndHomogeneity
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
open CalderonN Set Filter
open scoped ContDiff Topology
set_option maxHeartbeats 5800000
set_option backward.isDefEq.respectTransparency false

namespace CalderonPaper

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  {dim : ℕ}
local notation "E" => AngularCoordinates dim

/-- Give the independent-radius derivatives the same classical transport
estimates as the original symbol. This also preserves the zero principal
coefficient on the chosen physical geometry. -/
theorem exists_radius_classical_symbol_pair
    (e : (Q × ℝ) ≃ₗᵢ[ℝ] P) {U J J₀ Z : Set P} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U)
    (hJ₀ : IsCompact J₀) (hSeg : J₀ ⊆ geometryRadiusSegment e U)
    (hZeroJ : MapsTo (geometryZeroRadiusLinear e) J₀ J) (hZ : Z ⊆ J₀)
    {D S : Set E} (hD : IsOpen D) (hDD : unitAnnulus E ⊆ D) (hS : IsCompact S)
    {a : P × E → E → ℂ} {b : ℕ → P × E → E → ℂ}
    (H : CompactClassicalAngularSymbol (U ×ˢ (univ : Set E)) (J ×ˢ S) 1 a)
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hAnn : LocalNormalizedAnnulusJetBounds U a b)
    (hCoeff : H.coefficient = homogeneousAngularCoefficient b)
    (ha₀ : ∀ p x, x ∉ S → ∀ ξ, a (p,x) ξ = 0)
    (hb₀ : ∀ k p x, x ∉ S → ∀ ξ, b k (p,x) ξ = 0)
    (hPrincipal : ∀ p ∈ Z, ∀ x ξ, ξ ≠ 0 →
      radiusFirstAngular e (H.coefficient 0) (geometryZeroRadiusLinear e p,x) ξ = 0) :
    ∃ aFirst aTail : P × E → E → ℂ,
      GeometryClassicalSymbolPrincipalZero univ J₀ Z 1 aFirst ∧
      UniformGeometryClassicalAngularSymbol univ J₀ 1 aTail ∧
      (∀ p ∈ J₀, ∀ x ξ, aFirst (p,x) ξ =
        radiusFirstAngular e a (geometryZeroRadiusLinear e p,x) ξ) ∧
      (∀ p ∈ J₀, ∀ x ξ, aTail (p,x) ξ = radiusTaylorAngular e a (p,x) ξ) ∧
      ∃ C > (0:ℝ), ∀ p ∈ J, ∀ x ξ, ‖radiusFirstAngular e a (p,x) ξ‖ ≤ C*(1+‖ξ‖) := by
  let a₁ := radiusFirstAngular e a
  let b₁ (j : ℕ) := radiusFirstAngular e (b j)
  let a₂ := radiusTaylorAngular e a
  let b₂ (j : ℕ) := radiusTaylorAngular e (b j)
  let U₂ := geometryRadiusSegment e U
  let L := geometryZeroRadiusLinear e
  let Z₁ := L '' Z
  have hU₂ : IsOpen U₂ := geometryRadiusSegment_open e hU
  have hAs₁ := radiusFirstAngular_contDiffOn (e := e) hU isOpen_univ H.smooth
  have hAs₂ := radiusTaylorAngular_contDiffOn (e := e) hU isOpen_univ H.smooth
  have hBs₁ (j : ℕ) := radiusFirstAngular_contDiffOn (e := e) hU hD (hb j)
  have hBs₂ (j : ℕ) := radiusTaylorAngular_contDiffOn (e := e) hU hD (hb j)
  have hBase : RadiusAngularAnnularBounds U (unitAnnulus E) a b := by
    intro W hW hWU K hK N j
    exact hAnn hW hWU hK N j
  have hAnn₁ : LocalNormalizedAnnulusJetBounds U a₁ b₁ :=
    hBase.radialFirst hU hD hDD H.smooth hb
  have hAnn₂ : LocalNormalizedAnnulusJetBounds U₂ a₂ b₂ :=
    hBase.radiusTaylor hU hD hDD H.smooth hb
  obtain ⟨H₁,hCoeff₁⟩ := classicalSymbol_of_localAnnulus hU hD hDD hJ hJU hS
    a₁ b₁ hAs₁ hBs₁ hAnn₁
  obtain ⟨H₂,hCoeff₂⟩ := classicalSymbol_of_localAnnulus hU₂ hD hDD hJ₀
    hSeg hS a₂ b₂ hAs₂ hBs₂ hAnn₂
  have ha₁₀ (p : P) (x : E) (hx : x ∉ S) (ξ : E) : a₁ (p,x) ξ = 0 :=
    radiusFirstAngular_zero_off_support hS.isClosed ha₀ p x hx ξ
  have ha₂₀ (p : P) (x : E) (hx : x ∉ S) (ξ : E) : a₂ (p,x) ξ = 0 :=
    radiusTaylorAngular_zero_off_support hS.isClosed ha₀ p x hx ξ
  have hB₁₀ (k : ℕ) (p : P) (x : E) (hx : x ∉ S) (ξ : E) : H₁.coefficient k (p,x) ξ = 0 := by
    rw [hCoeff₁,homogeneousAngularCoefficient]
    exact smul_eq_zero_of_right _ (radiusFirstAngular_zero_off_support hS.isClosed (hb₀ k) p x hx _)
  have hB₂₀ (k : ℕ) (p : P) (x : E) (hx : x ∉ S) (ξ : E) : H₂.coefficient k (p,x) ξ = 0 := by
    rw [hCoeff₂,homogeneousAngularCoefficient]
    exact smul_eq_zero_of_right _ (radiusTaylorAngular_zero_off_support hS.isClosed (hb₀ k) p x hx _)
  have hPrincipal' (p : P) (hp : p ∈ Z₁) (x : E) (ξ : E) (hξ : ξ ≠ 0) :
      H₁.coefficient 0 (p,x) ξ = 0 := by
    rcases hp with ⟨p',hp',rfl⟩
    have hpU : L p' ∈ U := hJU (hZeroJ (hZ hp'))
    have hSmooth : ContDiffOn ℝ ∞ (Function.uncurry (homogeneousAngularCoefficient b 0))
        ((U ×ˢ (univ : Set E)) ×ˢ {0}ᶜ) := by
      rw [← hCoeff]
      exact H.coefficientSmooth 0
    have hn := norm_pos_iff.mpr hξ
    have hν : ‖(‖ξ‖⁻¹ : ℝ) • ξ‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    rw [hCoeff₁,← radiusFirstAngular_homogeneousAngularCoefficient hU hD 0 (hb 0)
        hSmooth hpU x hξ (hDD (unitDirection_mem_unitAnnulus _ hν)),← hCoeff]
    exact hPrincipal p' hp' x ξ hξ
  obtain ⟨hA₁,hR₁⟩ := geometryClassicalSymbol_supported_bounds hU hJU hS.isClosed
    (a := a₁) (χ := H₁.cutoff) (b := H₁.coefficient) 1
    (fun p _ => ha₁₀ p) (fun k p _ => hB₁₀ k p)
    (by
      intro N l j
      obtain ⟨C,hC,hbd⟩ := H₁.remainder N j l
      refine ⟨C,hC,fun p hp x hx ξ => ?_⟩
      simpa only [Complex.real_smul, Int.cast_one, Int.cast_natCast] using hbd (p,x) ⟨hp,hx⟩ ξ)
  have hF₁ : GeometryClassicalSymbolPrincipalZero U J Z₁ 1 a₁ := by
    refine ⟨hAs₁,hA₁,H₁.cutoff,H₁.coefficient,H₁.cutoffSmooth,H₁.cutoffZero,H₁.cutoffOne,
      H₁.coefficientSmooth,?_,hR₁,hPrincipal'⟩
    intro k p hp x ξ hξ r hr
    exact (H₁.homogeneous k (p,x) ⟨hp,mem_univ _⟩ ξ hξ r hr).trans Complex.real_smul
  have hF₂ : UniformGeometryClassicalAngularSymbol U₂ J₀ 1 a₂ := by
    refine geometryClassicalAngularSymbol_of_supported_remainders hU₂ hSeg
      hS.isClosed (χ := H₂.cutoff) (b := H₂.coefficient) 1 hAs₂ H₂.cutoffSmooth
      H₂.cutoffZero H₂.cutoffOne H₂.coefficientSmooth ?_ (fun p _ => ha₂₀ p)
      (fun k p _ => hB₂₀ k p) ?_
    · intro k p hp x ξ hξ r hr
      exact (H₂.homogeneous k (p,x) ⟨hp,mem_univ _⟩ ξ hξ r hr).trans Complex.real_smul
    · intro N l j
      obtain ⟨C,hC,hbd⟩ := H₂.remainder N j l
      refine ⟨C,hC,fun p hp x hx ξ => ?_⟩
      simpa only [Complex.real_smul, Int.cast_one, Int.cast_natCast] using hbd (p,x) ⟨hp,hx⟩ ξ
  have hLZ : MapsTo L Z Z₁ := fun p hp => mem_image_of_mem L hp
  have hReindex := hF₁.reindex hU hJU (norm_geometryZeroRadiusLinear_le e) hZeroJ hLZ
  obtain ⟨θ₁,O₁,hO₁,hJ₀₁,hθ₁,hG₁⟩ := hReindex.globalize (hU.preimage L.continuous)
    hJ₀ (fun _ hp => hJU (hZeroJ hp))
  obtain ⟨θ₂,O₂,hO₂,hJ₀₂,hθ₂,hG₂⟩ := hF₂.globalize hU₂ hJ₀ hSeg
  refine ⟨_,_,hG₁,hG₂,?_,?_,?_⟩
  · intro p hp x ξ
    exact geometryCutoffSymbol_eq hθ₁ (hJ₀₁ hp) x ξ
  · intro p hp x ξ
    exact geometryCutoffSymbol_eq hθ₂ (hJ₀₂ hp) x ξ
  · obtain ⟨C,hC,hbd⟩ := hA₁ 0 0
    refine ⟨C,hC,fun p hp x ξ => ?_⟩
    simpa only [angularMixedJet,norm_iteratedFDeriv_zero,Int.cast_one,Nat.cast_zero,sub_zero,Real.rpow_one]
      using hbd p hp x ξ

end CalderonPaper
