module

public import Proof.Manuscript.MovingTrace.LocalPoissonAnnulus
public import Proof.Manuscript.MovingTrace.LocalAngularSymbolAlgebra
public import Proof.Manuscript.MovingTrace.VelocityChartPlaneWaves
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch.BoundaryLayer Set Filter Metric
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

/-- The actual localized angular response has a classical order-one
symbol. The principal symbol is explicit, and every coefficient is
supported where both angular cutoffs can be active. -/
theorem exists_velocity_classical_symbol
    (A : SmoothRadialVelocity G) {J : Set P} (hJ : IsCompact J) (hJU : J ⊆ A.U)
    {χ ζ : E → ℂ} (hχ : ContDiff ℝ ∞ χ) (hζ : ContDiff ℝ ∞ ζ)
    {Kχ Kζ : Set E} (hKχ : IsCompact Kχ) (hKζ : IsCompact Kζ)
    (hχ₀ : ∀ x ∉ Kχ, χ x = 0) (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) :
    ∃ (U : Set P) (s : Q → E → ℂ),
      IsOpen U ∧ J ⊆ U ∧ U ⊆ A.U ∧
      ∃ H : CompactClassicalAngularSymbol (U ×ˢ (univ : Set E)) (J ×ˢ Kχ) 1 s,
        (∀ p ∈ U, ∀ x ξ, s (p,x) ξ = C.actualVelocityChartSymbol A χ ζ (p,x) ξ) ∧
        (∀ p x ξ, x ∉ Kχ → s (p,x) ξ = 0) ∧
        (∀ k p x ξ, x ∉ Kχ ∩ Kζ → H.coefficient k (p,x) ξ = 0) ∧
        (∀ p ∈ U, ∀ x ξ, ξ ≠ 0 → H.coefficient 0 (p,x) ξ = C.velocityPrincipalSymbol A χ ζ (p,x) ξ) ∧
        ∃ (D : Set E) (b : ℕ → Q → E → ℂ),
          IsOpen D ∧ unitAnnulus E ⊆ D ∧ D ⊆ {0}ᶜ ∧
          (∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D)) ∧
          LocalNormalizedAnnulusJetBounds U s b ∧
          H.coefficient = homogeneousAngularCoefficient b ∧
          (∀ k p x ξ, x ∉ Kχ ∩ Kζ → b k (p,x) ξ = 0) := by
  obtain ⟨U₀,W,V,a,hU₀,hJU₀,hU₀A,hW,hSW,hV,hEqV,ha,ha₀,hAmp⟩ :=
    C.exists_chart_velocity_plane_data A hJ hJU hζ hKζ hζ₀
  obtain ⟨U₁,D,b,hU₁,hJU₁,hU₁G,hD,hDD,hD₀,hB,hB₀,hPrincipal,hBounds⟩ :=
    C.exists_radialPoisson_annulus hJ (hJU.trans A.subset) ha hKζ ha₀
  let U := U₀ ∩ U₁
  have hU : IsOpen U := hU₀.inter hU₁
  have hJU' : J ⊆ U := subset_inter hJU₀ hJU₁
  have hUA : U ⊆ A.U := inter_subset_left.trans hU₀A
  have hUV : U ⊆ G.V := hUA.trans A.subset
  let h (i j : I (n+1)) := rotationCoeff V i j
  let c (q : Q) := χ q.2 * (C.chartWeight A q : ℂ)
  let d (q : Q) := -χ q.2 * ∑ i, ∑ j, C.localRotationLow i j (fun q => ζ q.2) (h i j) q
  let L (q : Q) (ξ : E) :=
    -χ q.2 * ∑ i, ∑ j, C.localRotationHigh i j (fun q => ζ q.2) (h i j) q ξ
  let f := C.rawPoissonSymbol a
  let s := baseMulAddAffineSymbol f c d L
  let b' := baseMulAddAffineCoefficients b c d L
  have hc : ContDiffOn ℝ ∞ c (U ×ˢ univ) :=
    ((hχ.comp contDiff_snd).contDiffOn).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((C.chartWeight_contDiffOn A).mono (Set.prod_mono hUA Subset.rfl)))
  have hRot (i j : I (n+1)) := C.localRotationSymbol_contDiffOn hU (hζ.comp contDiff_snd)
    ((rotationCoeff_contDiff hV i j).contDiffOn) i j
  have hd : ContDiffOn ℝ ∞ d (U ×ˢ univ) :=
    ((hχ.comp contDiff_snd).neg.contDiffOn).mul
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hRot i j).1)
  have hL : ContDiffOn ℝ ∞ (Function.uncurry L) ((U ×ˢ univ) ×ˢ univ) :=
    ((hχ.comp contDiff_fst.snd).neg.contDiffOn).mul
      (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => (hRot i j).2)
  have hLin : ∀ p ξ k, L p (k • ξ) = (k:ℝ) • L p ξ := by
    intro p ξ k
    simp only [L,C.localRotationHigh_smul,Complex.real_smul,← Finset.mul_sum]
    ring
  have hf : ContDiffOn ℝ ∞ (Function.uncurry f) ((U ×ˢ univ) ×ˢ univ) :=
    (C.rawPoissonSymbol_contDiffOn ha hKζ ha₀).mono (Set.prod_mono (Set.prod_mono hUV Subset.rfl) Subset.rfl)
  have hb (k : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D) :=
    (hB k).mono (Set.prod_mono (Set.prod_mono inter_subset_right Subset.rfl) Subset.rfl)
  have hBounds' : LocalNormalizedAnnulusJetBounds U f b := by
    intro J' hJ' hJ'U Kout hKout
    exact hBounds hJ' (hJ'U.trans inter_subset_right) hKout
  obtain ⟨hs,hbs,hRem⟩ := localAnnulus_baseMulAddAffine hU hD hDD hf hb hBounds' hc hd hL hLin
  obtain ⟨H,hH⟩ := classicalSymbol_of_localAnnulus hU hD hDD hJ hJU' hKχ s b' hs hbs hRem
  have hEqV' (p : P) (hp : p ∈ U) :
      EqOn (fun z => V (p,z)) (fun z => A.velocity (p,z)) W :=
    fun z hz => hEqV ⟨hp.1,hz⟩
  have hb₀ (k : ℕ) (p : P) (x ξ : E) (hx : x ∉ Kχ ∩ Kζ) : b' k (p,x) ξ = 0 := by
    by_cases hχx : x ∈ Kχ
    · have hζx : x ∉ Kζ := fun hx' => hx ⟨hχx,hx'⟩
      have hZero (i j : I (n+1)) := C.localRotation_zero_off_support hKζ.isClosed (a := fun q => ζ q.2)
        (fun p x hx => hζ₀ x hx) (h i j) i j p hζx ξ
      simp [b',baseMulAddAffineCoefficients,d,L,hB₀ _ _ _ _ hζx,(hZero _ _).1,(hZero _ _).2]
    · simp [b',baseMulAddAffineCoefficients,c,d,L,hχ₀ x hχx]
  refine ⟨U,s,hU,hJU',hUA,H,?_,?_,?_,?_,D,b',hD,hDD,hD₀,hbs,hRem,hH,hb₀⟩
  · intro p hp x ξ
    have hEx := C.chartPlaneWave_adjoint_readout A hζ hKζ hζ₀ hV hW hSW (hUA hp) (hEqV' p hp)
      (hAmp p hp.1) x ξ
    rw [actualVelocityChartSymbol,hEx]
    simp only [s,baseMulAddAffineSymbol,c,d,L,f,Finset.sum_add_distrib]
    ring
  · intro p x ξ hx
    simp [s,baseMulAddAffineSymbol,c,d,L,hχ₀ x hx]
  · intro k p x ξ hx
    rw [hH,homogeneousAngularCoefficient]
    simp only [hb₀ k p x _ hx,smul_zero]
  · intro p hp x ξ hξ
    let ν : E := ‖ξ‖⁻¹ • ξ
    let w := angularPoint C.pole x
    have hν : ‖ν‖ = 1 := by
      have hn := norm_pos_iff.mpr hξ
      simp only [ν,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hνD : ν ∈ D := hDD (unitDirection_mem_unitAnnulus ν hν)
    have hw : w ∈ W := hSW ((stereographic' ((n+1)-1) C.pole).symm x).property
    have hVel : V (p,w) = A.velocity (p,w) := hEqV' p hp hw
    have hHRot (i j : I (n+1)) :
        C.localRotationHigh i j (fun q => ζ q.2) (h i j) (p,x) ν =
        C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff A.velocity i j) (p,x) ν := by
      unfold localRotationHigh localRotationAmplitude
      simp only [h,rotationCoeff,show V (p,angularPoint C.pole x) = A.velocity (p,angularPoint C.pole x) from hVel]
    rw [hH]
    change homogeneousAngularCoefficient b' 0 (p,x) ξ = _
    unfold homogeneousAngularCoefficient
    change angularSymbolScale 0 ‖ξ‖ • b' 0 (p,x) ν = _
    rw [show angularSymbolScale 0 ‖ξ‖ = ‖ξ‖ by simp [angularSymbolScale]]
    have hbTop : b' 0 (p,x) ν = c (p,x) * b 0 (p,x) ν + L (p,x) ν := by
      simp [b',baseMulAddAffineCoefficients]
    have hL' : L (p,x) ν = -χ x * ∑ i, ∑ j,
        C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff A.velocity i j) (p,x) ν := by
      simp only [L,hHRot]
    rw [hbTop,hL',hPrincipal p hp.2 x ν hνD,hAmp p hp.1 x]
    have hWc : (C.chartWeight A (p,x) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (C.chartWeight_ne_zero A (hUA hp) x)
    let R := ∑ i, ∑ j, C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff A.velocity i j) (p,x) ν
    let D₀ := (⟪w,A.velocity (p,w)⟫_ℝ : ℂ)
    let K₀ := (C.coefficients.kappa ((p,ν),x) : ℂ)
    let W₀ := (C.chartWeight A (p,x) : ℂ)
    change (‖ξ‖:ℝ) • ((χ x * W₀) * (K₀ * (ζ x * C.rawChartNormalAmplitude A (p,x))) + -χ x * R) =
      (‖ξ‖:ℂ) * (χ x * (K₀ * ζ x * D₀) - χ x * R)
    have hAmplitude : C.rawChartNormalAmplitude A (p,x) = D₀ / W₀ := Complex.ofReal_div _ _
    rw [hAmplitude,Complex.real_smul]
    field_simp [show W₀ ≠ 0 from hWc]
    ring

end SignedPoissonCollar
end CalderonPaper
