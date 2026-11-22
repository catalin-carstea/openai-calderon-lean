module

public import Proof.Manuscript.RapidSphereKernel
import Proof.Manuscript.RadialVelocitySphereZero
public import Proof.Manuscript.MovingTrace.VelocityChartPlaneDatum
public import Proof.Manuscript.MovingTrace.ClassicalAngularAnnulus
import Mathlib.Tactic

public section

noncomputable section

set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter Metric MeasureTheory CalderonN
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "E" => X n

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n+1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G) (A : SmoothRadialVelocity G)

/-- The outputs of the local exact velocity quantization needed for
smoothing on disjoint angular supports. -/
structure CompactVelocityRapidChart (χ η : Z → ℂ) (ζ : E → ℂ)
    (Kζ : Set E) (J : Set P) where
  U : Set P
  symbol : Q → E → ℂ
  openU : IsOpen U
  contains : J ⊆ U
  subset : U ⊆ A.U
  classical : CompactClassicalAngularSymbol (U ×ˢ (univ : Set E))
    (J ×ˢ angularChartSupport C.pole χ) 1 symbol
  exactSymbol : ∀ p ∈ U, ∀ x ξ, symbol (p,x) ξ =
    C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ
  quantization : ∀ p ∈ U, ∀ u : Z → ℂ, smoothNear u S → ∀ x : E,
    χ (angularPoint C.pole x) * A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
      ∫ ξ, angularFourierPhase (dim := n+1) x ξ * symbol (p,x) ξ *
        angularFourierTransform (dim := n+1) (fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)) ξ
  coeffSupport : ∀ k p x ξ, x ∉ angularChartSupport C.pole χ ∩ Kζ →
    classical.coefficient k (p,x) ξ = 0

private theorem actualVelocityChartSymbol_eq_zero_outside (χ : Z → ℂ) (ζ : E → ℂ)
    (p : P) (x : E) (hx : x ∉ angularChartSupport C.pole χ) (ξ : E) :
    C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ = 0 := by
  simp [actualVelocityChartSymbol, angularDatum_zero_outside_chartSupport C.pole χ hx]

/-- A choice of local exact compact symbol witnesses extends to a single
literal rapid symbol on the complete open velocity domain. -/
theorem actualVelocityChartSymbol_rapid
    {χ η : Z → ℂ} {ζ : E → ℂ} {Kζ : Set E}
    (hχS : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (hDis : Disjoint (angularChartSupport C.pole χ) Kζ)
    (hLocal : ∀ J : Set P, IsCompact J → J ⊆ A.U →
      Nonempty (C.CompactVelocityRapidChart A χ η ζ Kζ J)) :
    RapidAngularSymbol (dim := n+1) A.U (C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ) := by
  let a := C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ
  have ha : ContDiffOn ℝ ∞ (Function.uncurry a) ((A.U ×ˢ univ) ×ˢ univ) := by
    intro q hq
    obtain ⟨H⟩ := hLocal {q.1.1} isCompact_singleton (singleton_subset_iff.mpr hq.1.1)
    let V : Set (Q × E) := (H.U ×ˢ univ) ×ˢ univ
    have hV : IsOpen V := (H.openU.prod isOpen_univ).prod isOpen_univ
    have hqV : q ∈ V := ⟨⟨H.contains (mem_singleton _),mem_univ _⟩,mem_univ _⟩
    have he : Function.uncurry a =ᶠ[𝓝 q] Function.uncurry H.symbol :=
      Filter.mem_of_superset (hV.mem_nhds hqV)
        (fun q hq => (H.exactSymbol q.1.1 hq.1.1 q.1.2 q.2).symm)
    exact ((H.classical.smooth.contDiffAt (hV.mem_nhds hqV)).congr_of_eventuallyEq he).contDiffWithinAt
  refine rapidAngularSymbol_of_zero_classical_expansion (dim := n+1) A.openU ha
    (c := 0) rfl (b := fun _ _ _ => 0) (fun _ _ _ _ _ _ => rfl) ?_
  intro J hJ hJU N k
  obtain ⟨H⟩ := hLocal J hJ hJU
  have hCoeff (j : ℕ) (q : Q) (ξ : E) : H.classical.coefficient j q ξ = 0 := by
    rcases q with ⟨p,x⟩
    exact H.coeffSupport j p x ξ (fun hx => (Set.disjoint_left.mp hDis) hx.1 hx.2)
  obtain ⟨B,hB,hBound⟩ := H.classical.remainder N k 0
  refine ⟨B,hB,fun p hp x ξ => ?_⟩
  simp only [Pi.zero_apply,Finset.sum_const_zero,Complex.ofReal_zero,zero_mul,sub_zero]
  by_cases hx : x ∈ angularChartSupport C.pole χ
  · have hN : H.U ×ˢ (univ : Set E) ∈ 𝓝 (p,x) :=
      (H.openU.prod isOpen_univ).mem_nhds ⟨H.contains hp,mem_univ _⟩
    have he : (fun q => iteratedFDeriv ℝ 0 (a q) ξ) =ᶠ[𝓝 (p,x)]
        (fun q => iteratedFDeriv ℝ 0 (H.symbol q) ξ) := by
      refine Filter.mem_of_superset hN fun q hq => ?_
      change iteratedFDeriv ℝ 0 (a q) ξ = iteratedFDeriv ℝ 0 (H.symbol q) ξ
      have hEqq : a q ξ = H.symbol q ξ := (H.exactSymbol q.1 hq.1 q.2 ξ).symm
      simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,hEqq]
    change ‖iteratedFDeriv ℝ k (fun q => iteratedFDeriv ℝ 0 (a q) ξ) (p,x)‖ ≤ _
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    simpa only [hCoeff,Finset.sum_const_zero,smul_zero,sub_zero,angularMixedJet,
      Int.cast_one,Nat.cast_zero,sub_zero,iteratedFDeriv_zero_eq_comp,Function.comp_def] using! hBound (p,x) ⟨hp,hx⟩ ξ
  · let Kχ := angularChartSupport C.pole χ
    have hC : IsCompact Kχ := angularChartSupport_isCompact C.pole χ hχS
    have hN : (Prod.snd : Q → E) ⁻¹' Kχᶜ ∈ 𝓝 (p,x) :=
      (hC.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hx
    have he : (fun q => iteratedFDeriv ℝ 0 (a q) ξ) =ᶠ[𝓝 (p,x)] 0 := by
      refine Filter.mem_of_superset hN fun q hq => ?_
      change iteratedFDeriv ℝ 0 (a q) ξ = 0
      have hZ : a q ξ = 0 := actualVelocityChartSymbol_eq_zero_outside C A χ ζ q.1 q.2 hq ξ
      simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,hZ,map_zero]
    change ‖iteratedFDeriv ℝ k (fun q => iteratedFDeriv ℝ 0 (a q) ξ) (p,x)‖ ≤ _
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds,iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    positivity

/-- The local symbol realizations also give the exact quantization of the
same literal symbol on the whole open velocity domain. -/
theorem actualVelocityChartSymbol_quantization
    {χ η : Z → ℂ} {ζ : E → ℂ} {Kζ : Set E}
    (hLocal : ∀ J : Set P, IsCompact J → J ⊆ A.U →
      Nonempty (C.CompactVelocityRapidChart A χ η ζ Kζ J))
    {p : P} (hp : p ∈ A.U) (u : Z → ℂ) (hu : smoothNear u S) (x : E) :
    χ (angularPoint C.pole x) * A.operator p (fun z => η z*u z) (angularPoint C.pole x) =
      ∫ ξ, angularFourierPhase (dim := n+1) x ξ *
        C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ *
          angularFourierTransform (dim := n+1) (fun z => η (angularPoint C.pole z) * u (angularPoint C.pole z)) ξ := by
  obtain ⟨H⟩ := hLocal {p} isCompact_singleton (singleton_subset_iff.mpr hp)
  have hp' : p ∈ H.U := H.contains (mem_singleton _)
  simpa only [H.exactSymbol p hp'] using H.quantization p hp' u hu x

end SignedPoissonCollar

/-- Local compact quantization input for all charts, with a coordinate
cutoff fixed before each compact choice. -/
@[expose] def HasCompactVelocityRapidChart {G : BallPoissonTube P (n+1)} (A : SmoothRadialVelocity G) : Prop :=
  ∀ C : SignedPoissonCollar G,
    ∀ (χ η : Z → ℂ), smoothNear χ S → smoothNear η S →
      angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source →
      angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source →
      ∀ (ζ : E → ℂ), ContDiff ℝ ∞ ζ → ∀ Kζ : Set E, IsCompact Kζ →
        (∀ x ∉ Kζ, ζ x = 0) → EqOn ζ 1 (angularChartSupport C.pole η) →
        ∀ J : Set P, IsCompact J → J ⊆ A.U →
          Nonempty (C.CompactVelocityRapidChart A χ η ζ Kζ J)

private theorem angularChartSupport_disjoint (v : ↥S) {χ η : Z → ℂ}
    (hχ : angularSupport χ ⊆ (stereographic' ((n+1)-1) v).source)
    (hη : angularSupport η ⊆ (stereographic' ((n+1)-1) v).source)
    (hDis : Disjoint (angularSupport χ) (angularSupport η)) :
    Disjoint (angularChartSupport v χ) (angularChartSupport v η) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w,hw,rfl⟩ ⟨z,hz,he⟩
  have hzw := (stereographic' ((n+1)-1) v).injOn (hη hz) (hχ hw) he
  exact (Set.disjoint_left.mp hDis) hw (hzw ▸ hz)

/-- The exact radial velocity family has a joint smooth spherical kernel
on every pair of disjoint angular supports. -/
theorem exists_radialVelocity_offDiagonal_kernel
    (hn : 2 ≤ n+1) {G : BallPoissonTube P (n+1)} (A : SmoothRadialVelocity G)
    (hCollars : ∀ v : ↥S, ∃ C : SignedPoissonCollar G, C.pole = v)
    (hLocal : HasCompactVelocityRapidChart A)
    (χ η : Z → ℂ) (hχ : smoothNear χ S) (hη : smoothNear η S)
    (hDis : Disjoint (angularSupport χ) (angularSupport η)) :
    ∃ F : P × (Z × Z) → ℂ,
      ContDiffOn ℝ ∞ F (A.U ×ˢ univ) ∧
      ∀ p ∈ A.U, ∀ u : Z → ℂ, smoothNear u S → ∀ w : ↥S,
        χ w * A.operator p (fun z => η z*u z) w =
          ∫ z : ↥S, F (p,(w,z)) * u z ∂sphereProbability (n+1) := by
  refine exists_ambient_offDiagonal_kernel_of_rapid_chart hn A.openU Subset.rfl
    (A := A.operator) (fun p hp f hf hz w => A.operator_eq_zero_of_sphere_zero hp hf hz w)
    ?_ χ η hχ hη hDis
  intro v κ χ η hχ hη hχS hηS hDis
  obtain ⟨C,hPole⟩ := hCollars v
  have hχC : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source := by
    simpa only [hPole] using hχS
  have hηC : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source := by
    simpa only [hPole] using hηS
  let Kχ := angularChartSupport C.pole χ
  let Kη := angularChartSupport C.pole η
  have hKχ : IsCompact Kχ := angularChartSupport_isCompact C.pole χ hχC
  have hKη : IsCompact Kη := angularChartSupport_isCompact C.pole η hηC
  have hKDis : Disjoint Kχ Kη := angularChartSupport_disjoint C.pole hχC hηC hDis
  obtain ⟨ζR,hζR,hζRc,hζR1,hζRdis⟩ := exists_localizingAngularBump hKη hKχ.isClosed hKDis.symm
  let ζ : E → ℂ := Complex.ofReal ∘ ζR
  let Kζ := tsupport ζR
  have hζ : ContDiff ℝ ∞ ζ := Complex.ofRealCLM.contDiff.comp hζR
  have hζ₀ (x : E) (hx : x ∉ Kζ) : ζ x = 0 := by
    have hz : ζR x = 0 := by_contra fun hz => hx (subset_tsupport ζR hz)
    show (ζR x : ℂ) = 0
    rw [hz,Complex.ofReal_zero]
  have hζ₁ : EqOn ζ 1 Kη := by
    intro x hx
    show (ζR x : ℂ) = 1
    rw [show ζR x = 1 from hζR1 hx,Complex.ofReal_one]
  have hL := hLocal C χ η hχ hη hχC hηC ζ hζ Kζ hζRc hζ₀ hζ₁
  let a := C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ
  refine ⟨a,C.actualVelocityChartSymbol_rapid A hχC hζRdis.symm hL,?_,?_⟩
  · intro p hp x hx ξ
    apply C.actualVelocityChartSymbol_eq_zero_outside A χ ζ p x _ ξ
    simpa only [hPole] using hx
  · intro p hp u hu x
    simpa only [hPole,angularPoint,κ,a] using
      C.actualVelocityChartSymbol_quantization A hL hp u hu x

end CalderonPaper
