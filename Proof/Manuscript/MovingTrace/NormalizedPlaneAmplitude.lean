module

public import Proof.CalderonN.CompactSmoothExtension
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Proof.Manuscript.MovingTraceSymbols
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2300000

open CalderonN Set Metric
open scoped ContDiff Topology

namespace CalderonPaper

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The cutoff is one on an open neighborhood of the prescribed compact
set and its closed support is contained in the original open set. -/
theorem exists_compact_bump_one_near {U K : Set P} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (χ : P → ℝ) (V : Set P), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn χ 1 V := by
  obtain ⟨W,hW,hKW,hWU,hWc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V,hV,hKV,hVW,hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨χ,hχ,_,hSupp,hOne⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hW isClosed_closure hVW
  refine ⟨χ,V,hχ,?_,?_,hV,hKV,subset_closure.trans (hVW.trans (subset_closure.trans hWU)),?_⟩
  · simpa only [HasCompactSupport,tsupport,hSupp] using hWc
  · simpa only [tsupport,hSupp] using hWU
  · intro x hx
    exact (hOne x).mp (subset_closure hx)

def unitAnnulus (E : Type*) [Norm E] : Set E := {ν | (1/2:ℝ) ≤ ‖ν‖ ∧ ‖ν‖ ≤ 2}

theorem unitAnnulus_isCompact : IsCompact (unitAnnulus E) := by
  apply (isCompact_closedBall (0 : E) 2).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  · exact fun _ h => by simpa only [Metric.mem_closedBall,dist_zero_right] using h.2

theorem unitAnnulus_ne_zero : unitAnnulus E ⊆ ({0}ᶜ : Set E) := by
  intro ν hν h
  have hν0 : ν = 0 := mem_singleton_iff.mp h
  have hνp : (1/2:ℝ) ≤ ‖ν‖ := hν.1
  rw [hν0,norm_zero] at hνp
  norm_num at hνp

theorem unitDirection_mem_unitAnnulus (ν : E) (hν : ‖ν‖ = 1) : ν ∈ unitAnnulus E := by
  change (1/2:ℝ) ≤ ‖ν‖ ∧ ‖ν‖ ≤ 2
  rw [hν]
  norm_num

/-- The finite-layer datum agrees with the original angular datum on an
open neighborhood of the compact geometry and frequency annulus. -/
theorem exists_normalized_plane_amplitude {V J : Set P} (hV : IsOpen V)
    (hJ : IsCompact J) (hJV : J ⊆ V)
    {Ka : Set E} (hKa : IsCompact Ka) (a : P × E → ℂ) (ha : ContDiff ℝ ∞ a)
    (ha₀ : ∀ p x, x ∉ Ka → a (p,x) = 0) :
    ∃ (U : Set P) (D : Set E) (K : Set ((P × E) × E)) (b : (P × E) × E → ℂ),
      IsOpen U ∧ J ⊆ U ∧ U ⊆ V ∧
      IsOpen D ∧ unitAnnulus E ⊆ D ∧ D ⊆ {0}ᶜ ∧
      IsCompact K ∧ K ⊆ (V ×ˢ ({0}ᶜ : Set E)) ×ˢ univ ∧ (∀ q ∈ K, q.2 ∈ Ka) ∧
      ContDiff ℝ ∞ b ∧ (∀ q ∉ K, b q = 0) ∧
      ∀ p ∈ U, ∀ ν ∈ D, ∀ x : E, b ((p,ν),x) = a (p,x) := by
  obtain ⟨χ,U,hχ,hχc,hχV,hU,hJU,hUV,hOne⟩ := exists_compact_bump_one_near hV hJ hJV
  obtain ⟨η,D,hη,hηc,hηD,hD,hND,hD₀,hηOne⟩ := exists_compact_bump_one_near
    (isOpen_compl_singleton (x := (0:E))) (unitAnnulus_isCompact (E := E)) unitAnnulus_ne_zero
  let K := (tsupport χ ×ˢ tsupport η) ×ˢ Ka
  let b (q : (P × E) × E) := (χ q.1.1 * η q.1.2 : ℝ) • a (q.1.1,q.2)
  have hb : ContDiff ℝ ∞ b :=
    (((hχ.comp contDiff_fst.fst).mul (hη.comp contDiff_fst.snd)).smul
      (ha.comp (contDiff_fst.fst.prodMk contDiff_snd)))
  refine ⟨U,D,K,b,hU,hJU,hUV,hD,hND,hD₀,(hχc.isCompact.prod hηc.isCompact).prod hKa,
    fun q hq => ⟨⟨hχV hq.1.1,hηD hq.1.2⟩,mem_univ _⟩,fun q hq => hq.2,hb,?_,?_⟩
  · intro q hq
    by_cases h₁ : q.1.1 ∈ tsupport χ
    · by_cases h₂ : q.1.2 ∈ tsupport η
      · simp [b,ha₀ q.1.1 q.2 (fun h => hq ⟨⟨h₁,h₂⟩,h⟩)]
      · simp [b,image_eq_zero_of_notMem_tsupport h₂]
    · simp [b,image_eq_zero_of_notMem_tsupport h₁]
  · intro p hp ν hν x
    simp [b,show χ p = 1 from hOne hp,show η ν = 1 from hηOne hν]

end CalderonPaper
