module

public import Proof.Manuscript.ScalarInteriorJets
public import Proof.Manuscript.ScalarAugmentationBudget

import Proof.CalderonN.CrossTensor
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory Metric CalderonN LocalMetricExtension
open scoped ContDiff Topology ENNReal

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem CoefficientBound.mono {L : ScalarElliptic n} {D O : Set (X n)}
    {a A : ℝ} {N M : ℕ} (h : L.CoefficientBound D a A N) (hOD : O ⊆ D) (hMN : M ≤ N) :
    L.CoefficientBound O a A M :=
  ⟨fun x hx => h.1 x (hOD hx),fun x hx j hj => h.2 x (hOD hx) j (hj.trans hMN)⟩

/-- Compact scalar interior estimate with its constant chosen before all
operators with the specified finite coefficient budget. -/
theorem exists_numeric_scalar_interior_jet_bound {D K : Set (X n)}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) (k : ℕ)
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ScalarElliptic n, L.SmoothOn D →
      L.CoefficientBound D a A ((fullCoordinateWord (n+3)).length + k + 2) →
      ∀ (u : ChartL2 D) {f : X n → ℝ}, L.SolvesOn D f →
      (u : X n → ℝ) =ᵐ[volume.restrict D] f →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖u‖ := by
  let : NeZero (n+3) := ⟨by omega⟩
  let U := augmentedDomain D
  let Z := zeroAuxiliarySlice '' K
  let s : X n →L[ℝ] X (n+3) := zeroAuxiliarySlice
  have hU : IsOpen U := augmentedDomain_open hD
  have hZ : IsCompact Z := hK.image s.continuous
  have hZU : Z ⊆ U := by
    rintro _ ⟨x,hx,rfl⟩
    change x ∈ (zeroAuxiliarySlice ⁻¹' augmentedDomain D)
    rw [zeroAuxiliarySlice_preimage]
    exact hKD hx
  obtain ⟨lam,Ma,hlam,_,hBudget⟩ := exists_numeric_augmented_divergence_budget (n := n)
    a A ha hA ((fullCoordinateWord (n+3)).length + k)
  obtain ⟨B,hB,hJet⟩ := exists_numeric_harmonic_interior_jet_bound hU hZ hZU k (Ma := Ma) hlam
  refine ⟨B * ‖auxProfileLp‖ * ‖s‖^k, by positivity, fun L hL hCoeff u f hf hrep x hx => ?_⟩
  have hg := augmentedMetric_smoothOnDomain hD hL
  have hSubBase : U ⊆ baseProjection ⁻¹' D := fun _ hz => hz.1
  obtain ⟨hEll,hWord⟩ := hBudget L hD hL hCoeff
  have hFloorU : Elliptic.HasEllipticityFloor
      (fun i j z => divergenceCoeff L.augmentedMetric z i j) U lam :=
    fun z hz => hEll z (hSubBase hz)
  have hWordU : Elliptic.HasWordBudget
      (fun i j z => divergenceCoeff L.augmentedMetric z i j) U Ma
      ((fullCoordinateWord (n+3)).length + k) :=
    fun z hz => hWord z (hSubBase hz)
  have hsx : s x ∈ Z := mem_image_of_mem _ hx
  have hsxU : s x ∈ U := hZU hsx
  have hComp (x : X n) : x ∈ s ⁻¹' U ↔ x ∈ D := by
    change x ∈ (zeroAuxiliarySlice ⁻¹' augmentedDomain D) ↔ _
    rw [zeroAuxiliarySlice_preimage]
  have hSub : s ⁻¹' U = D := zeroAuxiliarySlice_preimage D
  have hLift := hf.augmentedHarmonic hD hL
  have hBase : Measure.QuasiMeasurePreserving (baseProjection (n := n))
      (volume.restrict U) (volume.restrict D) :=
    Measure.quasiMeasurePreserving_fst.comp (splitAux_measurePreserving_restrict hD).quasiMeasurePreserving
  have hLiftEq : (scalarLiftL2 hD u : X (n+3) → ℝ) =ᵐ[volume.restrict U] liftedFunction f := by
    apply (scalarLiftL2_ae hD u).trans
    exact (hBase.ae_eq_comp hrep).mono fun y hy => congrArg (· * auxProfile (auxiliaryProjection y)) hy
  have h := hJet L.augmentedMetric hg hFloorU hWordU (scalarLiftL2 hD u) (liftedFunction f) hLift hLiftEq (s x) hsx
  have hDeri := s.iteratedFDerivWithin_comp_right hLift.1 hU.uniqueDiffOn
    (hU.preimage s.continuous).uniqueDiffOn hsxU (by simp : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω))
  rw [hSub, show liftedFunction f ∘ s = f from liftedFunction_zeroAuxiliarySlice f,
    iteratedFDerivWithin_eq_iteratedFDeriv hD.uniqueDiffOn
      ((hf.1.contDiffAt (hD.mem_nhds (hKD hx))).of_le (by simp)) (hKD hx),
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hLift.1.contDiffAt (hU.mem_nhds hsxU)).of_le (by simp)) hsxU] at hDeri
  rw [hDeri]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [norm_scalarLiftL2] at h
  exact (mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg _) _)).trans_eq (by ring)

end CalderonPaper.ScalarElliptic
