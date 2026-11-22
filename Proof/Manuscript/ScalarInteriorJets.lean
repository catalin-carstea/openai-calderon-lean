module

public import Proof.Manuscript.ScalarSolutionSpace

import Proof.CalderonN.ClassicalInteriorJets
import Mathlib.Tactic

public section

open Set Metric Filter MeasureTheory CalderonN
open scoped ContDiff Topology

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

@[expose] def zeroAuxiliarySlice : X n →L[ℝ] X (n+3) :=
  splitAux.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (X n) (X 3))

theorem zeroAuxiliarySlice_apply (x : X n) :
    splitAux (zeroAuxiliarySlice x) = (x,0) :=
  splitAux.apply_symm_apply _

theorem liftedFunction_zeroAuxiliarySlice (u : X n → ℝ) :
    liftedFunction u ∘ zeroAuxiliarySlice = u := by
  funext x
  have h := zeroAuxiliarySlice_apply x
  have h₁ : baseProjection (zeroAuxiliarySlice x) = x := congrArg Prod.fst h
  have h₂ : auxiliaryProjection (zeroAuxiliarySlice x) = 0 := congrArg Prod.snd h
  simp [liftedFunction,h₁,h₂,auxProfile]

theorem zeroAuxiliarySlice_preimage (D : Set (X n)) :
    zeroAuxiliarySlice ⁻¹' augmentedDomain D = D := by
  ext x
  change splitAux (zeroAuxiliarySlice x) ∈ D ×ˢ auxiliaryBall ↔ _
  rw [zeroAuxiliarySlice_apply]
  exact ⟨And.left, fun hx => ⟨hx,mem_ball_self one_pos⟩⟩

/-- Each fixed scalar operator has the same local L²-to-jet interface
as the released harmonic solution Hilbert space. -/
theorem exists_scalar_interior_jet_bound {L : ScalarElliptic n} {D K : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (hK : IsCompact K) (hKD : K ⊆ D) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
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
  have hg := augmentedMetric_smoothOnDomain hD hL
  have hjoint (i j : I (n+3)) :
      ContDiffOn ℝ ∞ (fun q : ℝ × X (n+3) => divergenceCoeff L.augmentedMetric q.2 i j)
        (univ ×ˢ U) :=
    (contDiffOn_divergenceCoeff hg i j).comp contDiff_snd.contDiffOn (fun _ h => h.2)
  obtain ⟨A,hA,hJet⟩ := exists_uniform_harmonic_interior_jet_bound (g := fun _ : ℝ => L.augmentedMetric)
     (isCompact_singleton (x := (0 : ℝ))) hU (fun _ _ => hg) hjoint hZ hZU k
  refine ⟨A * ‖auxProfileLp‖ * ‖s‖^k, by positivity, fun u f hf hrep x hx => ?_⟩
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
  have h := hJet 0 (mem_singleton _) (scalarLiftL2 hD u) (liftedFunction f) hLift hLiftEq (s x) hsx
  have hDeri := s.iteratedFDerivWithin_comp_right hLift.1 hU.uniqueDiffOn
    (hU.preimage s.continuous).uniqueDiffOn hsxU (by simp : (k : WithTop ℕ∞) ≤ ∞)
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
