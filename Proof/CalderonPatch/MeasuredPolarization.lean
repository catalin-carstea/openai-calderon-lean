module

public import Proof.CalderonPatch.DirichletMinimization
public import Proof.CalderonPatch.CapGreenAgreement

import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Tactic.Linarith

public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) 1 M] [MeasurableSpace M]
  {F : Type*} [AddCommGroup F] [Module ℝ F]

local notation "J" => 𝓡∂ n
local notation "R" => 𝓘(ℝ, ℝ)

theorem integral_energy_add (g : SmoothMetric n M) (μ : Measure M)
    {u v : M → ℝ} (hu : ContMDiff J R ∞ u) (hv : ContMDiff J R ∞ v)
    (hI : ∀ a b : M → ℝ, ContMDiff J R ∞ a → ContMDiff J R ∞ b →
      Integrable (energyPairingDensity g a b) μ) :
    (∫ x, covectorEnergy g x (mfderiv J R (u + v) x) ∂μ) =
      (∫ x, covectorEnergy g x (mfderiv J R u x) ∂μ) +
      2 * (∫ x, energyPairingDensity g u v x ∂μ) +
      (∫ x, covectorEnergy g x (mfderiv J R v x) ∂μ) := by
  have hQ (f : M → ℝ) (hf : ContMDiff J R ∞ f) :
      Integrable (fun x => covectorEnergy g x (mfderiv J R f x)) μ := by
    simpa only [show energyPairingDensity g f f = _ from funext (energyPairingDensity_self g f)] using hI f f hf hf
  have hCross := (hI u v hu hv).const_mul 2
  calc
    _ = ∫ x, covectorEnergy g x (mfderiv J R u x) + 2 * energyPairingDensity g u v x +
        covectorEnergy g x (mfderiv J R v x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mfderiv_add (hu.contMDiffAt.mdifferentiableAt (by simp)) (hv.contMDiffAt.mdifferentiableAt (by simp))]
      exact covectorEnergy_add g x (mfderiv J R u x) (mfderiv J R v x)
    _ = (∫ x, covectorEnergy g x (mfderiv J R u x) + 2 * energyPairingDensity g u v x ∂μ) +
      (∫ x, covectorEnergy g x (mfderiv J R v x) ∂μ) := integral_add ((hQ u hu).add hCross) (hQ v hv)
    _ = ((∫ x, covectorEnergy g x (mfderiv J R u x) ∂μ) + (∫ x, 2 * energyPairingDensity g u v x ∂μ)) +
      (∫ x, covectorEnergy g x (mfderiv J R v x) ∂μ) :=
        congrArg (· + (∫ x, covectorEnergy g x (mfderiv J R v x) ∂μ)) (integral_add (hQ u hu) hCross)
    _ = _ := by rw [integral_const_mul]

private theorem energyPairing_eq_of_diagonal_eq {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    (u₁ u₂ : F →ₗ[ℝ] (M → ℝ)) (hS₁ : ∀ a, ContMDiff J R ∞ (u₁ a)) (hS₂ : ∀ a, ContMDiff J R ∞ (u₂ a))
    (hI₁ : ∀ a b, ContMDiff J R ∞ a → ContMDiff J R ∞ b → Integrable (energyPairingDensity g₁ a b) μ₁)
    (hI₂ : ∀ a b, ContMDiff J R ∞ a → ContMDiff J R ∞ b → Integrable (energyPairingDensity g₂ a b) μ₂)
    (hDiag : ∀ a, (∫ x, covectorEnergy g₁ x (mfderiv J R (u₁ a) x) ∂μ₁) =
      ∫ x, covectorEnergy g₂ x (mfderiv J R (u₂ a) x) ∂μ₂) (a b : F) :
    (∫ x, energyPairingDensity g₁ (u₁ a) (u₁ b) x ∂μ₁) = ∫ x, energyPairingDensity g₂ (u₂ a) (u₂ b) x ∂μ₂ := by
  have h := hDiag (a + b)
  rw [map_add, map_add, integral_energy_add g₁ μ₁ (hS₁ a) (hS₁ b) hI₁,
    integral_energy_add g₂ μ₂ (hS₂ a) (hS₂ b) hI₂, hDiag a, hDiag b] at h
  linarith

/-- The frozen measured quadratic forms determine the bilinear energy
pairing of their smooth stationary Dirichlet extensions. -/
theorem measured_energyPairing_eq {g₁ g₂ : SmoothMetric n M} {μ₁ μ₂ : Measure M}
    {Γ : Set ((J).boundary M)} (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ)
    (trace : F → M → ℝ) (hTrace : ∀ a, ContMDiff J R ∞ (trace a))
    (hSupp : ∀ a, tsupport (fun p : (J).boundary M => trace a p) ⊆ Γ)
    (u₁ u₂ : F →ₗ[ℝ] (M → ℝ)) (hS₁ : ∀ a, ContMDiff J R ∞ (u₁ a)) (hS₂ : ∀ a, ContMDiff J R ∞ (u₂ a))
    (hT₁ : ∀ a, EqOn (u₁ a) (trace a) ((J).boundary M)) (hT₂ : ∀ a, EqOn (u₂ a) (trace a) ((J).boundary M))
    (hI₁ : ∀ a b, ContMDiff J R ∞ a → ContMDiff J R ∞ b → Integrable (energyPairingDensity g₁ a b) μ₁)
    (hI₂ : ∀ a b, ContMDiff J R ∞ a → ContMDiff J R ∞ b → Integrable (energyPairingDensity g₂ a b) μ₂)
    (hW₁ : ∀ a w, ContMDiff J R ∞ w → EqOn w 0 ((J).boundary M) →
      (∫ x, energyPairingDensity g₁ (u₁ a) w x ∂μ₁) = 0)
    (hW₂ : ∀ a w, ContMDiff J R ∞ w → EqOn w 0 ((J).boundary M) →
      (∫ x, energyPairingDensity g₂ (u₂ a) w x ∂μ₂) = 0) :
    ∀ a b, (∫ x, energyPairingDensity g₁ (u₁ a) (u₁ b) x ∂μ₁) =
      ∫ x, energyPairingDensity g₂ (u₂ a) (u₂ b) x ∂μ₂ := by
  apply energyPairing_eq_of_diagonal_eq u₁ u₂ hS₁ hS₂ hI₁ hI₂
  intro a
  rw [← dirichletQuadraticEnergy_eq_of_stationary g₁ μ₁ (hS₁ a) (hT₁ a) hI₁ (hW₁ a),
    ← dirichletQuadraticEnergy_eq_of_stationary g₂ μ₂ (hS₂ a) (hT₂ a) hI₂ (hW₂ a)]
  exact hEnergy (trace a) (hTrace a) (hSupp a)

/-- Equality of the measured quadratic energies implies equality of
the relevant bilinear pairings for any common supported trace of the
tests. Smooth stationary extensions are only needed for the two trace
classes involved in the polarization. -/
theorem integral_energyPairing_eq_of_patchEnergy {g₁ g₂ : SmoothMetric n M}
    {μ₁ μ₂ : Measure M} {Γ : Set ((J).boundary M)}
    (hEnergy : PatchEnergyEqual g₁ g₂ μ₁ μ₂ Γ)
    {u₁ u₂ v₁ v₂ w₁ w₂ : M → ℝ}
    (hu₁ : ContMDiff J R ∞ u₁) (hu₂ : ContMDiff J R ∞ u₂)
    (hv₁ : ContMDiff J R ∞ v₁) (hv₂ : ContMDiff J R ∞ v₂)
    (hw₁ : ContMDiff J R ∞ w₁) (hw₂ : ContMDiff J R ∞ w₂)
    (hU : EqOn u₁ u₂ ((J).boundary M))
    (hW₁ : EqOn w₁ v₁ ((J).boundary M)) (hW₂ : EqOn w₂ v₂ ((J).boundary M))
    (hV : EqOn v₁ v₂ ((J).boundary M))
    (hUS : tsupport (fun p : (J).boundary M => u₁ p) ⊆ Γ)
    (hVS : tsupport (fun p : (J).boundary M => v₁ p) ⊆ Γ)
    (hStaU₁ : IsDirichletStationary g₁ μ₁ u₁) (hStaU₂ : IsDirichletStationary g₂ μ₂ u₂)
    (hStaW₁ : IsDirichletStationary g₁ μ₁ w₁) (hStaW₂ : IsDirichletStationary g₂ μ₂ w₂)
    (hI₁ : ∀ a b : M → ℝ, ContMDiff J R ∞ a → ContMDiff J R ∞ b →
      Integrable (energyPairingDensity g₁ a b) μ₁)
    (hI₂ : ∀ a b : M → ℝ, ContMDiff J R ∞ a → ContMDiff J R ∞ b →
      Integrable (energyPairingDensity g₂ a b) μ₂) :
    (∫ x, energyPairingDensity g₁ u₁ v₁ x ∂μ₁) =
      ∫ x, energyPairingDensity g₂ u₂ v₂ x ∂μ₂ := by
  have hDiagonal {f a b : M → ℝ} (hf : ContMDiff J R ∞ f)
      (hfS : tsupport (fun p : (J).boundary M => f p) ⊆ Γ)
      (ha : ContMDiff J R ∞ a) (hb : ContMDiff J R ∞ b)
      (haT : EqOn a f ((J).boundary M)) (hbT : EqOn b f ((J).boundary M))
      (hStaA : IsDirichletStationary g₁ μ₁ a) (hStaB : IsDirichletStationary g₂ μ₂ b) :
      (∫ x, covectorEnergy g₁ x (mfderiv J R a x) ∂μ₁) =
        ∫ x, covectorEnergy g₂ x (mfderiv J R b x) ∂μ₂ := by
    rw [← dirichletQuadraticEnergy_eq_of_stationary g₁ μ₁ ha haT hI₁ hStaA,
      ← dirichletQuadraticEnergy_eq_of_stationary g₂ μ₂ hb hbT hI₂ hStaB]
    exact hEnergy f hf hfS
  have hUV : tsupport (fun p : (J).boundary M => (u₁ + v₁) p) ⊆ Γ := by
    apply (closure_minimal _
      ((isClosed_tsupport (fun p : (J).boundary M => u₁ p)).union
        (isClosed_tsupport (fun p : (J).boundary M => v₁ p)))).trans (union_subset hUS hVS)
    intro p hp
    by_contra hn
    change u₁ p + v₁ p ≠ 0 at hp
    rw [image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inl h)),
      image_eq_zero_of_notMem_tsupport (fun h => hn (Or.inr h)),zero_add] at hp
    exact hp rfl
  have hSum₁ : EqOn (u₁ + w₁) (u₁ + v₁) ((J).boundary M) :=
    fun x hx => congrArg (u₁ x + ·) (hW₁ hx)
  have hSum₂ : EqOn (u₂ + w₂) (u₁ + v₁) ((J).boundary M) :=
    fun x hx => congrArg₂ (· + ·) (hU hx).symm ((hW₂ hx).trans (hV hx).symm)
  have hD₁ := hDiagonal hu₁ hUS hu₁ hu₂ (fun _ _ => rfl) hU.symm hStaU₁ hStaU₂
  have hD₂ := hDiagonal hv₁ hVS hw₁ hw₂ hW₁ (hW₂.trans hV.symm) hStaW₁ hStaW₂
  have hD := hDiagonal (hu₁.add hv₁) hUV (hu₁.add hw₁) (hu₂.add hw₂) hSum₁ hSum₂
    (hStaU₁.add hStaW₁ hu₁ hw₁ hI₁) (hStaU₂.add hStaW₂ hu₂ hw₂ hI₂)
  rw [integral_energy_add g₁ μ₁ hu₁ hw₁ hI₁, integral_energy_add g₂ μ₂ hu₂ hw₂ hI₂,
    hD₁,hD₂] at hD
  rw [hStaU₁.integral_eq_of_same_trace hu₁ hv₁ hw₁ hW₁.symm hI₁,
    hStaU₂.integral_eq_of_same_trace hu₂ hv₂ hw₂ hW₂.symm hI₂]
  linarith

omit [AddCommGroup F] [Module ℝ F] in
/-- In a boundary chart, the measured pairings distinguish continuous
conormal derivatives when the same positive boundary density is used. -/
theorem boundaryConormal_eq_of_measured_pairings {d : ℕ} {U : Set (CalderonN.X d)} (hU : IsOpen U)
    {ρ : CalderonN.X d → ℝ} (hρ : ContinuousOn ρ U) (hρpos : ∀ x ∈ U, 0 < ρ x)
    (flux₁ flux₂ : F → CalderonN.X d → ℝ)
    (hC₁ : ∀ a, ContinuousOn (flux₁ a) U) (hC₂ : ∀ a, ContinuousOn (flux₂ a) U)
    (B₁ B₂ : F → F → ℝ) (hB : ∀ a b, B₁ a b = B₂ a b)
    (hTest : ∀ φ : CalderonN.X d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∃ b : F, ∀ a, (∫ x in U, φ x * flux₁ a x * ρ x) = B₁ a b ∧ (∫ x in U, φ x * flux₂ a x * ρ x) = B₂ a b) :
    ∀ a, EqOn (flux₁ a) (flux₂ a) U := by
  intro a
  apply eqOn_of_weighted_test_pairings hU Subset.rfl hρ hρpos (hC₁ a) (hC₂ a)
  intro φ hφ hφc hφs
  obtain ⟨b, hb⟩ := hTest φ hφ hφc hφs
  exact (hb a).1.trans ((hB a b).trans (hb a).2.symm)

end CalderonPatch
