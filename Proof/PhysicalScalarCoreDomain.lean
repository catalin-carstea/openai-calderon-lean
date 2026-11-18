import Proof.PhysicalScalarSelfIntegral
import Proof.ScalarCovariantSelfCore
import Proof.ScalarPrincipalConnectionDrift
import Proof.CompactSupportedLpWeightedSquare
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Admissible.contDiffOn_scalarPrincipalMatrix_entry {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hSub : Y ⊆ Ω) (hK : 0 < K) (i j : I) :
    ContDiffOn ℝ ∞ (fun y => scalarPrincipalMatrix d.γ d.g₂ d.radius y i j) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have hg2 : Elliptic Y K d.g₂ :=
    ⟨fun a b => (hd.1.2.2.1.1 a b).mono hSub,fun y hy => hd.1.2.2.1.2 y (hSub hy)⟩
  simpa only [scalarPrincipalMatrix,Matrix.smul_apply,smul_eq_mul] using
    hd.2.2.2.2.1.1.mul (contDiffOn_principal_entry hg hg2 hK i j)

lemma Admissible.contDiffOn_scalarPrincipalConnectionWeight {Y Ω : Set X} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hK : 0 < K) (k : I) :
    ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d k) Y := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  exact ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ =>
    (hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK a b).mul (hg.contDiffOn_christoffel hY hK k a b)))

theorem physical_scalar_principal_core_supported
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsClosed S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) :
    (ContDiff ℝ ∞ (scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U) ∧
      ∀ y ∉ S,scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y=0) ∧
    (ContDiff ℝ ∞ (scalarCovariantSecondTransposeSection d (metricDensity d.γ)
      (scalarPrincipalMatrix d.γ d.g₂ d.radius) U) ∧
      ∀ y ∉ S,scalarCovariantSecondTransposeSection d (metricDensity d.γ)
        (scalarPrincipalMatrix d.γ d.g₂ d.radius) U y=0) := by
  have hg : Elliptic Y K d.γ :=
    ⟨fun a b => (hd.1.1.1 a b).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun y => d.frame y i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have ha := hd.contDiffOn_scalarPrincipalMatrix_entry hSub hK
  have hSym (y : X) (hy : y ∈ Y) : (scalarPrincipalMatrix d.γ d.g₂ d.radius y).IsHermitian :=
    (hd.principal_properties hK (hSub hy)).1.isHermitian.smul (by simp [isSelfAdjoint_iff])
  exact ⟨contDiff_supported_scalarCovariantSecondSection hY d hg hK he _ ha U hU S hS hSY h0U,
    contDiff_supported_scalarCovariantSecondTransposeSection hY d hg hK he _ (hg.contDiffOn_density hK)
      (fun y hy => (metricDensity_pos hg hK hy).ne') _ ha hSym U hU S hS hSY h0U⟩

theorem physical_scalar_principal_core_memLp
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hY : IsOpen Y) (hSub : Y ⊆ Ω) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (U : X → SphereSobolev 2) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (p : ℝ≥0∞) :
    MemLp (scalarCovariantSecondSection d (scalarPrincipalMatrix d.γ d.g₂ d.radius) U) p (volume.restrict Y) ∧
    MemLp (scalarCovariantSecondTransposeSection d (metricDensity d.γ)
      (scalarPrincipalMatrix d.γ d.g₂ d.radius) U) p (volume.restrict Y) := by
  have hSData := physical_scalar_principal_core_supported hY hSub hd hK U hU S hS.isClosed hSY h0U
  exact ⟨hSData.1.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hSData.1.2),
    hSData.2.1.continuous.memLp_of_hasCompactSupport (HasCompactSupport.intro hS hSData.2.2)⟩

end ShrinkingSpheres
