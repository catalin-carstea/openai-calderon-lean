module

public import Proof.CalderonN.ZonalProjection
public import Proof.CalderonN.PolynomialFamilies
public import Proof.CalderonN.SmoothSphereFields

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.AngularPolynomial
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Two smooth compact L2 fields have harmonic coordinates in one fixed finite polynomial
    family. This supplies common real/imaginary coordinates for complex angular projection. -/
theorem exists_common_harmonic_coordinates (k : ℕ) (U V : (X N) → (SphereL2 N))
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V) (K : Set (X N)) (hK : IsCompact K)
    (hzeroU : ∀ x ∉ K,U x = 0) (hzeroV : ∀ x ∉ K,V x = 0) :
    ∃ n : ℕ,∃ b : Fin n → MvPolynomial (I N) ℝ,∃ c d : (X N) → Fin n → ℝ,
      (∀ j,b j ∈ harmonicHomogeneous N k) ∧ ContDiff ℝ ∞ c ∧ ContDiff ℝ ∞ d ∧
      HasCompactSupport c ∧ HasCompactSupport d ∧ tsupport c ⊆ K ∧ tsupport d ⊆ K ∧
      (∀ x,polynomialSphereL2 (finitePolynomialField b c x) = (harmonicProjection k (U x) : (SphereL2 N))) ∧
      (∀ x,polynomialSphereL2 (finitePolynomialField b d x) = (harmonicProjection k (V x) : (SphereL2 N))) := by
  classical
  let B := Module.finBasis ℝ (harmonicSphereSubspace N k)
  have hex : ∀ j,∃ p : MvPolynomial (I N) ℝ,p ∈ harmonicHomogeneous N k ∧ polynomialSphereL2 p = (B j : (SphereL2 N)) := by
    intro j
    exact (B j).property
  choose b hb hrep using hex
  let c : (X N) → Fin (Module.finrank ℝ (harmonicSphereSubspace N k)) → ℝ :=
    fun x => B.equivFunL (harmonicProjection k (U x))
  let d : (X N) → Fin (Module.finrank ℝ (harmonicSphereSubspace N k)) → ℝ :=
    fun x => B.equivFunL (harmonicProjection k (V x))
  have hc : ContDiff ℝ ∞ c := B.equivFunL.contDiff.comp ((harmonicProjection k).contDiff.comp hU)
  have hd : ContDiff ℝ ∞ d := B.equivFunL.contDiff.comp ((harmonicProjection k).contDiff.comp hV)
  have hcz (x : (X N)) (hx : x ∉ K) : c x = 0 := by simp only [c,hzeroU x hx,map_zero]
  have hdz (x : (X N)) (hx : x ∉ K) : d x = 0 := by simp only [d,hzeroV x hx,map_zero]
  have hsuppc : tsupport c ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (hcz x hn)
  have hsuppd : tsupport d ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (hdz x hn)
  have hcompc : HasCompactSupport c := hK.of_isClosed_subset (isClosed_tsupport c) hsuppc
  have hcompd : HasCompactSupport d := hK.of_isClosed_subset (isClosed_tsupport d) hsuppd
  have hrec (v : harmonicSphereSubspace N k) :
      polynomialSphereL2 (∑ j,B.equivFunL v j • b j) = (v : (SphereL2 N)) := by
    rw [map_sum]
    simp_rw [map_smul,hrep]
    have hh := congrArg (fun v : harmonicSphereSubspace N k => (v : (SphereL2 N))) (B.sum_repr v)
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Module.Basis.equivFunL_apply,
      Module.Basis.equivFun_apply] using hh
  refine ⟨_,b,c,d,hb,hc,hd,hcompc,hcompd,hsuppc,hsuppd,?_,?_⟩
  · intro x
    exact hrec (harmonicProjection k (U x))
  · intro x
    exact hrec (harmonicProjection k (V x))

end CalderonN
