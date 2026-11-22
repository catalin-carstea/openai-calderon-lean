module

public import Proof.CalderonN.TestHarmonicCoordinates
public import Proof.CalderonN.ComplexZonalProjection

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MeasureTheory MvPolynomial Filter
open scoped ContDiff
namespace CalderonN
variable {N : ℕ} [NeZero N]
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.AngularPolynomial

lemma harmonicProjection_zero_of_integral_zero (hn : 3 ≤ N) (u : (SphereL2 N))
    (hu : (∫ v : (UnitSphere N),u v ∂(unitSphereProbability N)) = 0) : harmonicProjection 0 u = 0 := by
  have hp : (harmonicProjectionPolynomial 0 u).val = 0 := by
    let p := (harmonicProjectionPolynomial 0 u).val
    apply (polynomialSphereL2_eq_zero_iff (sphereFischerInner N) 0 _
      (harmonicProjectionPolynomial 0 u).property).mp
    apply Lp.ext
    filter_upwards [(polynomialSphere p).coeFn_toLp (p := 2) (𝕜 := ℝ) (unitSphereProbability N),
      Lp.coeFn_zero (E := ℝ) (p := 2) (unitSphereProbability N)] with v hpv hz
    have h := sphere_zonal_projection_Lp hn v 0 u
    rw [harmonicMultiplicity, Nat.cast_one, one_mul] at h
    simp only [zonal, one_mul, hu] at h
    exact hpv.trans (h.symm.trans hz.symm)
  apply Subtype.ext
  change (harmonicProjection 0 u : (SphereL2 N)) = 0
  rw [← polynomialSphereL2_harmonicProjectionPolynomial,hp,map_zero]

/-- The actual physical mean-zero condition removes the degree-zero component of both
    Hilbert sections. All integrability here comes from L2 on the probability sphere. -/
theorem Test.harmonicProjection_zero (hn : 3 ≤ N) {Y : Set (X N)} {g : (MetricField N)} {e : (Frame N)} {φ : (Field N)}
    (hφ : Test Y g e φ) (y : (X N)) (hy : y ∈ Y) (U V : (SphereL2 N))
    (hRe : U =ᵐ[(unitSphereProbability N)] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).re))
    (hIm : V =ᵐ[(unitSphereProbability N)] (fun v : (UnitSphere N) => (φ (y,frameVector e y v.val)).im)) :
    harmonicProjection 0 U = 0 ∧ harmonicProjection 0 V = 0 := by
  have hiU : Integrable U (unitSphereProbability N) := (Lp.memLp U).integrable (by norm_num)
  have hiV : Integrable V (unitSphereProbability N) := (Lp.memLp V).integrable (by norm_num)
  have heq : (∫ v : (UnitSphere N),Complex.mk (U v) (V v) ∂(unitSphereProbability N)) = 0 := by
    calc
      _ = ∫ v : (UnitSphere N),φ (y,frameVector e y v.val) ∂(unitSphereProbability N) := by
        apply integral_congr_ae
        filter_upwards [hRe,hIm] with v hr hi
        apply Complex.ext <;> assumption
      _ = 0 := hφ.2.2 y hy
  rw [integral_complexMk_of_integrable hiU hiV] at heq
  exact ⟨harmonicProjection_zero_of_integral_zero hn U (congrArg Complex.re heq),
    harmonicProjection_zero_of_integral_zero hn V (congrArg Complex.im heq)⟩

end CalderonN
