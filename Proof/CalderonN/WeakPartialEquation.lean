module

public import Proof.CalderonN.WeakTest
import Mathlib.Tactic

@[expose] public section

/-! Differentiation in a constant coordinate direction. The argument uses the
test function integration by parts and weak mixed-partial symmetry from the
released 3D proof, over a finite index set of arbitrary cardinality. -/
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ContDiff Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonN.WeakTest
open TauCeti TauCeti.PDE WkpCalculus
variable {n : ℕ} {Ω : Opens (X n)}

theorem gradient_d1_coordinate (U : Wkp (volume : Measure (X n)) Ω 2 2) (k j : Fin n) :
    (fun x => W1p.gradient (d1 k U) x j) =ᵐ[(volume : Measure (X n)).restrict Ω]
      (fun x => Wkp.iteratedGradient 1 U x (WeakTest.e j) k) := by
  rw [gradient_d1]
  filter_upwards [ContinuousLinearMap.coeFn_compLp (contr k 0) (Wkp.iteratedGradient 1 U)] with x hx
  rw [hx]
  change (EuclideanSpace.proj j : X n →L[ℝ] ℝ) ((contr k 0) (Wkp.iteratedGradient 1 U x)) = _
  simp only [contr, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_smul, WkpCalculus.e, WeakTest.e]
  simp [eq_comm]
  rfl

/-- The scalar forcing after differentiating the divergence equation in coordinate `k`. -/
def partialForcing (a : X n → Mat n) (k : Fin n)
    (U : Wkp (volume : Measure (X n)) Ω 2 2)
    (F : W1p (volume : Measure (X n)) Ω 2) (x : X n) : ℝ :=
  W1p.gradient F x k + ∑ i, ∑ j,
    (pd (pd (fun y => a y i j) k) i x * W1p.gradient (Wkp.lowerOrder 1 U) x j +
      pd (fun y => a y i j) k x * Wkp.iteratedGradient 1 U x (WeakTest.e i) j)

set_option maxHeartbeats 3500000 in
theorem partial_test_equation {a : X n → Mat n} (ha : ContDiff ℝ ∞ a)
    (U : Wkp (volume : Measure (X n)) Ω 2 2)
    (F : W1p (volume : Measure (X n)) Ω 2)
    (heq : ∀ ψ : 𝓓(Ω, ℝ), ∫ x, matrixBilinearForm (a x) (gradient (ψ : X n → ℝ) x)
      (W1p.gradient (Wkp.lowerOrder 1 U) x) = ∫ x, W1p.value F x * ψ x)
    (k : Fin n) (φ : 𝓓(Ω, ℝ)) :
    (∫ x in (Ω : Set (X n)), matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
      (W1p.gradient (d1 k U) x)) =
      ∫ x, φ x * partialForcing a k U F x := by
  let u := Wkp.lowerOrder 1 U
  let G := (W1p.gradient u : X n → X n)
  let D := (Wkp.iteratedGradient 1 U : X n → X n →L[ℝ] X n)
  have hG : HasWeakFDerivOn volume Ω G D := by
    simpa [G, D, u, Wkp.iteratedGradient_zero] using Wkp.hasWeakFDerivOn_iteratedGradient 0 U
  have hu := W1p.hasWeakFDerivOn u
  have hF := coordDeriv (W1p.hasWeakFDerivOn F) k
  have hφ := TF.of φ
  let A := fun (i j : Fin n) (x : X n) => a x i j
  let B := fun (i j : Fin n) => pd (A i j) k
  have hA i j : ContDiff ℝ ∞ (A i j) := contDiff_entry ha i j
  have hB i j : ContDiff ℝ ∞ (B i j) :=
    (((hA i j).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const)
  let L := fun (i j : Fin n) (x : X n) => pd φ i x * (A i j x * D x (WeakTest.e j) k)
  let T := fun (i j : Fin n) (x : X n) => pd (pd φ k) i x * (A i j x * G x j)
  let H := fun (i j : Fin n) (x : X n) => φ x *
    (pd (B i j) i x * G x j + B i j x * D x (WeakTest.e i) j)
  have hflux (i j : Fin n) : HasWeakLineDerivOn volume Ω
      (fun x => A i j x * G x j)
      (fun x => B i j x * G x j + A i j x * D x (WeakTest.e j) k) (WeakTest.e k) := by
    simpa [B, pd, smul_eq_mul, add_comm] using
      (HasWeakLineDerivOn.contDiff_smul (symmDeriv hu hG j k) (hA i j))
  have hcomm (i j : Fin n) : HasWeakLineDerivOn volume Ω
      (fun x => B i j x * G x j)
      (fun x => pd (B i j) i x * G x j + B i j x * D x (WeakTest.e i) j) (WeakTest.e i) := by
    simpa [pd, smul_eq_mul, add_comm] using
      (HasWeakLineDerivOn.contDiff_smul (vecDeriv hG j i) (hB i j))
  have hL i j : Integrable (L i j) :=
    ((hφ.deriv i).mul (hA i j)).integrable (symmDeriv hu hG j k).locallyIntegrableOn_deriv
      |>.congr (Eventually.of_forall fun x => by simp [L, mul_assoc])
  have hT i j : Integrable (T i j) :=
    ((hφ.deriv k).deriv i).integrable (hflux i j).locallyIntegrableOn
  have hH i j : Integrable (H i j) := hφ.integrable (hcomm i j).locallyIntegrableOn_deriv
  have hrow (i j : Fin n) : ∫ x, L i j x = (-(∫ x, T i j x) + ∫ x, H i j x) := by
    have hR := (hφ.deriv i).ibp (hflux i j)
    simp only [pd_pd_comm φ.contDiff i k, mul_add] at hR
    have hR2 := hφ.ibp (hcomm i j)
    have hI := (hφ.deriv i).integrable (hcomm i j).locallyIntegrableOn
    rw [integral_add hI (hL i j)] at hR
    change (∫ x, pd φ i x * (B i j x * G x j)) + (∫ x, L i j x) = -(∫ x, T i j x) at hR
    change (∫ x, H i j x) = -(∫ x, pd φ i x * (B i j x * G x j)) at hR2
    linarith
  have hsumL : Integrable (fun x => ∑ i, ∑ j, L i j x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hL i j
  have hsumT : Integrable (fun x => ∑ i, ∑ j, T i j x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hT i j
  have hsumH : Integrable (fun x => ∑ i, ∑ j, H i j x) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hH i j
  have hsum : (∫ x, ∑ i, ∑ j, L i j x) =
      -(∫ x, ∑ i, ∑ j, T i j x) + ∫ x, ∑ i, ∑ j, H i j x := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hL i j),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hT i j),
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hH i j)]
    simp_rw [integral_finsetSum _ (fun j _ => hL _ j),
      integral_finsetSum _ (fun j _ => hT _ j), integral_finsetSum _ (fun j _ => hH _ j), hrow,
      Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hlhs : (∫ x in (Ω : Set (X n)), matrixBilinearForm (a x) (gradient (φ : X n → ℝ) x)
      (W1p.gradient (d1 k U) x)) = ∫ x, ∑ i, ∑ j, L i j x := by
    rw [integral_eq_setIntegral (Ω := Ω) (Z := fun x => ∑ i, ∑ j, L i j x)
      (fun x hx => by simp [L, (hφ.deriv _).zero_of_notMem hx])]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.mpr (gradient_d1_coordinate U k)] with x hx
    simp only [matrixBilinearForm_eq_sum, gradient_coord, hx, L, A, D]
  obtain ⟨ψ, hψ⟩ := hφ.deriv k
  have hT_eq : (∫ x, ∑ i, ∑ j, T i j x) = ∫ x, W1p.value F x * pd φ k x := by
    simpa only [matrixBilinearForm_eq_sum, gradient_coord, hψ, T, A, G, u] using heq ψ
  have hF_eq := hφ.ibp hF
  have hH_eq : (∫ x, ∑ i, ∑ j, H i j x) =
      ∫ x, φ x * (∑ i, ∑ j, (pd (B i j) i x * G x j +
        B i j x * D x (WeakTest.e i) j)) := by
    simp only [H, Finset.mul_sum]
  rw [hlhs, hsum, hT_eq, show (∫ x, W1p.value F x * pd φ k x) =
    ∫ x, pd φ k x * W1p.value F x from integral_congr_ae
      (Eventually.of_forall fun x => mul_comm _ _), hH_eq]
  have hF_reverse : -(∫ x, pd φ k x * W1p.value F x) =
      ∫ x, φ x * W1p.gradient F x k := hF_eq.symm
  rw [hF_reverse]
  have hI : Integrable (fun x => φ x * (∑ i, ∑ j, (pd (B i j) i x * G x j +
      B i j x * D x (WeakTest.e i) j))) := by simpa only [H, Finset.mul_sum] using hsumH
  rw [← integral_add (hφ.integrable hF.locallyIntegrableOn_deriv) hI]
  simp only [partialForcing, B, A, G, u, D, mul_add]

end CalderonN.WeakTest
