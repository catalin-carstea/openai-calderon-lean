module

public import Proof.CalderonN.WeakPartialEquation
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.Regularity.SmoothFlatBoundary

import Proof.ReleasedAnalysis.TauCeti.MeasureTheory.Function.LocallyIntegrableOperations
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic

public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace TauCeti TauCeti.PDE
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPatch

open CalderonN
open CalderonN.WeakTest (TF pd)

variable {n : ℕ} {Ω : Opens (X n)}
local notation "E" => X n
local notation "μ" => (volume : Measure E)

/-- Recover the strong divergence equation for a genuine H² reading.
The mixed second derivatives are represented by its Sobolev Hessian. -/
theorem ae_principal_equation_of_wkp_two {a : E → Mat n} (ha : ContDiff ℝ ∞ a)
    (w : Wkp μ Ω 2 2) (f : Lp ℝ 2 ((μ).restrict Ω))
    (hu : ∀ φ : 𝓓(Ω,ℝ),
      (∫ x, matrixBilinearForm (a x) (gradient (φ : E → ℝ) x)
        (W1p.gradient (Wkp.lowerOrder 1 w) x) ∂μ) = ∫ x, f x * φ x ∂μ) :
    ∀ᵐ x ∂(μ).restrict Ω, f x + ∑ i, ∑ j,
      (pd (fun z => a z i j) i x * W1p.gradient (Wkp.lowerOrder 1 w) x j +
        a x i j * Wkp.iteratedGradient 1 w x (WeakTest.e i) j) = 0 := by
  let G := (W1p.gradient (Wkp.lowerOrder 1 w) : E → E)
  let D := (Wkp.iteratedGradient 1 w : E → E →L[ℝ] E)
  let A (i j : Fin n) (x : E) := a x i j
  let B (i j : Fin n) (x : E) := pd (A i j) i x * G x j + A i j x * D x (WeakTest.e i) j
  let R (x : E) := ∑ i, ∑ j, B i j x
  have hG : HasWeakFDerivOn μ Ω G D := by
    simpa only [G,D,Wkp.iteratedGradient_zero] using Wkp.hasWeakFDerivOn_iteratedGradient 0 w
  have hB (i j : Fin n) : HasWeakLineDerivOn μ Ω (fun x => A i j x * G x j)
      (B i j) (WeakTest.e i) := by
    simpa [B,pd,smul_eq_mul,add_comm] using
      HasWeakLineDerivOn.contDiff_smul (WeakTest.vecDeriv hG j i) (WeakTest.contDiff_entry ha i j)
  have hR : LocallyIntegrableOn R Ω μ := locallyIntegrableOn_finsetSum Finset.univ fun i _ =>
    locallyIntegrableOn_finsetSum Finset.univ fun j _ => (hB i j).locallyIntegrableOn_deriv
  have hf : LocallyIntegrableOn (f : E → ℝ) Ω μ := locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable (by norm_num))
  have htest (φ : 𝓓(Ω,ℝ)) :
      ∫ x, φ x * (f x + R x) ∂μ = 0 := by
    have hφ : TF Ω φ := TF.of φ
    have hI (i j : Fin n) : Integrable (fun x => pd φ i x * (A i j x * G x j)) μ :=
      (hφ.deriv i).integrable (hB i j).locallyIntegrableOn
    have hJ (i j : Fin n) : Integrable (fun x => φ x * B i j x) μ :=
      hφ.integrable (hB i j).locallyIntegrableOn_deriv
    have hsumL : (∫ x, matrixBilinearForm (a x) (gradient (φ : E → ℝ) x) (G x) ∂μ) =
        ∑ i, ∑ j, ∫ x, pd φ i x * (A i j x * G x j) ∂μ := by
      simp only [WeakTest.matrixBilinearForm_eq_sum, WeakTest.gradient_coord, A]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
      exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hI i j)
    have hsumR : (∫ x, φ x * R x ∂μ) = ∑ i, ∑ j, ∫ x, φ x * B i j x ∂μ := by
      simp only [R,Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hJ i j))]
      exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hJ i j)
    have hF : (∫ x, φ x * f x ∂μ) =
        ∑ i, ∑ j, -(∫ x, φ x * B i j x ∂μ) := by
      calc
        _ = (∫ x, f x * φ x ∂μ) := integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
        _ = _ := (hu φ).symm.trans hsumL
        _ = _ := Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by
            rw [hφ.ibp (hB i j),neg_neg]
    simp_rw [mul_add]
    rw [integral_add (hφ.integrable hf) (hφ.integrable hR),hF,hsumR]
    simp only [Finset.sum_neg_distrib,neg_add_cancel]
  have hzero := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.add hR) (by
    intro φ hφ hφc hφs
    let Φ : 𝓓(Ω,ℝ) := ⟨φ,hφ,hφc,hφs⟩
    exact htest Φ)
  rw [ae_restrict_iff' Ω.isOpen.measurableSet]
  exact hzero

/-- Coordinate entries of the weak Hessian of a scalar Sobolev
function commute almost everywhere. -/
theorem wkp_two_hessian_symm (w : Wkp μ Ω 2 2) (i j : Fin n) :
    (fun x => Wkp.iteratedGradient 1 w x (WeakTest.e i) j) =ᵐ[(μ).restrict Ω]
        (fun x => Wkp.iteratedGradient 1 w x (WeakTest.e j) i) := by
  let u := Wkp.lowerOrder 1 w
  let G := (W1p.gradient u : E → E)
  let D := (Wkp.iteratedGradient 1 w : E → E →L[ℝ] E)
  have hG : HasWeakFDerivOn μ Ω G D := by
    simpa only [G,D,u,Wkp.iteratedGradient_zero] using Wkp.hasWeakFDerivOn_iteratedGradient 0 w
  exact (WeakTest.vecDeriv hG j i).ae_eq
    (WeakTest.symmDeriv (W1p.hasWeakFDerivOn u) hG j i)

end CalderonPatch
