module

public import Proof.CalderonPatch.CompactSecondJet
public import Proof.CalderonN.FixedKernelIntegral

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.Ring

public section

noncomputable section
open Matrix MeasureTheory Set
open scoped ContDiff

namespace CalderonPatch

open CalderonN (I X Mat axis coordDeriv hessian parameterSecondOrder)

variable {n : ℕ} [NeZero n]

/-- Any functional on scalar second jets is a constant-coefficient
differential evaluation of order at most two. The matrix coefficients
may be obtained from a linear extension of the symmetric Hessian slot. -/
theorem exists_parameterSecondOrder_for_jetFunctional (D : ScalarSecondJet n →ₗ[ℝ] ℝ) :
    ∃ (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ),
      ∀ {U : Set (X n)} (hU : IsOpen U) {x : X n} (hx : x ∈ U)
        (u : X n → ℝ) (hu : ContDiffOn ℝ ∞ u U),
        D (smoothSecondJet hU hx u hu) = parameterSecondOrder a b c u x := by
  classical
  let g : (I n → ℝ) →ₗ[ℝ] ℝ :=
    D.comp (LinearMap.inr ℝ ℝ ((I n → ℝ) × symmetricHessians n)) |>.comp
      (LinearMap.inl ℝ (I n → ℝ) (symmetricHessians n))
  let h : symmetricHessians n →ₗ[ℝ] ℝ :=
    D.comp (LinearMap.inr ℝ ℝ ((I n → ℝ) × symmetricHessians n)) |>.comp
      (LinearMap.inr ℝ (I n → ℝ) (symmetricHessians n))
  obtain ⟨L,hL⟩ := LinearMap.exists_extend h
  let a (i j : I n) := L (Matrix.single i j 1)
  let b (i : I n) := g (Pi.single i 1)
  let c := D ((1 : ℝ),0,0)
  refine ⟨a,b,c,?_⟩
  intro U hU x hx u hu
  let J := smoothSecondJet hU hx u hu
  have h₁ : D (J.1,0,0) = c * J.1 := by
    have hh : (J.1,0,0) = J.1 • ((1,0,0) : ScalarSecondJet n) := by
      exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    rw [hh,map_smul,smul_eq_mul,mul_comm]
  have h₂ : D (0,J.2.1,0) = ∑ i, b i * J.2.1 i := by
    change g J.2.1 = _
    have hh : (∑ i : I n, J.2.1 i • Pi.single i (1 : ℝ)) = J.2.1 := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← hh]
    simp only [map_sum, map_smul, smul_eq_mul, b]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have h₃ : D (0,0,J.2.2) = ∑ i, ∑ j, a i j * J.2.2.val i j := by
    have hEq : L J.2.2.val = h J.2.2 := DFunLike.congr_fun hL J.2.2
    change h J.2.2 = _
    rw [← hEq]
    have hh := Matrix.sum_sum_single J.2.2.val
    conv_lhs => rw [← show _ = J.2.2.val from hh]
    simp only [map_sum, a]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← show J.2.2.val i j • Matrix.single i j (1 : ℝ) = Matrix.single i j (J.2.2.val i j) from
      by rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul, mul_comm]
  have hJ : J = (J.1,0,0) + (0,J.2.1,0) + (0,0,J.2.2) := by
    ext <;> simp
  change D J = _
  conv_lhs => rw [hJ, map_add, map_add, h₁, h₂, h₃]
  let C₁ := ∑ i, b i * coordDeriv i u x
  let C₂ := ∑ i, ∑ j, a i j * hessian u x i j
  change c * u x + C₁ + C₂ = C₂ + C₁ + c * u x
  ring

/-- Second-jet evaluation commutes with integration of a jointly
smooth kernel over a fixed compact carrier. -/
theorem jetFunctional_integral_on_compact {μ : Measure (X n)} [IsFiniteMeasure μ]
    {K U V : Set (X n)} [DecidablePred (· ∈ U)] (hK : IsCompact K) (hKU : K ⊆ U)
    (hU : IsOpen U) (hV : IsOpen V) (hμ : μ Kᶜ = 0)
    {G : X n → X n → ℝ} (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V))
    (D : ScalarSecondJet n →ₗ[ℝ] ℝ) {x : X n} (hx : x ∈ V) :
    ∃ (hInt : ContDiffOn ℝ ∞ (fun z => ∫ y, G y z ∂μ) V)
      (hSlice : ∀ y ∈ U, ContDiffOn ℝ ∞ (G y) V),
      D (smoothSecondJet hV hx (fun z => ∫ y, G y z ∂μ) hInt) =
        ∫ y in U, D (if hy : y ∈ U then smoothSecondJet hV hx (G y) (hSlice y hy) else 0) ∂μ := by
  classical
  have hInt : ContDiffOn ℝ ∞ (fun z => ∫ y, G y z ∂μ) V :=
    contDiffOn_infty.mpr (fun k => CalderonN.contDiffOn_integral_on_compact hK hKU hU hV hμ k G
      (hG.of_le (by simp)))
  have hSlice (y : X n) (hy : y ∈ U) : ContDiffOn ℝ ∞ (G y) V :=
    hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hy,hz⟩)
  obtain ⟨a,b,c,hD⟩ := exists_parameterSecondOrder_for_jetFunctional D
  refine ⟨hInt,hSlice,?_⟩
  rw [hD hV hx _ hInt, CalderonN.integral_parameterSecondOrder hK hKU hU hV hμ
    (hG.of_le (by simp)) a b c hx]
  have hAU : ∀ᵐ y ∂μ, y ∈ U := (CalderonN.ae_mem_of_measure_compl hμ).mono hKU
  rw [Measure.restrict_eq_self_of_ae_mem hAU]
  apply integral_congr_ae
  filter_upwards [hAU] with y hy
  rw [dite_eq_left hy,hD hV hx _ (hSlice y hy)]

end CalderonPatch
