module

public import Proof.CalderonN.InteriorFluxEnergy
public import Proof.CalderonN.DifferentiatedFlux

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace CalderonN.Elliptic

variable {d : ℕ} [NeZero d]


private def wordsThrough : ℕ → Finset (List (I d))
  | 0 => {[]}
  | n+1 => insert [] (Finset.univ.biUnion fun i : (I d) => (wordsThrough n).image (List.cons i))

private theorem mem_wordsThrough (n : ℕ) (w : List (I d)) :
    w ∈ wordsThrough n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => cases w <;> simp [wordsThrough]
  | succ n ih =>
    cases w with
    | nil => simp [wordsThrough]
    | cons i w =>
      simp only [wordsThrough,Finset.mem_insert,List.cons_ne_nil,false_or,Finset.mem_biUnion,
        Finset.mem_univ,true_and,Finset.mem_image,List.cons.injEq,List.length_cons,
        Nat.succ_le_succ_iff,ih]
      constructor
      · rintro ⟨_,_,hv,rfl,rfl⟩
        exact hv
      · intro hw
        exact ⟨i,w,hw,rfl,rfl⟩

/-- A common squared (L²) interior estimate for all coefficients in the
compact family and all coordinate words through a specified order. -/
theorem exists_interior_word_energy_bound_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J) {U : Set (X d)} (hU : IsOpen U)
    (a : P → (I d) → (I d) → (X d) → ℝ) (ha : ∀ i j, Strict.JointSmooth (fun p => a p i j))
    (hpos : ∀ p ∈ J, ∀ x ∈ U, Matrix.PosDef (fun i j => a p i j x : (Mat d)))
    (n : ℕ) {K : Set (X d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ (u : (X d) → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ U, Lop (a p) u x = 0) → IntegrableOn (fun x => u x ^ 2) U →
      ∀ w : List (I d), w.length ≤ n →
        (∫ x in K, wordDeriv w u x ^ 2) ≤ C*(∫ x in U, u x^2) := by
  induction n generalizing K with
  | zero =>
    refine ⟨1,zero_le_one,fun _ _ u _ _ hInt w hw => ?_⟩
    have hz : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    rw [hz,wordDeriv,one_mul]
    exact setIntegral_mono_set hInt (ae_of_all _ fun x => sq_nonneg (u x)) hKU.eventuallyLE
  | succ n ih =>
    obtain ⟨L,hL,hLU,C₀,hC₀,hstep⟩ := exists_interior_flux_energy_bound_family hJ hU hK hKU a ha hpos
    obtain ⟨A,hA,hprev⟩ := ih hL hLU
    choose B hB hF using (fun (w : List (I d)) (j : (I d)) => exists_wordFlux_energy_constant_family hJ hL ha w j)
    let S := ∑ w ∈ wordsThrough n, ∑ j : (I d), B w j
    have hS : 0 ≤ S := Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun j _ => hB w j
    refine ⟨max 1 (C₀*((1+S)*A)),zero_le_one.trans (le_max_left _ _),fun p hp u hu hPDE hInt w hw => ?_⟩
    have hap (i j : (I d)) := Strict.jointSmooth_slice (ha i j) p
    let E := ∫ x in U, u x^2
    have hE : 0 ≤ E := integral_nonneg fun x => sq_nonneg (u x)
    cases w with
    | nil =>
      rw [wordDeriv]
      exact (setIntegral_mono_set hInt (ae_of_all _ fun x => sq_nonneg (u x)) hKU.eventuallyLE).trans
        (le_mul_of_one_le_left hE (le_max_left _ _))
    | cons i w =>
      have hw' : w.length ≤ n := Nat.le_of_succ_le_succ hw
      have hUword := contDiff_wordDeriv w hu
      have hFw (j : (I d)) := contDiff_wordFlux hap w hu j
      have hEq := lop_wordDeriv_eq_div_wordFlux hU hap hu hPDE w
      have hbound (v : List (I d)) (hv : v.length ≤ w.length) :
          (∫ x in L, wordDeriv v u x^2) ≤ A*E :=
        hprev p hp u hu hPDE hInt v (hv.trans hw')
      have hS₁ : ∑ j : (I d), B w j ≤ S :=
        Finset.single_le_sum (f := fun v => ∑ j : (I d), B v j)
          (fun v _ => Finset.sum_nonneg fun j _ => hB v j) ((mem_wordsThrough n w).mpr hw')
      have hIntU (j : (I d)) : IntegrableOn (fun x => pd j (wordDeriv w u) x ^ 2) K :=
        ((contDiff_pd hUword).continuous.pow 2).continuousOn.integrableOn_compact hK
      have hIntF (j : (I d)) : IntegrableOn (fun x => wordFlux (a p) w u j x ^ 2) L :=
        ((hFw j).continuous.pow 2).continuousOn.integrableOn_compact hL
      have hIntW : IntegrableOn (fun x => wordDeriv w u x^2) L :=
        (hUword.continuous.pow 2).continuousOn.integrableOn_compact hL
      have hSumF : (∫ x in L, ∑ j, wordFlux (a p) w u j x ^ 2) ≤ S*(A*E) := by
        rw [integral_finsetSum _ (fun j _ => hIntF j)]
        calc
          _ ≤ ∑ j : (I d), B w j*(A*E) :=
            Finset.sum_le_sum (fun j _ => hF w j p hp u (A*E) hu hbound)
          _ = (∑ j : (I d), B w j)*(A*E) := (Finset.sum_mul ..).symm
          _ ≤ S*(A*E) := mul_le_mul_of_nonneg_right hS₁ (mul_nonneg hA hE)
      have hLbound : (∫ x in L, (wordDeriv w u x ^ 2 + ∑ j, wordFlux (a p) w u j x ^ 2)) ≤ (1+S)*A*E := by
        rw [integral_add hIntW (integrable_finsetSum _ (fun j _ => hIntF j))]
        exact (add_le_add (hbound w le_rfl) hSumF).trans_eq (by ring)
      have hI : (∫ x in K, pd i (wordDeriv w u) x^2) ≤ ∫ x in K, ∑ j, pd j (wordDeriv w u) x^2 := by
        apply integral_mono (hIntU i) (integrable_finsetSum _ (fun j _ => hIntU j))
        exact fun x => Finset.single_le_sum (f := fun j => pd j (wordDeriv w u) x^2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [wordDeriv]
      exact hI.trans ((hstep p hp _ _ hUword hFw hEq).trans
        ((mul_le_mul_of_nonneg_left hLbound hC₀).trans
          (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE)))

/-- The same estimate for a single fixed metric. -/
theorem exists_interior_word_energy_bound {U : Set (X d)} (hU : IsOpen U)
    (a : (I d) → (I d) → (X d) → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hpos : ∀ x ∈ U, Matrix.PosDef (fun i j => a i j x : (Mat d)))
    (n : ℕ) {K : Set (X d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (X d) → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ U, Lop a u x = 0) → IntegrableOn (fun x => u x ^ 2) U →
      ∀ w : List (I d), w.length ≤ n →
        (∫ x in K, wordDeriv w u x ^ 2) ≤ C*(∫ x in U, u x^2) := by
  obtain ⟨C,hC,h⟩ := exists_interior_word_energy_bound_family (isCompact_singleton (x := (0:ℝ))) hU
    (fun _ => a) (fun i j => (ha i j).comp contDiff_snd) (fun _ _ x hx => hpos x hx) n hK hKU
  exact ⟨C,hC,h 0 (mem_singleton _)⟩

end CalderonN.Elliptic
