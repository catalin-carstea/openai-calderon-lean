module

public import Proof.CalderonN.SphereHarmonicBridge

import Mathlib.Tactic

@[expose] public section

/- Fischer decomposition ported from LiteratureHarmonicDecomposition in the
   released Proposition 5.3 proof (f308cb9d). -/
noncomputable section
open MvPolynomial

namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

variable {n : ℕ}

private theorem laplacian_radiusSq_mul_gen {f : MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    laplacian (radiusSq * f) = radiusSq * laplacian f + C (2*(n : ℝ) + 4*(d : ℝ)) * f := by
  rw [laplacian_radiusSq_mul_of_isHomogeneous hf, Fintype.card_fin]
  congr 3
  ring

lemma laplacian_radiusSq_pow_mul {h : MvPolynomial (Fin n) ℝ} {m : ℕ}
    (hh : h ∈ harmonicHomogeneous n m) (s : ℕ) :
    laplacian (radiusSq ^ (s + 1) * h) =
      C (2 * ((s : ℝ) + 1) * (2 * s + 2 * m + (n : ℝ))) * (radiusSq ^ s * h) := by
  induction s with
  | zero =>
    rw [pow_one, laplacian_radiusSq_mul_gen hh.1, hh.2]
    have : (C (2 * ((0 : ℕ) + 1) * (2 * (0 : ℕ) + 2 * m + (n : ℝ)) : ℝ) : MvPolynomial (Fin n) ℝ) =
        C (2 * (n : ℝ) + 4 * (m : ℝ)) := by
      congr 1; push_cast; ring
    rw [this]; ring
  | succ s ih =>
    have hd : (radiusSq ^ (s + 1) * h).IsHomogeneous (2 * (s + 1) + m) :=
      (radiusSq_isHomogeneous.pow _).mul hh.1
    rw [pow_succ', mul_assoc, laplacian_radiusSq_mul_gen hd, ih]
    have : (C (2 * (((s + 1 : ℕ) : ℝ) + 1) * (2 * ((s + 1 : ℕ) : ℝ) + 2 * m + (n : ℝ))) :
        MvPolynomial (Fin n) ℝ) =
        C (2 * ((s : ℝ) + 1) * (2 * s + 2 * m + (n : ℝ))) +
          C (2 * (n : ℝ) + 4 * (((2 * (s + 1) + m : ℕ)) : ℝ)) := by
      rw [← C_add]; congr 1; push_cast; ring
    rw [this, pow_succ']; ring

 
def laplacianLinear : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := laplacian
  map_add' p q := by simp [laplacian, Finset.sum_add_distrib]
  map_smul' c p := by simp [laplacian, Finset.smul_sum]

 
def harmonicDecompSpan n (k : ℕ) : Submodule ℝ (MvPolynomial (Fin n) ℝ) :=
  Submodule.span ℝ {p | ∃ j m : ℕ, 2 * j + m = k ∧ ∃ h ∈ harmonicHomogeneous n m,
    p = radiusSq ^ j * h}

lemma harmonicDecompSpan_le (k : ℕ) :
    harmonicDecompSpan n k ≤ homogeneousSubmodule (Fin n) ℝ k := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, m, rfl, h, hh, rfl⟩
  exact (radiusSq_isHomogeneous.pow j).mul hh.1

lemma harmonicHomogeneous_le_decompSpan (k : ℕ) :
    harmonicHomogeneous n k ≤ harmonicDecompSpan n k := fun h hh =>
  Submodule.subset_span ⟨0, k, by ring, h, hh, by simp⟩

lemma harmonicDecompSpan_le_map (hn : 0 < n) (k : ℕ) :
    harmonicDecompSpan n k ≤ (harmonicDecompSpan n (k + 2)).map laplacianLinear := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, m, rfl, h, hh, rfl⟩
  set c : ℝ := 2 * ((j : ℝ) + 1) * (2 * j + 2 * m + (n : ℝ))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : c ≠ 0 := by positivity
  refine ⟨c⁻¹ • (radiusSq ^ (j + 1) * h), Submodule.smul_mem _ _
    (Submodule.subset_span ⟨j + 1, m, by ring, h, hh, rfl⟩), ?_⟩
  rw [map_smul]
  change c⁻¹ • laplacian _ = _
  rw [laplacian_radiusSq_pow_mul hh, smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc,
    C_1, one_mul]

lemma pderiv_eq_zero_of_isHomogeneous_zero {q : MvPolynomial (Fin n) ℝ} (hq : q.IsHomogeneous 0)
    (i : Fin n) : pderiv i q = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hq
  rw [hq, pderiv_C]

lemma laplacian_isHomogeneous {p : MvPolynomial (Fin n) ℝ} {k : ℕ} (hp : p.IsHomogeneous (k + 2)) :
    (laplacian p).IsHomogeneous k :=
  IsHomogeneous.sum _ _ _ fun _ _ => (hp.pderiv.pderiv : IsHomogeneous _ (k + 2 - 1 - 1))

 

theorem homogeneous_mem_harmonicDecompSpan (hn : 0 < n) {p : MvPolynomial (Fin n) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) : p ∈ harmonicDecompSpan n k := by
  induction k using Nat.strong_induction_on generalizing p with
  | _ k ih =>
  match k, ih, hp with
  | 0, _, hp =>
    refine harmonicHomogeneous_le_decompSpan 0 ⟨hp, ?_⟩
    simp [laplacian, pderiv_eq_zero_of_isHomogeneous_zero hp]
  | 1, _, hp =>
    refine harmonicHomogeneous_le_decompSpan 1 ⟨hp, ?_⟩
    simp [laplacian, pderiv_eq_zero_of_isHomogeneous_zero (hp.pderiv : IsHomogeneous _ (1 - 1))]
  | k + 2, ih, hp =>
    obtain ⟨q, hq, hΔ⟩ := harmonicDecompSpan_le_map hn k (ih k (by omega) (laplacian_isHomogeneous hp))
    have hpq : p - q ∈ harmonicHomogeneous n (k + 2) := by
      refine ⟨hp.sub (harmonicDecompSpan_le _ hq), ?_⟩
      change laplacianLinear (p - q) = 0
      rw [map_sub, hΔ]; exact sub_self _
    simpa using Submodule.add_mem _ (harmonicHomogeneous_le_decompSpan _ hpq) hq

end OAI.AnisotropicCalderon.SphereHarmonic
