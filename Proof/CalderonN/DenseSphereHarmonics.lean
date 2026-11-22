module

public import Proof.CalderonN.HarmonicDecomposition
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

import Mathlib.Tactic

@[expose] public section

/- Degree density ported from LiteratureDenseSphereHarmonics, Proposition
   5.3 check f308cb9d. -/
noncomputable section
open MeasureTheory MvPolynomial
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularPolynomial

variable {n : ℕ}

 
def coordSphere (i : Fin n) : C(UnitSphere n, ℝ) := ⟨fun x => (x.val : Fin n → ℝ) i, by fun_prop⟩

lemma polynomialSphere_eq_aeval (p : MvPolynomial (Fin n) ℝ) :
    polynomialSphere p = aeval coordSphere p := by
  ext x
  induction p using MvPolynomial.induction_on with
  | C a => simp [polynomialSphere]
  | add p q hp hq => simp_all [polynomialSphere]
  | mul_X p i hp => simp_all [polynomialSphere, coordSphere]

lemma polynomialSphere_denseRange : DenseRange (polynomialSphere (n := n)) := by
  let A : Subalgebra ℝ C(UnitSphere n, ℝ) := (aeval coordSphere).range
  have hA : A.topologicalClosure = ⊤ := by
    apply ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    intro x y hxy
    have : (x.val : Fin n → ℝ) ≠ (y.val : Fin n → ℝ) := by
      intro h; apply hxy; ext1; exact WithLp.ofLp_injective _ h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp this
    exact ⟨_, ⟨coordSphere i, ⟨X i, by simp⟩, rfl⟩, by simpa [coordSphere] using hi⟩
  have hr : Set.range polynomialSphere = (A : Set C(UnitSphere n, ℝ)) := by
    ext f; simp [A, polynomialSphere_eq_aeval]
  rw [DenseRange, hr, dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, hA]
  rfl

variable [NeZero n]

lemma polynomialSphereL2_denseRange : DenseRange (polynomialSphereL2 (n := n)) := by
  have h := ContinuousMap.toLp_denseRange ℝ (unitSphereProbability n) ℝ (p := 2) (by simp)
  exact h.comp polynomialSphere_denseRange (ContinuousMap.toLp 2 (unitSphereProbability n) ℝ).continuous

omit [NeZero n] in
lemma eval_radiusSq_sphere (x : UnitSphere n) :
    radiusSq.eval (x.val : Fin n → ℝ) = 1 := by
  have h1 : ‖x.val‖ = 1 := by simp
  have h2 := EuclideanSpace.norm_sq_eq x.val
  simp only [h1, one_pow, Real.norm_eq_abs, sq_abs] at h2
  simp [radiusSq, h2]

lemma polynomialSphereL2_radiusSq_pow_mul (j : ℕ) (h : MvPolynomial (Fin n) ℝ) :
    polynomialSphereL2 (radiusSq ^ j * h) = polynomialSphereL2 h := by
  have : polynomialSphere (radiusSq ^ j * h) = polynomialSphere h := by
    ext x; simp [polynomialSphere, eval_radiusSq_sphere x]
  change ContinuousMap.toLp 2 (unitSphereProbability n) ℝ (polynomialSphere _) =
    ContinuousMap.toLp 2 (unitSphereProbability n) ℝ (polynomialSphere _)
  rw [this]

lemma polynomialSphereL2_mem_iSup (p : MvPolynomial (Fin n) ℝ) :
    polynomialSphereL2 p ∈ ⨆ k : ℕ, harmonicSphereSubspace n k := by
  have hdec : ∀ k, harmonicDecompSpan n k ≤
      (⨆ k : ℕ, harmonicSphereSubspace n k).comap polynomialSphereL2 := by
    intro k
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, m, -, h, hh, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, polynomialSphereL2_radiusSq_pow_mul]
    exact Submodule.mem_iSup_of_mem m ⟨h, hh, rfl⟩
  rw [← sum_homogeneousComponent p, map_sum]
  exact Submodule.sum_mem _ fun d _ =>
    hdec d (homogeneous_mem_harmonicDecompSpan (Nat.pos_of_ne_zero (NeZero.ne n)) (homogeneousComponent_isHomogeneous d p))

 
theorem denseSphereHarmonics (n : ℕ) [NeZero n] : DenseSphereHarmonics n := by
  rw [DenseSphereHarmonics, ← Submodule.dense_iff_topologicalClosure_eq_top]
  refine polynomialSphereL2_denseRange.mono ?_
  rintro _ ⟨p, rfl⟩
  exact polynomialSphereL2_mem_iSup p

end OAI.AnisotropicCalderon.SphereHarmonic
