module

public import Proof.CalderonN.EllipticCalculus
import Mathlib.Tactic

@[expose] public section

/- Joint coefficient derivatives from the 3D Theorem 3.1 release. -/
noncomputable section
open scoped ContDiff

namespace CalderonN.Elliptic.Strict
variable {d : ℕ}

abbrev JointSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → (X d) → ℝ) :
    Prop :=
  ContDiff ℝ ∞ (fun q : E × (X d) => F q.1 q.2)

section JointSmoothClosure
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- U2a: the coordinate derivative of a jointly smooth family is jointly smooth. -/
theorem jointSmooth_pd {F : E → (X d) → ℝ} (hF : JointSmooth F) (k : Fin d) :
    JointSmooth (fun q => pd k (F q)) := by
  have hu : ContDiff ℝ ∞ (Function.uncurry fun (q : E × (X d)) (y : (X d)) => F q.1 y) :=
    hF.comp (by fun_prop : ContDiff ℝ ∞ (fun p : (E × (X d)) × (X d) => (p.1.1, p.2)))
  show ContDiff ℝ ∞ (fun q : E × (X d) => fderiv ℝ (F q.1) q.2 (EuclideanSpace.single k 1))
  exact hu.fderiv_apply contDiff_snd contDiff_const (by simp)

theorem jointSmooth_add {F G : E → (X d) → ℝ} (hF : JointSmooth F) (hG : JointSmooth G) :
    JointSmooth (fun q y => F q y + G q y) := ContDiff.add hF hG

theorem jointSmooth_mul {F G : E → (X d) → ℝ} (hF : JointSmooth F) (hG : JointSmooth G) :
    JointSmooth (fun q y => F q y * G q y) := ContDiff.mul hF hG

theorem jointSmooth_const_mul (c : ℝ) {F : E → (X d) → ℝ} (hF : JointSmooth F) :
    JointSmooth (fun q y => c * F q y) := ContDiff.mul contDiff_const hF

theorem jointSmooth_sum {F : Fin d → E → (X d) → ℝ} (hF : ∀ k, JointSmooth (F k)) :
    JointSmooth (fun q y => ∑ k, F k q y) := ContDiff.sum fun k _ => hF k

theorem jointSmooth_divV {F : E → Fin d → (X d) → ℝ} (hX : ∀ j, JointSmooth fun q => F q j) :
    JointSmooth fun q => divV (F q) :=
  jointSmooth_sum (F := fun j q y => pd j (F q j) y)
    (fun j => jointSmooth_pd (F := fun q => F q j) (hX j) j)

theorem jointSmooth_Lop {a : E → Fin d → Fin d → (X d) → ℝ}
    (ha : ∀ i k, JointSmooth fun q => a q i k) {f : E → (X d) → ℝ}
    (hf : JointSmooth f) : JointSmooth fun q => Lop (a q) (f q) :=
  jointSmooth_sum (F := fun i q y => pd i (fun z => ∑ k, a q i k z * pd k (f q) z) y)
    (fun i => jointSmooth_pd (F := fun q z => ∑ k, a q i k z * pd k (f q) z)
      (jointSmooth_sum (F := fun k q z => a q i k z * pd k (f q) z)
        (fun k => jointSmooth_mul (ha i k) (jointSmooth_pd hf k))) i)

end JointSmoothClosure

theorem jointSmooth_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → (X d) → ℝ} (hF : JointSmooth F) (P : E) : ContDiff ℝ ∞ (F P) := by
  have hJ : ContDiff ℝ ∞ (fun q : E × (X d) => F q.1 q.2) := hF
  have h := hJ.comp (by fun_prop : ContDiff ℝ ∞ fun y : (X d) => (P, y))
  exact h

end CalderonN.Elliptic.Strict
