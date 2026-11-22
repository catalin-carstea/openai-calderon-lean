module

public import Proof.CalderonN.WkpCalculus
public import Mathlib.Analysis.Matrix.Normed
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Leibniz
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic

/-! Test function calculus and weak mixed-partial symmetry from the checked
3D release's `CollaboratorRegularityDiffEquationOct17`, over an arbitrary open set. -/
@[expose] public section

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonN.WeakTest
open TauCeti TauCeti.PDE
variable {n : ℕ} {Ω : Opens (X n)}

def e (i : Fin n) : (X n) := EuclideanSpace.single i (1 : ℝ)

lemma coord_eq_inner (y : (X n)) (i : Fin n) : y i = ⟪y, e i⟫_ℝ := by
  simp [e, EuclideanSpace.inner_single_right]

def pd (g : (X n) → ℝ) (i : Fin n) : (X n) → ℝ := fun x => fderiv ℝ g x (e i)

def TF (Ω : Opens (X n)) (g : (X n) → ℝ) : Prop := ∃ ψ : 𝓓(Ω, ℝ), (ψ : (X n) → ℝ) = g

end CalderonN.WeakTest

namespace CalderonN.WeakTest.TF
open TauCeti TauCeti.PDE
variable {n : ℕ} {Ω : Opens (X n)}

lemma of (ψ : 𝓓(Ω, ℝ)) : TF Ω ψ := ⟨ψ, rfl⟩

lemma contDiff {g : (X n) → ℝ} (h : TF Ω g) : ContDiff ℝ ∞ g := by
  obtain ⟨ψ, rfl⟩ := h; exact ψ.contDiff

lemma differentiableAt {g : (X n) → ℝ} (h : TF Ω g) (x : (X n)) : DifferentiableAt ℝ g x :=
  (h.contDiff.differentiable (by simp)) x

lemma zero_of_notMem {g : (X n) → ℝ} (h : TF Ω g) {x : (X n)} (hx : x ∉ (Ω : Set (X n))) :
    g x = 0 := by
  obtain ⟨ψ, rfl⟩ := h
  exact image_eq_zero_of_notMem_tsupport (fun hmem => hx (ψ.tsupport_subset hmem))

lemma mul {g : (X n) → ℝ} (h : TF Ω g) {f : (X n) → ℝ} (hf : ContDiff ℝ ∞ f) :
    TF Ω (fun x => g x * f x) := by
  obtain ⟨ψ, rfl⟩ := h
  exact ⟨⟨(ψ : (X n) → ℝ) * f, ψ.contDiff.mul hf, ψ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans ψ.tsupport_subset⟩, rfl⟩

lemma deriv {g : (X n) → ℝ} (h : TF Ω g) (i : Fin n) : TF Ω (pd g i) := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨TestFunction.lineDerivCLM ℝ (e i) ψ, ?_⟩
  funext x
  rw [TestFunction.lineDerivCLM_apply_of_le le_top]
  exact ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv

lemma integrable {g : (X n) → ℝ} (h : TF Ω g) {w : (X n) → ℝ}
    (hw : LocallyIntegrableOn w (Ω : Set (X n)) volume) :
    Integrable (fun x => g x * w x) volume := by
  obtain ⟨ψ, rfl⟩ := h
  simpa [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hw ψ

lemma null {g : (X n) → ℝ} (h : TF Ω g) {u u' : (X n) → ℝ} {i : Fin n}
    (hu : HasWeakLineDerivOn volume Ω u u' (e i)) :
    Integrable (fun x => pd g i x * u x + g x * u' x) volume ∧
      ∫ x, (pd g i x * u x + g x * u' x) = 0 := by
  have h1 := (h.deriv i).integrable hu.locallyIntegrableOn
  have h2 := h.integrable hu.locallyIntegrableOn_deriv
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2]
  obtain ⟨ψ, rfl⟩ := h
  have := hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  simp only [smul_eq_mul] at this
  have e1 : (fun x => lineDeriv ℝ (ψ : (X n) → ℝ) x (e i) * u x) = fun x => pd ψ i x * u x := by
    funext x
    rw [((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv]; rfl
  rw [e1] at this
  rw [this]; ring

end CalderonN.WeakTest.TF

namespace CalderonN.WeakTest
open TauCeti TauCeti.PDE
variable {n : ℕ} {Ω : Opens (X n)}

lemma pd_pd_comm {g : (X n) → ℝ} (hg : ContDiff ℝ ∞ g) (i l : Fin n) (x : (X n)) :
    pd (pd g i) l x = pd (pd g l) i x := by
  have hdf : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have key : ∀ u u' : (X n), fderiv ℝ (fun y => fderiv ℝ g y u) x u' =
      fderiv ℝ (fderiv ℝ g) x u' u := by
    intro u u'
    rw [fderiv_clm_apply (hdf x) (differentiableAt_const u)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ g y (e i)) x (e l) = fderiv ℝ (fun y => fderiv ℝ g y (e l)) x (e i)
  rw [key, key]
  exact ((hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)) (e l) (e i)

end CalderonN.WeakTest

namespace CalderonN.WeakTest
open TauCeti TauCeti.PDE
variable {n : ℕ} {Ω : Opens (X n)}

lemma contDiff_entry {a : (X n) → Matrix (Fin n) (Fin n) ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin n) :
    ContDiff ℝ ∞ (fun x => a x i k) :=
  contDiff_pi.1 (contDiff_pi.1 ha i) k

lemma matrixBilinearForm_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (η ξ : (X n)) :
    matrixBilinearForm A η ξ = ∑ i, ∑ k, η i * (A i k * ξ k) := by
  rw [matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma gradient_coord (g : (X n) → ℝ) (x : (X n)) (i : Fin n) :
    gradient g x i = pd g i x := by
  rw [coord_eq_inner, inner_gradient_left]; rfl

lemma integral_eq_setIntegral {Z : (X n) → ℝ} (hZ : ∀ x ∉ (Ω : Set (X n)), Z x = 0) :
    ∫ x, Z x = ∫ x in (Ω : Set (X n)), Z x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hZ).symm

lemma coordDeriv {u : (X n) → ℝ} {G : (X n) → (X n)}
    (hu : HasWeakFDerivOn volume Ω u (fun x => innerSL ℝ (G x))) (k : Fin n) :
    HasWeakLineDerivOn volume Ω u (fun x => G x k) (e k) :=
  (hu.hasWeakLineDerivOn (e k)).congr_ae_deriv
    (Filter.Eventually.of_forall fun x => by simp [coord_eq_inner])

lemma vecDeriv {G : (X n) → (X n)} {D : (X n) → (X n) →L[ℝ] (X n)}
    (hG : HasWeakFDerivOn volume Ω G D) (k l : Fin n) :
    HasWeakLineDerivOn volume Ω (fun x => G x k) (fun x => D x (e l) k) (e l) :=
  (hG.hasWeakLineDerivOn (e l)).clm_comp (EuclideanSpace.proj k : (X n) →L[ℝ] ℝ)

end CalderonN.WeakTest

namespace CalderonN.WeakTest.TF
open TauCeti TauCeti.PDE
variable {n : ℕ} {Ω : Opens (X n)}

lemma ibp {g : (X n) → ℝ} (h : TF Ω g) {u u' : (X n) → ℝ} {i : Fin n}
    (hu : HasWeakLineDerivOn volume Ω u u' (e i)) :
    ∫ x, g x * u' x = -∫ x, pd g i x * u x := by
  have h1 := (h.deriv i).integrable hu.locallyIntegrableOn
  have h2 := h.integrable hu.locallyIntegrableOn_deriv
  have := (h.null hu).2
  rw [integral_add h1 h2] at this
  linarith

end CalderonN.WeakTest.TF

namespace CalderonN.WeakTest
open TauCeti TauCeti.PDE
variable {n : ℕ} {Ω : Opens (X n)}

lemma lineDeriv_eq_pd (ψ : 𝓓(Ω, ℝ)) (x : (X n)) (i : Fin n) :
    lineDeriv ℝ (ψ : (X n) → ℝ) x (e i) = pd ψ i x :=
  ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv

lemma symmDeriv {u : (X n) → ℝ} {G : (X n) → (X n)} {D : (X n) → (X n) →L[ℝ] (X n)}
    (hu : HasWeakFDerivOn volume Ω u (fun x => innerSL ℝ (G x)))
    (hG : HasWeakFDerivOn volume Ω G D) (k l : Fin n) :
    HasWeakLineDerivOn volume Ω (fun x => G x k) (fun x => D x (e k) l) (e l) := by
  have h1 := vecDeriv hG l k
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, (coordDeriv hu k).locallyIntegrableOn_deriv,
    h1.locallyIntegrableOn_deriv, fun ψ => ?_⟩
  rw [← h1.integral_lineDeriv_smul_eq_neg_integral_smul ψ]
  simp only [smul_eq_mul, lineDeriv_eq_pd]
  rw [((TF.of ψ).deriv l).ibp (coordDeriv hu k), ((TF.of ψ).deriv k).ibp (coordDeriv hu l)]
  simp only [pd_pd_comm ψ.contDiff l k]

end CalderonN.WeakTest
