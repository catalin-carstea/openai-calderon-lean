module

public import Proof.CalderonN.BallRegularity.FixedRegularity
public import Proof.CalderonN.BallRegularity.FixedCalculus
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.TestFunctionLp
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.SecondOrder
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Leibniz

/-! From Proof/Archive/CollaboratorRegularityDiffEquationOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

noncomputable section
open MeasureTheory TopologicalSpace
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace CalderonN.BallRegularity.DiffEq

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE


def e (i : Fin dim) : (X dim) := EuclideanSpace.single i (1 : ℝ)

lemma coord_eq_inner (y : (X dim)) (i : Fin dim) : y i = ⟪y, e i⟫_ℝ := by
  simp [e, EuclideanSpace.inner_single_right]


def pd (g : (X dim) → ℝ) (i : Fin dim) : (X dim) → ℝ := fun x => fderiv ℝ g x (e i)


def TF (g : (X dim) → ℝ) : Prop := ∃ ψ : 𝓓((fixedBallOpens dim), ℝ), (ψ : (X dim) → ℝ) = g

end CalderonN.BallRegularity.DiffEq

namespace CalderonN.BallRegularity.DiffEq.TF

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

lemma of (ψ : 𝓓((fixedBallOpens dim), ℝ)) : TF ψ := ⟨ψ, rfl⟩

lemma contDiff {g : (X dim) → ℝ} (h : TF g) : ContDiff ℝ ∞ g := by
  obtain ⟨ψ, rfl⟩ := h; exact ψ.contDiff

lemma differentiableAt {g : (X dim) → ℝ} (h : TF g) (x : (X dim)) : DifferentiableAt ℝ g x :=
  (h.contDiff.differentiable (by simp)) x

lemma zero_of_notMem {g : (X dim) → ℝ} (h : TF g) {x : (X dim)} (hx : x ∉ ((fixedBallOpens dim) : Set (X dim))) :
    g x = 0 := by
  obtain ⟨ψ, rfl⟩ := h
  exact image_eq_zero_of_notMem_tsupport (fun hmem => hx (ψ.tsupport_subset hmem))

lemma mul {g : (X dim) → ℝ} (h : TF g) {f : (X dim) → ℝ} (hf : ContDiff ℝ ∞ f) :
    TF (fun x => g x * f x) := by
  obtain ⟨ψ, rfl⟩ := h
  exact ⟨⟨(ψ : (X dim) → ℝ) * f, ψ.contDiff.mul hf, ψ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans ψ.tsupport_subset⟩, rfl⟩

lemma add {g h : (X dim) → ℝ} (hg : TF g) (hh : TF h) : TF (fun x => g x + h x) := by
  obtain ⟨ψ, rfl⟩ := hg; obtain ⟨χ, rfl⟩ := hh
  exact ⟨ψ + χ, rfl⟩

lemma zero : TF (fun _ : X dim => 0) := ⟨0, rfl⟩

lemma sum {ι : Type*} (s : Finset ι) {g : ι → (X dim) → ℝ} (h : ∀ i, TF (g i)) :
    TF (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using TF.zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a).add ih

lemma deriv {g : (X dim) → ℝ} (h : TF g) (i : Fin dim) : TF (pd g i) := by
  obtain ⟨ψ, rfl⟩ := h
  refine ⟨TestFunction.lineDerivCLM ℝ (e i) ψ, ?_⟩
  funext x
  rw [TestFunction.lineDerivCLM_apply_of_le le_top]
  exact ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv

lemma integrable {g : (X dim) → ℝ} (h : TF g) {w : (X dim) → ℝ}
    (hw : LocallyIntegrableOn w ((fixedBallOpens dim) : Set (X dim)) volume) :
    Integrable (fun x => g x * w x) volume := by
  obtain ⟨ψ, rfl⟩ := h
  simpa [smul_eq_mul] using integrable_smul_of_locallyIntegrableOn hw ψ


lemma null {g : (X dim) → ℝ} (h : TF g) {u u' : (X dim) → ℝ} {i : Fin dim}
    (hu : HasWeakLineDerivOn volume (fixedBallOpens dim) u u' (e i)) :
    Integrable (fun x => pd g i x * u x + g x * u' x) volume ∧
      ∫ x, (pd g i x * u x + g x * u' x) = 0 := by
  have h1 := (h.deriv i).integrable hu.locallyIntegrableOn
  have h2 := h.integrable hu.locallyIntegrableOn_deriv
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2]
  obtain ⟨ψ, rfl⟩ := h
  have := hu.integral_lineDeriv_smul_eq_neg_integral_smul ψ
  simp only [smul_eq_mul] at this
  have e1 : (fun x => lineDeriv ℝ (ψ : (X dim) → ℝ) x (e i) * u x) = fun x => pd ψ i x * u x := by
    funext x
    rw [((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv]; rfl
  rw [e1] at this
  rw [this]; ring

end CalderonN.BallRegularity.DiffEq.TF

namespace CalderonN.BallRegularity.DiffEq

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

lemma pd_pd_comm {g : (X dim) → ℝ} (hg : ContDiff ℝ ∞ g) (i l : Fin dim) (x : (X dim)) :
    pd (pd g i) l x = pd (pd g l) i x := by
  have hdf : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have key : ∀ u u' : (X dim), fderiv ℝ (fun y => fderiv ℝ g y u) x u' =
      fderiv ℝ (fderiv ℝ g) x u' u := by
    intro u u'
    rw [fderiv_clm_apply (hdf x) (differentiableAt_const u)]
    simp
  show fderiv ℝ (fun y => fderiv ℝ g y (e i)) x (e l) = fderiv ℝ (fun y => fderiv ℝ g y (e l)) x (e i)
  rw [key, key]
  exact ((hg.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)) (e l) (e i)

lemma pd_mul {x : (X dim)} {f g : (X dim) → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (i : Fin dim) : pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  simp only [pd]
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma pd_sum {x : (X dim)} {ι : Type*} (s : Finset ι) {f : ι → (X dim) → ℝ}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) (i : Fin dim) :
    pd (fun y => ∑ j ∈ s, f j y) i x = ∑ j ∈ s, pd (f j) i x := by
  simp only [pd]
  rw [fderiv_fun_sum fun j _ => hf j]
  simp

lemma pd_coord {x : (X dim)} {c : (X dim) → (X dim)} (hc : DifferentiableAt ℝ c x) (l i : Fin dim) :
    pd (fun y => c y l) i x = fderiv ℝ c x (e i) l := by
  simp only [pd]
  have h := ((EuclideanSpace.proj l : (X dim) →L[ℝ] ℝ).hasFDerivAt.comp x hc.hasFDerivAt).fderiv
  have h2 : (fun y => c y l) = (EuclideanSpace.proj l : (X dim) →L[ℝ] ℝ) ∘ c := rfl
  rw [h2, h]
  rfl

lemma alg (φ0 f0 P0 : ℝ) (p : Fin dim → ℝ) (q : Fin dim → Fin dim → ℝ) (A : Fin dim → Fin dim → ℝ)
    (dA : Fin dim → Fin dim → Fin dim → ℝ) (c : Fin dim → ℝ) (dc : Fin dim → Fin dim → ℝ) (G : Fin dim → ℝ)
    (Dm : Fin dim → Fin dim → ℝ) (gF : Fin dim → ℝ) (dψ : Fin dim → Fin dim → Fin dim → ℝ)
    (dP : Fin dim → ℝ) (dφc : Fin dim → ℝ)
    (hψ : ∀ i k l, dψ i k l = dA i k l * c l + A i k * dc l l)
    (hP : ∀ i, dP i = ∑ l, (q i l * c l + p l * dc l i))
    (hφc : ∀ l, dφc l = p l * c l + φ0 * dc l l)
    (hP0 : P0 = ∑ l, p l * c l)
    (hdiv : ∑ l, dc l l = 0) :
    ∑ i, ∑ k, p i * (A i k * ∑ l, (c l * Dm l k + G l * dc l k)) =
      (∑ l, c l * gF l) * φ0 +
        ∑ i, ∑ k, p i * ((∑ m, A i m * dc k m - ∑ l, c l * dA i k l + ∑ j, A j k * dc i j) * G k) +
        ((∑ i, ∑ k, ∑ l, (q i l * ((A i k * c l) • G k) +
            p i * ((A i k * c l) • Dm l k + dψ i k l • G k))) -
          (∑ i, ∑ k, (dP i * A i k) * G k - P0 * f0) -
          ∑ l, (dφc l * f0 + (φ0 * c l) * gF l)) := by
  simp only [hψ, hP, hφc, hP0, smul_eq_mul]
  have key := congrArg (fun t => (φ0 * f0 - ∑ i, ∑ k, p i * A i k * G k) * t) hdiv
  simp only [mul_add, add_mul, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at key ⊢
  have hMoveGradient :
      (∑ i, ∑ k, ∑ l, p i * A i k * G l * dc l k) =
        ∑ i, ∑ k, ∑ l, p i * A i l * dc k l * G k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hCoeffDeriv :
      (∑ i, ∑ k, ∑ l, p i * c l * dA i k l * G k) =
        ∑ i, ∑ k, ∑ l, p i * dA i k l * c l * G k := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  have hMoveTest :
      (∑ i, ∑ k, ∑ l, p i * A l k * dc i l * G k) =
        ∑ i, ∑ k, ∑ l, p l * dc l i * A i k * G k := by
    calc
      _ = ∑ i, ∑ l, ∑ k, p i * A l k * dc i l * G k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ l, ∑ k, p l * A i k * dc l i * G k := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        ring
  have hTestHessian :
      (∑ i, ∑ k, ∑ l, q i l * A i k * c l * G k) =
        ∑ i, ∑ k, ∑ l, q i l * c l * A i k * G k := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    ring
  have hForceDeriv : (∑ l, c l * gF l * φ0) = ∑ l, φ0 * c l * gF l := by
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hForceTrace : (∑ l : Fin dim, φ0 * dc l l * f0) = ∑ l : Fin dim, φ0 * f0 * dc l l := by
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hCoeffTrace :
      (∑ i, ∑ k, ∑ l, p i * A i k * dc l l * G k) =
        ∑ l, ∑ i, ∑ k, p i * A i k * G k * dc l l := by
    calc
      _ = ∑ i, ∑ l, ∑ k, p i * A i k * dc l l * G k :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, p i * A i k * dc l l * G k := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun k _ => ?_
        ring
  linear_combination (norm := ring_nf) key + hMoveGradient + hCoeffDeriv - hMoveTest - hTestHessian -
    hForceDeriv + hForceTrace - hCoeffTrace
  simp


def Null (Z : (X dim) → ℝ) : Prop := Integrable Z volume ∧ ∫ x, Z x = 0

end CalderonN.BallRegularity.DiffEq

namespace CalderonN.BallRegularity.DiffEq.Null

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

lemma sub {Z₁ Z₂ : (X dim) → ℝ} (h₁ : Null Z₁) (h₂ : Null Z₂) : Null (fun x => Z₁ x - Z₂ x) :=
  ⟨h₁.1.sub h₂.1, by rw [integral_sub h₁.1 h₂.1, h₁.2, h₂.2, sub_zero]⟩

lemma sum {ι : Type*} (s : Finset ι) {Z : ι → (X dim) → ℝ} (h : ∀ i, Null (Z i)) :
    Null (fun x => ∑ i ∈ s, Z i x) :=
  ⟨integrable_finsetSum s fun i _ => (h i).1, by
    rw [integral_finsetSum s fun i _ => (h i).1]
    exact Finset.sum_eq_zero fun i _ => (h i).2⟩

end CalderonN.BallRegularity.DiffEq.Null

namespace CalderonN.BallRegularity.DiffEq

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

lemma contDiff_entry {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin dim) :
    ContDiff ℝ ∞ (fun x => a x i k) :=
  contDiff_pi.1 (contDiff_pi.1 ha i) k

lemma contDiff_coord {c : (X dim) → (X dim)} (hc : ContDiff ℝ ∞ c) (l : Fin dim) :
    ContDiff ℝ ∞ (fun x => c x l) :=
  (EuclideanSpace.proj l : (X dim) →L[ℝ] ℝ).contDiff.comp hc

lemma matrixBilinearForm_eq_sum (A : Matrix (Fin dim) (Fin dim) ℝ) (η ξ : (X dim)) :
    matrixBilinearForm A η ξ = ∑ i, ∑ k, η i * (A i k * ξ k) := by
  rw [matrixBilinearForm_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]

lemma gradient_coord (g : (X dim) → ℝ) (x : (X dim)) (i : Fin dim) :
    gradient g x i = pd g i x := by
  rw [coord_eq_inner, inner_gradient_left]; rfl


lemma integral_eq_setIntegral {Z : (X dim) → ℝ} (hZ : ∀ x ∉ ((fixedBallOpens dim) : Set (X dim)), Z x = 0) :
    ∫ x, Z x = ∫ x in ((fixedBallOpens dim) : Set (X dim)), Z x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hZ).symm

lemma coordDeriv {u : (X dim) → ℝ} {G : (X dim) → (X dim)}
    (hu : HasWeakFDerivOn volume (fixedBallOpens dim) u (fun x => innerSL ℝ (G x))) (k : Fin dim) :
    HasWeakLineDerivOn volume (fixedBallOpens dim) u (fun x => G x k) (e k) :=
  (hu.hasWeakLineDerivOn (e k)).congr_ae_deriv
    (Filter.Eventually.of_forall fun x => by simp [coord_eq_inner])

lemma vecDeriv {G : (X dim) → (X dim)} {D : (X dim) → (X dim) →L[ℝ] (X dim)}
    (hG : HasWeakFDerivOn volume (fixedBallOpens dim) G D) (k l : Fin dim) :
    HasWeakLineDerivOn volume (fixedBallOpens dim) (fun x => G x k) (fun x => D x (e l) k) (e l) :=
  (hG.hasWeakLineDerivOn (e l)).clm_comp (EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ)

end CalderonN.BallRegularity.DiffEq

namespace CalderonN.BallRegularity.DiffEq.TF

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

lemma ibp {g : (X dim) → ℝ} (h : TF g) {u u' : (X dim) → ℝ} {i : Fin dim}
    (hu : HasWeakLineDerivOn volume (fixedBallOpens dim) u u' (e i)) :
    ∫ x, g x * u' x = -∫ x, pd g i x * u x := by
  have h1 := (h.deriv i).integrable hu.locallyIntegrableOn
  have h2 := h.integrable hu.locallyIntegrableOn_deriv
  have := (h.null hu).2
  rw [integral_add h1 h2] at this
  linarith

end CalderonN.BallRegularity.DiffEq.TF

namespace CalderonN.BallRegularity.DiffEq

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

lemma lineDeriv_eq_pd (ψ : 𝓓((fixedBallOpens dim), ℝ)) (x : (X dim)) (i : Fin dim) :
    lineDeriv ℝ (ψ : (X dim) → ℝ) x (e i) = pd ψ i x :=
  ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv


lemma symmDeriv {u : (X dim) → ℝ} {G : (X dim) → (X dim)} {D : (X dim) → (X dim) →L[ℝ] (X dim)}
    (hu : HasWeakFDerivOn volume (fixedBallOpens dim) u (fun x => innerSL ℝ (G x)))
    (hG : HasWeakFDerivOn volume (fixedBallOpens dim) G D) (k l : Fin dim) :
    HasWeakLineDerivOn volume (fixedBallOpens dim) (fun x => G x k) (fun x => D x (e k) l) (e l) := by
  have h1 := vecDeriv hG l k
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, (coordDeriv hu k).locallyIntegrableOn_deriv,
    h1.locallyIntegrableOn_deriv, fun ψ => ?_⟩
  rw [← h1.integral_lineDeriv_smul_eq_neg_integral_smul ψ]
  simp only [smul_eq_mul, lineDeriv_eq_pd]
  rw [((TF.of ψ).deriv l).ibp (coordDeriv hu k), ((TF.of ψ).deriv k).ibp (coordDeriv hu l)]
  simp only [pd_pd_comm ψ.contDiff l k]


def Mf (a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (c : (X dim) → (X dim)) : (X dim) → Matrix (Fin dim) (Fin dim) ℝ :=
  fun x i k => ∑ m, a x i m * pd (fun y => c y k) m x - ∑ l, c x l * pd (fun y => a y i k) l x +
    ∑ j, a x j k * pd (fun y => c y i) j x

lemma contDiff_pd {g : (X dim) → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin dim) : ContDiff ℝ ∞ (pd g i) :=
  (hg.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma contDiff_Mf {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : (X dim) → (X dim)} (hc : ContDiff ℝ ∞ c) (i k : Fin dim) : ContDiff ℝ ∞ (fun x => Mf a c x i k) := by
  simp only [Mf]
  have hA := contDiff_entry ha
  have hC := contDiff_coord hc
  refine ((ContDiff.sum fun m _ => (hA i m).mul (contDiff_pd (hC k) m)).sub
    (ContDiff.sum fun l _ => (hC l).mul (contDiff_pd (hA i k) l))).add
    (ContDiff.sum fun j _ => (hA j k).mul (contDiff_pd (hC i) j))

lemma core {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : (X dim) → (X dim)} (hc : ContDiff ℝ ∞ c)
    (hdiv : ∀ x, ∑ l, pd (fun y => c y l) l x = 0)
    {u : (X dim) → ℝ} {G : (X dim) → (X dim)} {D : (X dim) → (X dim) →L[ℝ] (X dim)} {f : (X dim) → ℝ} {gF : (X dim) → (X dim)}
    (hu : HasWeakFDerivOn volume (fixedBallOpens dim) u (fun x => innerSL ℝ (G x)))
    (hG : HasWeakFDerivOn volume (fixedBallOpens dim) G D)
    (hF : HasWeakFDerivOn volume (fixedBallOpens dim) f (fun x => innerSL ℝ (gF x)))
    (heq : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x) (G x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), f x * φ x)
    (φ : 𝓓((fixedBallOpens dim), ℝ)) :
    ∫ x, ∑ i, ∑ k, pd φ i x * (a x i k *
        ∑ l, (c x l * D x (e k) l + G x l * pd (fun y => c y l) k x)) =
      (∫ x, (∑ l, c x l * gF x l) * φ x) + ∫ x, ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k) := by
  have hA := contDiff_entry ha
  have hC := contDiff_coord hc
  have hφ := TF.of φ
  have hGl : ∀ k, LocallyIntegrableOn (fun x => G x k) ((fixedBallOpens dim) : Set (X dim)) volume :=
    fun k => (coordDeriv hu k).locallyIntegrableOn_deriv
  have hgFl : ∀ l, LocallyIntegrableOn (fun x => gF x l) ((fixedBallOpens dim) : Set (X dim)) volume :=
    fun l => (coordDeriv hF l).locallyIntegrableOn_deriv
  have hfl : LocallyIntegrableOn f ((fixedBallOpens dim) : Set (X dim)) volume :=
    (coordDeriv hF 0).locallyIntegrableOn

  have Z1 : ∀ i k l, Null (fun x => pd (pd φ i) l x * ((a x i k * c x l) • G x k) +
      pd φ i x * ((a x i k * c x l) • D x (e k) l +
        pd (fun y => a y i k * c y l) l x • G x k)) := fun i k l =>
    (hφ.deriv i).null (HasWeakLineDerivOn.contDiff_smul (symmDeriv hu hG k l) ((hA i k).mul (hC l)))
  have hPφ : TF (fun y => ∑ l, pd φ l y * c y l) :=
    TF.sum _ fun l => (hφ.deriv l).mul (hC l)
  have Z2 : Null (fun x => ∑ i, ∑ k, (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k -
      (∑ l, pd φ l x * c x l) * f x) := by
    obtain ⟨ψP, hψP⟩ := id hPφ
    have i1 : Integrable (fun x => ∑ i, ∑ k,
        (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k) volume :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
        ((hPφ.deriv i).mul (hA i k)).integrable (hGl k)
    have i2 := hPφ.integrable hfl
    refine ⟨i1.sub i2, ?_⟩
    rw [integral_sub i1 i2, sub_eq_zero]
    have h := heq ψP
    rw [hψP] at h
    calc ∫ x, ∑ i, ∑ k, (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k
        = ∫ x in ((fixedBallOpens dim) : Set (X dim)), ∑ i, ∑ k,
            (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k :=
          integral_eq_setIntegral (fun x hx => by simp [(hPφ.deriv _).zero_of_notMem hx])
      _ = ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x)
            (gradient (fun y => ∑ l, pd φ l y * c y l) x) (G x) := by
          refine setIntegral_congr_fun (fixedBallOpens dim).isOpen.measurableSet fun x _ => ?_
          simp only [matrixBilinearForm_eq_sum, gradient_coord]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
      _ = ∫ x in ((fixedBallOpens dim) : Set (X dim)), f x * ∑ l, pd φ l x * c x l := h
      _ = ∫ x, (∑ l, pd φ l x * c x l) * f x := by
          rw [integral_eq_setIntegral (fun x hx => by simp [hPφ.zero_of_notMem hx])]
          exact setIntegral_congr_fun (fixedBallOpens dim).isOpen.measurableSet fun x _ => mul_comm _ _
  have Z3 : ∀ l, Null (fun x => pd (fun y => φ y * c y l) l x * f x + (φ x * c x l) * gF x l) :=
    fun l => (hφ.mul (hC l)).null (coordDeriv hF l)
  have hZ := ((Null.sum Finset.univ fun i => Null.sum Finset.univ fun k =>
    Null.sum Finset.univ fun l => Z1 i k l).sub Z2).sub (Null.sum Finset.univ Z3)
  have hR1 : Integrable (fun x => (∑ l, c x l * gF x l) * φ x) volume := by
    refine (integrable_finsetSum Finset.univ fun l _ => (hφ.mul (hC l)).integrable (hgFl l)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hR2 : Integrable (fun x => ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k)) volume := by
    refine (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ
      fun k _ => ((hφ.deriv i).mul (contDiff_Mf ha hc i k)).integrable (hGl k)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hpt : ∀ x, ∑ i, ∑ k, pd φ i x * (a x i k *
        ∑ l, (c x l * D x (e k) l + G x l * pd (fun y => c y l) k x)) =
      (∑ l, c x l * gF x l) * φ x + ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k) +
        (((∑ i, ∑ k, ∑ l, (pd (pd φ i) l x * ((a x i k * c x l) • G x k) +
          pd φ i x * ((a x i k * c x l) • D x (e k) l +
            pd (fun y => a y i k * c y l) l x • G x k))) -
          (∑ i, ∑ k, (pd (fun y => ∑ l, pd φ l y * c y l) i x * a x i k) * G x k -
            (∑ l, pd φ l x * c x l) * f x)) -
          ∑ l, (pd (fun y => φ y * c y l) l x * f x + (φ x * c x l) * gF x l)) := by
    intro x
    have dA : ∀ i k, DifferentiableAt ℝ (fun y => a y i k) x :=
      fun i k => ((hA i k).differentiable (by simp)) x
    have dC : ∀ l, DifferentiableAt ℝ (fun y => c y l) x :=
      fun l => ((hC l).differentiable (by simp)) x
    have dφ : ∀ l, DifferentiableAt ℝ (pd φ l) x := fun l => (hφ.deriv l).differentiableAt x
    exact alg (φ x) (f x) (∑ l, pd φ l x * c x l) (fun i => pd φ i x)
      (fun i l => pd (pd φ i) l x) (fun i k => a x i k) (fun i k l => pd (fun y => a y i k) l x)
      (fun l => c x l) (fun l m => pd (fun y => c y l) m x) (fun k => G x k)
      (fun l k => D x (e k) l) (fun l => gF x l) (fun i k l => pd (fun y => a y i k * c y l) l x)
      (fun i => pd (fun y => ∑ l, pd φ l y * c y l) i x)
      (fun l => pd (fun y => φ y * c y l) l x)
      (fun i k l => pd_mul (dA i k) (dC l) l)
      (fun i => by
        rw [pd_sum (f := fun l y => pd φ l y * c y l) _ (fun l => (dφ l).mul (dC l))]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [pd_mul (dφ l) (dC l), pd_pd_comm φ.contDiff l i])
      (fun l => pd_mul (hφ.differentiableAt x) (dC l) l) rfl (hdiv x)
  have hR12 : Integrable (fun x => (∑ l, c x l * gF x l) * φ x +
      ∑ i, ∑ k, pd φ i x * (Mf a c x i k * G x k)) volume := hR1.add hR2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hR12 hZ.1,
    hZ.2, add_zero, integral_add hR1 hR2]

lemma sum_smul_e_apply (g : Fin dim → ℝ) (k : Fin dim) : (∑ k', g k' • e k') k = g k := by
  simp [e, Pi.single_apply]

lemma memLp_mul_cont {h : (X dim) → ℝ} (hh : Continuous h) {w : (X dim) → ℝ}
    (hw : MemLp w 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))) :
    MemLp (fun x => h x * w x) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : (X dim)) 1).exists_bound_of_continuousOn
    hh.continuousOn
  refine hw.of_le_mul (c := K) (hh.aestronglyMeasurable.mul hw.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem (fixedBallOpens dim).isOpen.measurableSet fun x hx => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hK x (Metric.ball_subset_closedBall hx)) (norm_nonneg _)

lemma main_abstract {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : (X dim) → (X dim)} (hc : ContDiff ℝ ∞ c)
    (hdiv : ∀ x, ∑ l : Fin dim, fderiv ℝ c x (EuclideanSpace.single l 1) l = 0)
    (v : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2) {D : (X dim) → (X dim) →L[ℝ] (X dim)}
    (hDL : ∀ k l, MemLp (fun x => D x (e k) l) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)))
    (hG : HasWeakFDerivOn volume (fixedBallOpens dim) (W1p.gradient v) D)
    (Fw : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2)
    (heq : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient v x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), W1p.value Fw x * φ x) :
    ∃ w : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2,
      (⇑(W1p.value w) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
        fun x => ⟪c x, W1p.gradient v x⟫_ℝ) ∧
      ∃ M : (X dim) → Matrix (Fin dim) (Fin dim) ℝ, ContDiff ℝ ∞ M ∧
        ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
          ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
              (W1p.gradient w x) =
            (∫ x in ((fixedBallOpens dim) : Set (X dim)), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x) +
              ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (M x) (gradient (φ : (X dim) → ℝ) x)
                (W1p.gradient v x) := by
  have hC := contDiff_coord hc
  have hu := W1p.hasWeakFDerivOn v
  have hF := W1p.hasWeakFDerivOn Fw
  have hdiv' : ∀ x, ∑ l, pd (fun y => c y l) l x = 0 := fun x => by
    rw [← hdiv x]
    exact Finset.sum_congr rfl fun l _ => pd_coord ((hc.differentiable (by simp)) x) l l
  have hGL : ∀ l, MemLp (fun x => W1p.gradient v x l) 2
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) := fun l =>
    (EuclideanSpace.proj l : (X dim) →L[ℝ] ℝ).comp_memLp' (Lp.memLp _)
  have hval : MemLp (fun x => ∑ l, c x l * W1p.gradient v x l) 2
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    memLp_finsetSum _ fun l _ => memLp_mul_cont (hC l).continuous (hGL l)
  have hgk : ∀ k, MemLp (fun x => ∑ l, (c x l * D x (e k) l +
      W1p.gradient v x l * pd (fun y => c y l) k x)) 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    fun k => memLp_finsetSum _ fun l _ => (memLp_mul_cont (hC l).continuous (hDL k l)).add
      (by simpa only [mul_comm] using memLp_mul_cont (contDiff_pd (hC l) k).continuous (hGL l))
  have hgrad : MemLp (fun x => ∑ k, (∑ l, (c x l * D x (e k) l +
      W1p.gradient v x l * pd (fun y => c y l) k x)) • e k) 2
      ((volume : Measure (X dim)).restrict (fixedBallOpens dim)) :=
    memLp_finsetSum _ fun k _ =>
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (e k)).comp_memLp' (hgk k)).ae_eq
        (Filter.Eventually.of_forall fun x => by simp [Finset.sum_smul])
  have hw : HasWeakFDerivOn volume (fixedBallOpens dim) (⇑(hval.toLp _))
      (fun x => innerSL ℝ ((hgrad.toLp _) x)) := by
    refine (EuclideanSpace.basisFun (Fin dim) ℝ).toBasis.hasWeakFDerivOn_of_forall
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp _).locallyIntegrable (by norm_num))) fun k => ?_
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have S := HasWeakLineDerivOn.sum Finset.univ
      (fun l _ => HasWeakLineDerivOn.contDiff_smul (vecDeriv hG l k) (hC l))
    refine (S.congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [hval.coeFn_toLp] with x hx
      rw [hx]
      simp only [smul_eq_mul]
    · filter_upwards [hgrad.coeFn_toLp] with x hx
      rw [innerSL_apply_apply, hx]
      simp only [sum_inner, inner_smul_left, smul_eq_mul]
      simp [e, EuclideanSpace.inner_single_right, pd]
      exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨W1p.mk _ _ hw, ?_, Mf a c, ?_, fun φ => ?_⟩
  · rw [W1p.value_mk]
    filter_upwards [hval.coeFn_toLp] with x hx
    rw [hx]
    simp [PiLp.inner_apply, mul_comm]
  · exact contDiff_pi.2 fun i => contDiff_pi.2 fun k => contDiff_Mf ha hc i k
  · rw [W1p.gradient_mk]
    have hcore := core ha hc hdiv' hu hG hF heq φ
    have hφ := TF.of φ
    have e1 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
        ((hgrad.toLp _) x) = ∫ x, ∑ i, ∑ k, pd φ i x * (a x i k *
          ∑ l, (c x l * D x (e k) l + W1p.gradient v x l * pd (fun y => c y l) k x)) := by
      rw [integral_eq_setIntegral (fun x hx => by simp [(hφ.deriv _).zero_of_notMem hx])]
      refine integral_congr_ae ?_
      filter_upwards [hgrad.coeFn_toLp] with x hx
      rw [hx, matrixBilinearForm_eq_sum]
      simp only [gradient_coord]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [sum_smul_e_apply]
    have e2 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x =
        ∫ x, (∑ l, c x l * W1p.gradient Fw x l) * φ x := by
      rw [integral_eq_setIntegral (fun x hx => by simp [hφ.zero_of_notMem hx])]
      refine setIntegral_congr_fun (fixedBallOpens dim).isOpen.measurableSet fun x _ => ?_
      simp [PiLp.inner_apply, mul_comm]
    have e3 : ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (Mf a c x)
        (gradient (φ : (X dim) → ℝ) x) (W1p.gradient v x) =
        ∫ x, ∑ i, ∑ k, pd φ i x * (Mf a c x i k * W1p.gradient v x k) := by
      rw [integral_eq_setIntegral (fun x hx => by simp [(hφ.deriv _).zero_of_notMem hx])]
      refine setIntegral_congr_fun (fixedBallOpens dim).isOpen.measurableSet fun x _ => ?_
      rw [matrixBilinearForm_eq_sum]
      simp only [gradient_coord]
    rw [e1, e2, e3]
    exact hcore

end CalderonN.BallRegularity.DiffEq

namespace CalderonN.BallRegularity

variable {dim : ℕ} [NeZero dim]
open TauCeti TauCeti.PDE

theorem exists_diff_equation {a : (X dim) → Matrix (Fin dim) (Fin dim) ℝ} (ha : ContDiff ℝ ∞ a)
    {c : (X dim) → (X dim)} (hc : ContDiff ℝ ∞ c)
    (hdiv : ∀ x, ∑ l : Fin dim, fderiv ℝ c x (EuclideanSpace.single l 1) l = 0)
    (V : Wkp (volume : Measure (X dim)) (fixedBallOpens dim) 2 2) (Fw : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2)
    (heq : ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
      ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
          (W1p.gradient (Wkp.lowerOrder 1 V) x) =
        ∫ x in ((fixedBallOpens dim) : Set (X dim)), W1p.value Fw x * φ x) :
    ∃ w : W1p (volume : Measure (X dim)) (fixedBallOpens dim) 2,
      (⇑(W1p.value w) =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
        fun x => ⟪c x, W1p.gradient (Wkp.lowerOrder 1 V) x⟫_ℝ) ∧
      ∃ M : (X dim) → Matrix (Fin dim) (Fin dim) ℝ, ContDiff ℝ ∞ M ∧
        ∀ φ : 𝓓((fixedBallOpens dim), ℝ),
          ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (a x) (gradient (φ : (X dim) → ℝ) x)
              (W1p.gradient w x) =
            (∫ x in ((fixedBallOpens dim) : Set (X dim)), ⟪c x, W1p.gradient Fw x⟫_ℝ * φ x) +
              ∫ x in ((fixedBallOpens dim) : Set (X dim)), matrixBilinearForm (M x) (gradient (φ : (X dim) → ℝ) x)
                (W1p.gradient (Wkp.lowerOrder 1 V) x) := by
  have hG : HasWeakFDerivOn volume (fixedBallOpens dim) (W1p.gradient (Wkp.lowerOrder 1 V))
      (Wkp.iteratedGradient 1 V) := by
    have h := Wkp.hasWeakFDerivOn_iteratedGradient 0 V
    rwa [Wkp.iteratedGradient_zero] at h
  exact DiffEq.main_abstract ha hc hdiv (Wkp.lowerOrder 1 V)
    (fun k l => ((EuclideanSpace.proj l : (X dim) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ (X dim) (DiffEq.e k))).comp_memLp' (Lp.memLp _)) hG Fw heq

end CalderonN.BallRegularity
