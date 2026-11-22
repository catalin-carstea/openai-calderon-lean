module

public import Proof.CalderonN.Chart

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.CoordinateJets
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic

/-! The finite-expansion proof adapts `Calderon/ProfileCovariantJets.lean`
at d6704c49395a38eb07e0249afeb8ea83d67971cc to Christoffel entries in the
selected chart instead of an operator-valued auxiliary connection. -/

@[expose] public section

set_option maxSynthPendingDepth 10
noncomputable section
open scoped ContDiff InnerProductSpace Topology
namespace CalderonN.ProfileCovariant

variable {dim : ℕ}

abbrev CoordinateConnectionFamily (dim : ℕ) := Fin dim → Fin dim → Fin dim → ℝ × (X dim) → ℝ

def coordinatePartialJet (f : (X dim) → ℝ) (n : ℕ) (I : Fin n → Fin dim) (x : (X dim)) : ℝ :=
  iteratedFDeriv ℝ n f x (fun i => axis (I i))

lemma contDiff_coordinatePartialJet (f : (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (I : Fin n → Fin dim) : ContDiff ℝ ∞ (coordinatePartialJet f n I) := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => (X dim)) ℝ
    (fun i => axis (I i))).contDiff.comp (hf.iteratedFDeriv_right (by simp))

lemma abs_coordinatePartialJet_le (f : (X dim) → ℝ) (n : ℕ) (I : Fin n → Fin dim) (x : (X dim)) :
    |coordinatePartialJet f n I x| ≤ ‖iteratedFDeriv ℝ n f x‖ := by
  have h := (iteratedFDeriv ℝ n f x).le_opNorm (fun i => axis (I i))
  simpa only [coordinatePartialJet, Real.norm_eq_abs, norm_axis,
    Finset.prod_const_one, mul_one] using h

lemma fderiv_coordinatePartialJet_apply (f : (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (I : Fin n → Fin dim) (i : Fin dim) (x : (X dim)) :
    fderiv ℝ (coordinatePartialJet f n I) x (axis i) =
      coordinatePartialJet f (n + 1) (Fin.cons i I) x := by
  have hDn : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right (by simp)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x := hDn.differentiable (by simp) x
  let J : Fin (n + 1) → Fin dim := Fin.cons i I
  have h := DifferentiableAt.iteratedFDeriv_succ_apply_left' (n := n) (f := f)
    (m := fun j : Fin (n + 1) => axis (J j)) hd
  change fderiv ℝ (fun y => iteratedFDeriv ℝ n f y (fun k => axis (I k))) x
    (axis i) = _
  simpa only [coordinatePartialJet, J, Fin.cons_zero, Fin.tail_cons, Fin.tail_def,
    Fin.cons_succ] using h.symm

def baseCoefficientDerivative (a : ℝ × (X dim) → ℝ) (i : Fin dim) (z : ℝ × (X dim)) : ℝ :=
  fderiv ℝ (fun y => a (z.1, y)) z.2 (axis i)

lemma baseCoefficientDerivative_eq_total (a : ℝ × (X dim) → ℝ)
    (ha : ContDiff ℝ ∞ a) (i : Fin dim) (z : ℝ × (X dim)) :
    baseCoefficientDerivative a i z = fderiv ℝ a z (0, axis i) := by
  have hp : HasFDerivAt (fun y : (X dim) => (z.1, y)) (ContinuousLinearMap.inr ℝ ℝ (X dim)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have h := ((ha.differentiable (by simp) z).hasFDerivAt).comp z.2 hp
  change fderiv ℝ (a ∘ fun y : (X dim) => (z.1, y)) z.2 (axis i) = _
  rw [h.fderiv]
  rfl

lemma contDiff_baseCoefficientDerivative (a : ℝ × (X dim) → ℝ)
    (ha : ContDiff ℝ ∞ a) (i : Fin dim) :
    ContDiff ℝ ∞ (baseCoefficientDerivative a i) := by
  have he : baseCoefficientDerivative a i = fun z => fderiv ℝ a z (0, axis i) :=
    funext (baseCoefficientDerivative_eq_total a ha i)
  rw [he]
  exact (contDiff_infty_iff_fderiv.mp ha).2.clm_apply contDiff_const

/-- Actual coordinate covariant derivatives, with one correction per covector slot. -/
def covariantCoordinateJet (Γ : (CoordinateConnectionFamily dim)) (f : (X dim) → ℝ)
    (lam : ℝ) : (n : ℕ) → (X dim) → (Fin n → Fin dim) → ℝ
  | 0, x, _ => f x
  | n + 1, x, I =>
      fderiv ℝ (fun y => covariantCoordinateJet Γ f lam n y (Fin.tail I)) x
        (axis (I 0)) -
      ∑ l : Fin n, ∑ k : Fin dim,
        Γ k (I 0) ((Fin.tail I) l) (lam, x) *
        covariantCoordinateJet Γ f lam n x (Function.update (Fin.tail I) l k)

/-- The finite expansion controls the protected covariant derivatives on
any open slice where the supplied coefficients are its Christoffel symbols. -/
theorem covJet_eq_on {U : Set (X dim)} (hU : IsOpen U) (g : (MetricField dim))
    (Γ : (CoordinateConnectionFamily dim)) (lam : ℝ)
    (hΓ : ∀ y ∈ U, ∀ k i j, Γ k i j (lam, y) = christoffel g y k i j)
    (f : (X dim) → ℝ) (n : ℕ) (idx : Fin n → I dim) :
    Set.EqOn (fun y => covJet g f n y idx) (fun y => covariantCoordinateJet Γ f lam n y idx) U := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro y hy
    change covJet g f (n + 1) y idx = covariantCoordinateJet Γ f lam (n + 1) y idx
    rw [covJet.eq_def, covariantCoordinateJet]
    change coordDeriv (idx 0) (fun x => covJet g f n x (Fin.tail idx)) y - _ =
      coordDeriv (idx 0) (fun x => covariantCoordinateJet Γ f lam n x (Fin.tail idx)) y - _
    rw [eqOn_coordDeriv hU (ih (Fin.tail idx)) (idx 0) hy]
    congr 1
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun k _ => by
      let js := Function.update (Fin.tail idx) t k
      have h : covJet g f n y js = covariantCoordinateJet Γ f lam n y js := ih js hy
      rw [hΓ y hy]
      exact congrArg (fun a : ℝ => christoffel g y k (idx 0) (idx t.succ) * a) h


structure CoordinateJetTerm (dim : ℕ) where
  coeff : ℝ × (X dim) → ℝ
  order : ℕ
  indices : Fin order → Fin dim

def coordinateTermValue (t : (CoordinateJetTerm dim)) (f : (X dim) → ℝ) (z : ℝ × (X dim)) : ℝ :=
  t.coeff z * coordinatePartialJet f t.order t.indices z.2

def coordinateTermDerivative (i : Fin dim) (t : (CoordinateJetTerm dim)) : List (CoordinateJetTerm dim) :=
  [⟨baseCoefficientDerivative t.coeff i, t.order, t.indices⟩,
   ⟨t.coeff, t.order + 1, Fin.cons i t.indices⟩]

def coordinateTermMultiply (a : ℝ × (X dim) → ℝ) (t : (CoordinateJetTerm dim)) : (CoordinateJetTerm dim) :=
  ⟨fun z => a z * t.coeff z, t.order, t.indices⟩

def connectionCoordinateCoeff (Γ : (CoordinateConnectionFamily dim)) (i j k : Fin dim)
    (z : ℝ × (X dim)) : ℝ := Γ k i j z

def covariantCoordinateExpansion (Γ : (CoordinateConnectionFamily dim)) :
    (n : ℕ) → (Fin n → Fin dim) → List (CoordinateJetTerm dim)
  | 0, _ => [⟨fun _ => 1, 0, Fin.elim0⟩]
  | n + 1, I =>
      (covariantCoordinateExpansion Γ n (Fin.tail I)).flatMap
        (coordinateTermDerivative (I 0)) ++
      (List.ofFn (fun l : Fin n => l)).flatMap (fun l =>
        (List.ofFn (fun k : Fin dim => k)).flatMap (fun k =>
          (covariantCoordinateExpansion Γ n (Function.update (Fin.tail I) l k)).map
            (coordinateTermMultiply (fun z => -connectionCoordinateCoeff Γ (I 0) ((Fin.tail I) l) k z))))

lemma covariantCoordinateExpansion_coeff_smooth (Γ : (CoordinateConnectionFamily dim))
    (hΓ : ∀ k i j, ContDiff ℝ ∞ (Γ k i j)) (n : ℕ) (I : Fin n → Fin dim) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I, ContDiff ℝ ∞ t.coeff := by
  induction n with
  | zero =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact contDiff_const
  | succ n ih =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      simp only [coordinateTermDerivative, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact contDiff_baseCoefficientDerivative _ (ih (Fin.tail I) s hs) _
      · exact ih (Fin.tail I) s hs
    · obtain ⟨l, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact (hΓ _ _ _).neg.mul
        (ih (Function.update (Fin.tail I) l k) s hs)

lemma covariantCoordinateExpansion_order_le (Γ : (CoordinateConnectionFamily dim))
    (n : ℕ) (I : Fin n → Fin dim) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I, t.order ≤ n := by
  induction n with
  | zero =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst t
    exact le_rfl
  | succ n ih =>
    intro t ht
    simp only [covariantCoordinateExpansion, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      have h := ih (Fin.tail I) s hs
      simp only [coordinateTermDerivative, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> dsimp only <;> omega
    · obtain ⟨l, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have h := ih (Function.update (Fin.tail I) l k) s hs
      dsimp only [coordinateTermMultiply]
      omega

lemma baseCoefficientDerivative_const (c : ℝ) (i : Fin dim) :
    baseCoefficientDerivative (fun _ => c) i = 0 := by
  funext z
  simp [baseCoefficientDerivative]

lemma covariantCoordinateExpansion_zero_order_coeff (Γ : (CoordinateConnectionFamily dim))
    (n : ℕ) (I : Fin n → Fin dim) (hn : 1 ≤ n) :
    ∀ t ∈ covariantCoordinateExpansion Γ n I, t.order = 0 → t.coeff = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro t ht hz
    simp only [covariantCoordinateExpansion, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨s, hs, ht⟩ := List.mem_flatMap.mp ht
      simp only [coordinateTermDerivative, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · dsimp only at hz ⊢
        by_cases hzero : n = 0
        · subst n
          simp only [covariantCoordinateExpansion, List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact baseCoefficientDerivative_const 1 _
        · rw [ih (Fin.tail I) (by omega) s hs hz]
          exact baseCoefficientDerivative_const 0 _
      · dsimp only at hz
        omega
    · obtain ⟨l, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, _, ht⟩ := List.mem_flatMap.mp ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      have hpos : 1 ≤ n := by have h := l.isLt; omega
      have hc := ih (Function.update (Fin.tail I) l k) hpos s hs hz
      funext z
      simp only [coordinateTermMultiply, hc, Pi.zero_apply, mul_zero]

def coordinateTermsValue (ts : List (CoordinateJetTerm dim)) (f : (X dim) → ℝ) (z : ℝ × (X dim)) : ℝ :=
  (ts.map (fun t => coordinateTermValue t f z)).sum

lemma coordinateTermsValue_append (as bs : List (CoordinateJetTerm dim)) (f : (X dim) → ℝ)
    (z : ℝ × (X dim)) : coordinateTermsValue (as ++ bs) f z =
      coordinateTermsValue as f z + coordinateTermsValue bs f z := by
  simp [coordinateTermsValue]

lemma coordinateTermsValue_flatMap {ι : Type*} (xs : List ι)
    (F : ι → List (CoordinateJetTerm dim)) (f : (X dim) → ℝ) (z : ℝ × (X dim)) :
    coordinateTermsValue (xs.flatMap F) f z =
      (xs.map (fun i => coordinateTermsValue (F i) f z)).sum := by
  induction xs with
  | nil => simp [coordinateTermsValue]
  | cons x xs ih => simp [List.flatMap_cons, coordinateTermsValue_append, ih]

lemma coordinateTermsValue_multiply (a : ℝ × (X dim) → ℝ) (ts : List (CoordinateJetTerm dim))
    (f : (X dim) → ℝ) (z : ℝ × (X dim)) :
    coordinateTermsValue (ts.map (coordinateTermMultiply a)) f z =
      a z * coordinateTermsValue ts f z := by
  simp only [coordinateTermsValue, List.map_map, Function.comp_def,
    coordinateTermValue, coordinateTermMultiply, mul_assoc, List.sum_map_mul_left]

lemma contDiff_coordinateTermsValue_slice (ts : List (CoordinateJetTerm dim))
    (hcoeff : ∀ t ∈ ts, ContDiff ℝ ∞ t.coeff)
    (f : (X dim) → ℝ) (hf : ContDiff ℝ ∞ f) (lam : ℝ) :
    ContDiff ℝ ∞ (fun x => coordinateTermsValue ts f (lam, x)) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih =>
    have ht : ContDiff ℝ ∞ (fun x : (X dim) => coordinateTermValue t f (lam, x)) :=
      ((hcoeff t (by simp)).comp (contDiff_const.prodMk contDiff_id)).mul
      (contDiff_coordinatePartialJet f hf t.order t.indices)
    have hts := ih (fun s hs => hcoeff s (by simp [hs]))
    exact ht.add hts

lemma fderiv_coordinateTermValue_slice_apply (t : (CoordinateJetTerm dim))
    (ht : ContDiff ℝ ∞ t.coeff) (f : (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (x : (X dim)) (i : Fin dim) :
    fderiv ℝ (fun y => coordinateTermValue t f (lam, y)) x (axis i) =
      coordinateTermsValue (coordinateTermDerivative i t) f (lam, x) := by
  have ha : ContDiff ℝ ∞ (fun y : (X dim) => t.coeff (lam, y)) :=
    ht.comp (contDiff_const.prodMk contDiff_id)
  have hJ := contDiff_coordinatePartialJet f hf t.order t.indices
  unfold coordinateTermValue
  rw [fderiv_fun_mul (c := fun y => t.coeff (lam, y))
    (d := coordinatePartialJet f t.order t.indices)
    (ha.differentiable (by simp) x) (hJ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_coordinatePartialJet_apply f hf]
  simp only [coordinateTermsValue, coordinateTermDerivative, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, coordinateTermValue, baseCoefficientDerivative, add_zero]
  ring

lemma fderiv_coordinateTermsValue_slice_apply (ts : List (CoordinateJetTerm dim))
    (hcoeff : ∀ t ∈ ts, ContDiff ℝ ∞ t.coeff)
    (f : (X dim) → ℝ) (hf : ContDiff ℝ ∞ f) (lam : ℝ) (x : (X dim)) (i : Fin dim) :
    fderiv ℝ (fun y => coordinateTermsValue ts f (lam, y)) x (axis i) =
      coordinateTermsValue (ts.flatMap (coordinateTermDerivative i)) f (lam, x) := by
  induction ts with
  | nil => simp [coordinateTermsValue]
  | cons t ts ih =>
    have ht : ContDiff ℝ ∞ (fun y => coordinateTermValue t f (lam, y)) :=
      ((hcoeff t (by simp)).comp (contDiff_const.prodMk contDiff_id)).mul
        (contDiff_coordinatePartialJet f hf t.order t.indices)
    have hrest := contDiff_coordinateTermsValue_slice ts
      (fun s hs => hcoeff s (by simp [hs])) f hf lam
    have he : (fun y => coordinateTermsValue (t :: ts) f (lam, y)) =
        fun y => coordinateTermValue t f (lam, y) + coordinateTermsValue ts f (lam, y) := by
      funext y
      simp only [coordinateTermsValue, List.map_cons, List.sum_cons]
    rw [he, fderiv_fun_add (ht.differentiable (by simp) x) (hrest.differentiable (by simp) x)]
    simp only [add_apply, List.flatMap_cons, coordinateTermsValue_append]
    rw [fderiv_coordinateTermValue_slice_apply t (hcoeff t (by simp)) f hf,
      ih (fun s hs => hcoeff s (by simp [hs]))]

theorem covariantCoordinateJet_eq_expansion (Γ : (CoordinateConnectionFamily dim))
    (hΓ : ∀ k i j, ContDiff ℝ ∞ (Γ k i j)) (f : (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (lam : ℝ) (n : ℕ) (I : Fin n → Fin dim) (x : (X dim)) :
    covariantCoordinateJet Γ f lam n x I =
      coordinateTermsValue (covariantCoordinateExpansion Γ n I) f (lam, x) := by
  induction n generalizing x with
  | zero => simp [covariantCoordinateJet, covariantCoordinateExpansion,
      coordinateTermsValue, coordinateTermValue, coordinatePartialJet]
  | succ n ih =>
    have he : (fun y => covariantCoordinateJet Γ f lam n y (Fin.tail I)) =
        fun y => coordinateTermsValue (covariantCoordinateExpansion Γ n (Fin.tail I)) f (lam, y) :=
      funext (fun y => ih (Fin.tail I) y)
    rw [covariantCoordinateJet, he,
      fderiv_coordinateTermsValue_slice_apply _
        (covariantCoordinateExpansion_coeff_smooth Γ hΓ _ _) f hf]
    rw [covariantCoordinateExpansion]
    rw [coordinateTermsValue_append, coordinateTermsValue_flatMap]
    simp only [coordinateTermsValue_flatMap, List.map_ofFn, Function.comp_def, List.sum_ofFn,
      coordinateTermsValue_multiply, ih, connectionCoordinateCoeff, neg_mul, Finset.sum_neg_distrib]
    ring

def covariantExpansionCoeffSum (Γ : (CoordinateConnectionFamily dim)) (n : ℕ)
    (I : Fin n → Fin dim) (z : ℝ × (X dim)) : ℝ :=
  ((covariantCoordinateExpansion Γ n I).map (fun t => |t.coeff z|)).sum

lemma covariantExpansionCoeffSum_nonneg (Γ : (CoordinateConnectionFamily dim))
    (n : ℕ) (I : Fin n → Fin dim) (z : ℝ × (X dim)) :
    0 ≤ covariantExpansionCoeffSum Γ n I z := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
  exact abs_nonneg _

lemma continuous_covariantExpansionCoeffSum (Γ : (CoordinateConnectionFamily dim))
    (hΓ : ∀ k i j, ContDiff ℝ ∞ (Γ k i j)) (n : ℕ) (I : Fin n → Fin dim) :
    Continuous (covariantExpansionCoeffSum Γ n I) := by
  have hs := covariantCoordinateExpansion_coeff_smooth Γ hΓ n I
  have hgen : ∀ ts : List (CoordinateJetTerm dim),
      (∀ t ∈ ts, ContDiff ℝ ∞ t.coeff) →
      Continuous (fun z => (ts.map (fun t => |t.coeff z|)).sum) := by
    intro ts
    induction ts with
    | nil => intro _; exact continuous_const
    | cons t ts ih =>
      intro ht
      exact (ht t (by simp)).continuous.abs.add (ih (fun s hs => ht s (by simp [hs])))
  exact hgen _ hs

lemma abs_coordinateTermsValue_le_of_jets (ts : List (CoordinateJetTerm dim))
    (horder : ∀ t ∈ ts, t.order ≤ n)
    (hzero : ∀ t ∈ ts, t.order = 0 → t.coeff = 0)
    (f : (X dim) → ℝ) (z : ℝ × (X dim)) (beta B J : ℝ)
    (hbeta : 0 ≤ beta) (hB : 1 ≤ B) (hBa : 1 ≤ B * beta) (hJ : 0 ≤ J)
    (hjets : ∀ k : ℕ, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f z.2‖ ≤ J * beta ^ k) :
    |coordinateTermsValue ts f z| ≤
      (ts.map (fun t => |t.coeff z|)).sum * J * (B * beta) ^ n := by
  have hterm : ∀ t ∈ ts, |coordinateTermValue t f z| ≤
      |t.coeff z| * J * (B * beta) ^ n := by
    intro t ht
    by_cases hz : t.order = 0
    · simp [coordinateTermValue, hzero t ht hz]
    · have hp : beta ^ t.order ≤ (B * beta) ^ n := by
        have hmul : beta ≤ B * beta := by nlinarith
        exact (pow_le_pow_left₀ hbeta hmul _).trans (pow_le_pow_right₀ hBa (horder t ht))
      have h := (abs_coordinatePartialJet_le f t.order t.indices z.2).trans
        ((hjets t.order (by omega) (horder t ht)).trans
          (mul_le_mul_of_nonneg_left hp hJ))
      have hm := mul_le_mul_of_nonneg_left h (abs_nonneg (t.coeff z))
      simpa only [coordinateTermValue, abs_mul, mul_assoc] using hm
  have hgen : ∀ us : List (CoordinateJetTerm dim),
      (∀ t ∈ us, |coordinateTermValue t f z| ≤ |t.coeff z| * J * (B * beta) ^ n) →
      |coordinateTermsValue us f z| ≤
        (us.map (fun t => |t.coeff z|)).sum * J * (B * beta) ^ n := by
    intro us
    induction us with
    | nil => intro _; simp [coordinateTermsValue]
    | cons t us ih =>
      intro ht
      have hfirst := ht t (by simp)
      have hrest := ih (fun s hs => ht s (by simp [hs]))
      simp only [coordinateTermsValue, List.map_cons, List.sum_cons] at hrest ⊢
      exact (abs_add_le _ _).trans (by nlinarith)
  exact hgen _ hterm

theorem exists_covariantCoordinateJet_compact_bound (Γ : (CoordinateConnectionFamily dim))
    (hΓ : ∀ k i j, ContDiff ℝ ∞ (Γ k i j)) (n : ℕ) (hn : 1 ≤ n) (K : Set (X dim)) (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ∀ I : Fin n → Fin dim, ∀ f : (X dim) → ℝ, ContDiff ℝ ∞ f →
      ∀ beta B J : ℝ, 0 ≤ beta → 1 ≤ B → 1 ≤ B * beta → 0 ≤ J →
      (∀ k : ℕ, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ J * beta ^ k) →
      |covariantCoordinateJet Γ f lam n x I| ≤ A * J * B ^ n * beta ^ n := by
  let S : ℝ × (X dim) → ℝ := fun z => ∑ I : Fin n → Fin dim, covariantExpansionCoeffSum Γ n I z
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro I _
    exact continuous_covariantExpansionCoeffSum Γ hΓ n I
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro lam hlam x hx I f hf beta B J hbeta hB hBa hJ hjets
  rw [covariantCoordinateJet_eq_expansion Γ hΓ f hf]
  have h := abs_coordinateTermsValue_le_of_jets _
    (covariantCoordinateExpansion_order_le Γ n I)
    (covariantCoordinateExpansion_zero_order_coeff Γ n I hn)
    f (lam, x) beta B J hbeta hB hBa hJ hjets
  have hcoeff : covariantExpansionCoeffSum Γ n I (lam, x) ≤ max C 0 := by
    have hsingle : covariantExpansionCoeffSum Γ n I (lam, x) ≤ S (lam, x) := by
      exact Finset.single_le_sum (s := Finset.univ) (a := I)
        (f := fun J => covariantExpansionCoeffSum Γ n J (lam, x))
        (fun J _ => covariantExpansionCoeffSum_nonneg Γ n J _) (Finset.mem_univ I)
    exact hsingle.trans (((le_abs_self _).trans (hC (lam, x) ⟨hlam, hx⟩)).trans (le_max_left _ _))
  have hm := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ J * (B * beta) ^ n from
      mul_nonneg hJ (pow_nonneg (mul_nonneg (show 0 ≤ B by linarith) hbeta) n))
  have he : (max C 0) * (J * (B * beta) ^ n) = max C 0 * J * B ^ n * beta ^ n := by
    rw [mul_pow]
    ring
  rw [he] at hm
  exact h.trans (by simpa only [covariantExpansionCoeffSum, mul_assoc] using hm)

end CalderonN.ProfileCovariant
