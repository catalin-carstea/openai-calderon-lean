import Proof.AdjointLocality
import Proof.Normalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma smoothNear.add {F G : Field} {S : Set (X × X)}
    (hF : smoothNear F S) (hG : smoothNear G S) : smoothNear (fun p => F p+G p) S := by
  obtain ⟨V,hV,hSV,hFV⟩ := hF
  obtain ⟨W,hW,hSW,hGW⟩ := hG
  exact ⟨V ∩ W,hV.inter hW,fun p hp => ⟨hSV hp,hSW hp⟩,
    (hFV.mono inter_subset_left).add (hGW.mono inter_subset_right)⟩

lemma smoothNear.mul {F G : Field} {S : Set (X × X)}
    (hF : smoothNear F S) (hG : smoothNear G S) : smoothNear (fun p => F p*G p) S := by
  obtain ⟨V,hV,hSV,hFV⟩ := hF
  obtain ⟨W,hW,hSW,hGW⟩ := hG
  exact ⟨V ∩ W,hV.inter hW,fun p hp => ⟨hSV hp,hSW hp⟩,
    (hFV.mono inter_subset_left).mul (hGW.mono inter_subset_right)⟩

lemma smoothNear.neg {F : Field} {S : Set (X × X)} (hF : smoothNear F S) : smoothNear (fun p => -F p) S := by
  obtain ⟨V,hV,hSV,hFV⟩ := hF
  exact ⟨V,hV,hSV,hFV.neg⟩

lemma smoothNear.finset_sum {α : Type*} (s : Finset α) (F : α → Field) {S : Set (X × X)}
    (hF : ∀ i ∈ s,smoothNear (F i) S) : smoothNear (fun p => ∑ i ∈ s,F i p) S := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨univ,isOpen_univ,subset_univ _,by simpa using (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : X × X => (0 : ℂ)) univ)⟩
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using (hF a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

lemma smoothNear_base {Y : Set X} (hY : IsOpen Y) {g : MetricField} {f : X → ℝ}
    (hf : ContDiffOn ℝ ∞ f Y) : smoothNear (fun p : X × X => (f p.1 : ℂ)) (bundle Y g) := by
  refine ⟨Prod.fst ⁻¹' Y,hY.preimage continuous_fst,fun p hp => hp.1,?_⟩
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hf.comp contDiffOn_fst (fun p hp => hp))

lemma smoothNear_traceDerivative {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) {e : Frame} {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A) {φ : Field} (hφ : smoothNear φ (bundle Y g)) (i : I) :
    smoothNear (traceDerivative g A i φ) (bundle Y g) := by
  have hh := smoothNear_horizontalField hY h hK (fun _ j => axis j) (fun _ => contDiffOn_const) hφ i
  exact hh.add (hA i φ hφ).1

lemma traceDerivative_zero_of_support {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A) (hD : Dirichlet Y g g₁ expMap r)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) (S : Set X) (hS : IsClosed S)
    (hzero : ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,φ (y,w) = 0)
    (i : I) {y : X} (hy : y ∈ Y \ S) (w : X) (hw : w ∈ sphereAt g y) :
    traceDerivative g A i φ (y,w) = 0 := by
  unfold traceDerivative
  rw [horizontal_zero_of_sphere_support hY h hK e he hframe hφ S hS hzero hy w hw,
    hA.zero_on_sphere hD hφ i hy.1 (hframe y hy.1) (hzero y hy) w hw,add_zero]

/-- Both applications of the moving derivative retain the original compact center support.
    This uses the actual Dirichlet solvability and adjoint duality, rather than a locality axiom. -/
theorem movingTrace_zero_of_support {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ g₂ : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame) (he : ∀ i,ContDiffOn ℝ ∞ (fun y => e y i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A) (hD : Dirichlet Y g g₁ expMap r)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) (S : Set X) (hS : IsClosed S)
    (hzero : ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,φ (y,w) = 0)
    {y : X} (hy : y ∈ Y \ S) (w : X) (hw : w ∈ sphereAt g y) :
    movingTrace g g₂ r A φ (y,w) = 0 := by
  have hW (j : I) := smoothNear_traceDerivative hY h hK hA hφ j
  have hWzero (j : I) : ∀ y ∈ Y \ S,∀ w ∈ sphereAt g y,traceDerivative g A j φ (y,w) = 0 :=
    fun y hy w hw => traceDerivative_zero_of_support hY h hK e he hframe hA hD hφ S hS hzero j hy w hw
  have hWWzero (i j : I) : traceDerivative g A i (traceDerivative g A j φ) (y,w) = 0 :=
    traceDerivative_zero_of_support hY h hK e he hframe hA hD (hW j) S hS (hWzero j) i hy w hw
  simp only [movingTrace,hWWzero,hWzero _ y hy w hw,mul_zero,Finset.sum_const_zero,sub_self,add_zero]


lemma contDiffOn_principal_entry {Y : Set X} {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) (i j : I) :
    ContDiffOn ℝ ∞ (fun y => principal g g₂ y i j) Y := by
  have hden : ContDiffOn ℝ ∞ (fun y => ((g y)*(g₂ y)⁻¹).trace) Y := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
    exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (h.1 i j).mul (h₂.contDiffOn_inverse_entry hK j i)))
  have hs : ContDiffOn ℝ ∞ (fun y => 3/((g y)*(g₂ y)⁻¹).trace) Y :=
    contDiffOn_const.div hden (fun y hy => (principal_denominator_pos g g₂ y (h.posDef hK hy) (h₂.posDef hK hy)).ne')
  simpa only [principal,Matrix.smul_apply,smul_eq_mul] using hs.mul (h₂.contDiffOn_inverse_entry hK i j)

lemma contDiffOn_drift {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K) (k : I) :
    ContDiffOn ℝ ∞ (fun y => drift g g₂ y k) Y :=
  ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
    (contDiffOn_principal_entry h h₂ hK i j).mul
      ((h.contDiffOn_christoffel hY hK k i j).sub (h₂.contDiffOn_christoffel hY hK k i j))))

/-- The actual twofold moving-trace expression is smooth near the sphere bundle. -/
theorem smoothNear_movingTrace {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g g₁ g₂ : MetricField}
    (h : Elliptic Y K g) (h₂ : Elliptic Y K g₂) (hK : 0 < K)
    {e : Frame} {expMap : X × X → X} {r : X → ℝ} {A : TraceAdjoint}
    (hr : ContDiffOn ℝ ∞ r Y) (hA : IsMovingTraceAdjoint Y g g₁ e expMap r A)
    {φ : Field} (hφ : smoothNear φ (bundle Y g)) :
    smoothNear (movingTrace g g₂ r A φ) (bundle Y g) := by
  let W (j : I) := traceDerivative g A j φ
  have hW (j : I) : smoothNear (W j) (bundle Y g) := smoothNear_traceDerivative hY h hK hA hφ j
  have hΓ (k i j : I) := smoothNear_base (g:=g) hY (h.contDiffOn_christoffel hY hK k i j)
  have hcorrected (i j : I) : smoothNear (fun p => traceDerivative g A i (W j) p-
      ∑ k,(christoffel g p.1 k i j : ℂ)*W k p) (bundle Y g) := by
    simpa only [sub_eq_add_neg] using (smoothNear_traceDerivative hY h hK hA (hW j) i).add
      ((smoothNear.finset_sum Finset.univ _ (fun k _ => (hΓ k i j).mul (hW k))).neg)
  have hsecond : smoothNear (fun p => ∑ i,∑ j,(principal g g₂ p.1 i j : ℂ)*
      (traceDerivative g A i (W j) p-∑ k,(christoffel g p.1 k i j : ℂ)*W k p)) (bundle Y g) :=
    smoothNear.finset_sum Finset.univ _ (fun i _ => smoothNear.finset_sum Finset.univ _ (fun j _ =>
      (smoothNear_base hY (contDiffOn_principal_entry h h₂ hK i j)).mul (hcorrected i j)))
  have hfirst : smoothNear (fun p => ∑ k,(drift g g₂ p.1 k : ℂ)*W k p) (bundle Y g) :=
    smoothNear.finset_sum Finset.univ _ (fun k _ => (smoothNear_base hY (contDiffOn_drift hY h h₂ hK k)).mul (hW k))
  exact (smoothNear_base hY hr).mul (hsecond.add hfirst)

end ShrinkingSpheres
