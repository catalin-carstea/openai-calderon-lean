import Proof.AdjointLinearity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

theorem horizontal_base_smul (g : MetricField) (f : X → ℝ) (φ : Field) (y w a : X)
    (hf : DifferentiableAt ℝ f y) (hφ : DifferentiableAt ℝ φ (y,w)) :
    horizontal g (fun p => f p.1 • φ p) y w a =
      (fderiv ℝ f y a) • φ (y,w)+f y • horizontal g φ y w a := by
  have hB := hf.hasFDerivAt.comp (y,w) (hasFDerivAt_fst (𝕜:=ℝ) (p:=(y,w)))
  have hP := hB.smul hφ.hasFDerivAt
  have hEq : (fun p : X × X => f p.1 • φ p)=(f ∘ (Prod.fst : X × X → X)) • φ := by
    funext p
    simp only [Pi.smul_apply',Function.comp_apply]
  rw [horizontal,hEq,hP.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',_root_.smul_apply,
    horizontal,Function.comp_apply]
  abel

theorem horizontal_add (g : MetricField) (φ ψ : Field) (y w a : X)
    (hφ : DifferentiableAt ℝ φ (y,w)) (hψ : DifferentiableAt ℝ ψ (y,w)) :
    horizontal g (fun p => φ p+ψ p) y w a = horizontal g φ y w a+horizontal g ψ y w a := by
  change (fderiv ℝ (φ+ψ) (y,w)) _ = _
  rw [fderiv_add hφ hψ]
  rfl

theorem Admissible.traceDerivative_base_smul {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {f : X → ℝ} (hf : ContDiffOn ℝ ∞ f Y)
    {φ : Field} (hφ : smoothNear φ (bundle Y d.γ)) (i : I) {y : X} (hy : y ∈ Y)
    {w : X} (hw : w ∈ sphereAt d.γ y) :
    traceDerivative d.γ d.adjoint i (fun p => f p.1 • φ p) (y,w) =
      coordDeriv i f y • φ (y,w)+f y • traceDerivative d.γ d.adjoint i φ (y,w) := by
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hf' := (hf.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hφ' := hφ.differentiableAt (show (y,w) ∈ bundle Y d.γ from ⟨hy,hw⟩)
  unfold traceDerivative
  rw [horizontal_base_smul d.γ f φ y w (axis i) hf' hφ',
    hd.2.2.2.1.base_smul hY hd.2.2.1 hf hφ i hy hframe w hw]
  simp only [coordDeriv,smul_add,add_assoc]

theorem Admissible.traceDerivative_add {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {φ ψ : Field} (hφ : smoothNear φ (bundle Y d.γ)) (hψ : smoothNear ψ (bundle Y d.γ))
    (i : I) {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    traceDerivative d.γ d.adjoint i (fun p => φ p+ψ p) (y,w) =
      traceDerivative d.γ d.adjoint i φ (y,w)+traceDerivative d.γ d.adjoint i ψ (y,w) := by
  have hφ' := hφ.differentiableAt (show (y,w) ∈ bundle Y d.γ from ⟨hy,hw⟩)
  have hψ' := hψ.differentiableAt (show (y,w) ∈ bundle Y d.γ from ⟨hy,hw⟩)
  unfold traceDerivative
  rw [horizontal_add d.γ φ ψ y w (axis i) hφ' hψ',hd.adjoint_add hY hφ hψ i hy w hw]
  abel

theorem Admissible.traceDerivative_zero {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (i : I) {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    traceDerivative d.γ d.adjoint i (fun _ => 0) (y,w) = 0 := by
  have hframe := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hZero : smoothNear (fun _ : X × X => (0 : ℂ)) (bundle Y d.γ) :=
    ⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩
  have hAdj := hd.2.2.2.1.zero_on_sphere hd.2.2.1 hZero i hy hframe (fun _ _ => rfl) w hw
  simp only [traceDerivative,hAdj,horizontal,add_zero]
  rw [(hasFDerivAt_const (𝕜:=ℝ) (0 : ℂ) (y,w)).fderiv]
  rfl

theorem Admissible.traceDerivative_finset_sum {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {α : Type*} (s : Finset α) (F : α → Field)
    (hF : ∀ j ∈ s,smoothNear (F j) (bundle Y d.γ))
    (i : I) {y : X} (hy : y ∈ Y) {w : X} (hw : w ∈ sphereAt d.γ y) :
    traceDerivative d.γ d.adjoint i (fun p => ∑ j ∈ s,F j p) (y,w) =
      ∑ j ∈ s,traceDerivative d.γ d.adjoint i (F j) (y,w) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
    intro hF
    simpa only [Finset.sum_empty] using hd.traceDerivative_zero i hy hw
  | @insert a s ha ih =>
    intro hF
    have hFs : ∀ j ∈ s,smoothNear (F j) (bundle Y d.γ) :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hSum := smoothNear.finset_sum s F hFs
    have hAdd := hd.traceDerivative_add hY (hF a (Finset.mem_insert_self a s)) hSum i hy hw
    rw [ih hFs] at hAdd
    simpa only [Finset.sum_insert ha] using hAdd

end ShrinkingSpheres
