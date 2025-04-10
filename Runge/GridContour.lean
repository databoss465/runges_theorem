import Mathlib

open Complex Set Finset SimpleGraph

set_option linter.unusedVariables false

-- A square in the complex plane
structure complex_square where
  btm_left : ℂ    -- Bottom left corner
  side : ℝ        -- Side length
  h₁ : side > 0

def unit_square : complex_square := ⟨0, 1, by linarith⟩
#check unit_square

-- The vertices of a complex square listed in a counter-clockwise order
def complex_sq_vertices (s: complex_square) : List ℂ :=
  [s.btm_left,
    s.btm_left + s.side,
    s.btm_left + s.side + s.side * I,
    s.btm_left + s.side * I]

#eval complex_sq_vertices unit_square   --Essentially [0, 1, 1 + i, i] but it doesn't look like that

def complex_sq_as_set (s: complex_square) : Set ℂ :=
  Ico s.btm_left.re (s.btm_left.re + s.side) ×ℂ Ico s.btm_left.im (s.btm_left.im + s.side)

def complex_sq_interior (s: complex_square) : Set ℂ :=
  let z := s.btm_left
  let w := s.btm_left + s.side * (1 + I) -- Top-right corner
 (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im))

def complex_sq_closure (s: complex_square) : Set ℂ :=
  let z := s.btm_left
  let w := s.btm_left + s.side * (1 + I) -- Top-right corner
  uIcc z.re w.re ×ℂ uIcc z.im w.im

-- Integral of a function over a complex square
noncomputable def complex_sq_boundary_integral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (s : complex_square) : E :=
  let z := s.btm_left
  let w := s.btm_left + s.side * (1 + I) -- Top-right corner
  (((∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * Complex.I)) - ∫ (x : ℝ) in
  z.re..w.re, f (↑x + ↑w.im * Complex.I)) + Complex.I • ∫ (y : ℝ) in z.im..w.im, f
  (↑w.re + ↑y * Complex.I)) - Complex.I • ∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * Complex.I)

noncomputable def complex_sq_boundary_integral' {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (s : complex_square) : E :=
  let vs := complex_sq_vertices s
  have h₁ : vs.length = 4 := by rfl
  (∫ x in vs[0].re..vs[1].re, f (x + vs[0].im * I)) - (∫ x in vs[3].re..vs[2].re, f (x + vs[2].im * I)) +
  I • ((∫ y in vs[1].im..vs[2].im, f (vs[1].re + y * I)) - (∫ y in vs[0].im..vs[3].im, f (vs[3].re + y * I)))

theorem complex_sq_boundary_integral_eq_zero {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (s : complex_square) (hC : ContinuousOn f (complex_sq_closure s))
    (hD : DifferentiableOn ℂ f (complex_sq_interior s)) :
    complex_sq_boundary_integral f s = 0 := by
    let z := s.btm_left
    let w := s.btm_left + s.side * (1 + I) -- Top-right corner
    apply Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    exact hC
    exact hD





-- **NEW APPROACH**

noncomputable def open_square (s : ℂ) (δ : ℝ) : Set ℂ := Ioo (s.re) (s.re + δ) ×ℂ Ioo (s.im) (s.im + δ)

noncomputable def closed_square (s : ℂ) (δ : ℝ) : Set ℂ := Icc (s.re) (s.re + δ) ×ℂ Icc (s.im) (s.im + δ)

/--A typeclass for compact sets where we can decide if a given square intersects it or not-/
class Gridable (K : Set ℂ) where
  hK : IsCompact K
  hDec : ∀ v δ, Decidable (closed_square v δ ∩ K).Nonempty

instance (K : Set ℂ) [Gridable K] : DecidablePred fun v ↦ (closed_square v δ ∩ K).Nonempty :=
  fun v ↦ Gridable.hDec v δ

/-- This function is used to generate the slightly larger than minimal Box that contains a compact set K-/
noncomputable def Box (K : Set ℂ) [Gridable K] {ε : ℝ} (hε : 0 < ε) : ℂ × ℂ :=
  let max_re : ℝ := sSup (re '' K)
  let min_re : ℝ := sInf (re '' K)
  let max_im : ℝ := sSup (im '' K)
  let min_im : ℝ := sInf (im '' K)
  ⟨(min_re - ε + I * (min_im - ε)), (max_re + ε + I * (max_im + ε))⟩

-- This function is used to generate the lattice points in the Box
noncomputable def Mesh (s : ℂ × ℂ) {δ : ℝ} (hδ : 0 < δ): Finset ℂ :=
  let (z, w) := s
  let N : ℕ := Nat.ceil ((w.re - z.re) / δ)
  let M : ℕ := Nat.ceil ((w.im - z.im) / δ)
  let NM := Finset.product (range N) (range M)
  NM.image (fun (i, j) => (z.re + i * δ) + I * (z.im + j * δ))

/-- This function tells me when the edge between z and w has only one square that intersects K-/
noncomputable def one_common_square (K : Set ℂ) [Gridable K] (z w : ℂ) (δ : ℝ) : Prop :=
  if ‖w-z‖ = δ then
    if (w - z).re > 0 then
      ((closed_square z δ ∩ K).Nonempty ∧ ¬(closed_square (z - δ * I) δ ∩ K).Nonempty) ∨
      (¬(closed_square z δ ∩ K).Nonempty ∧ (closed_square (z - δ * I) δ ∩ K).Nonempty)
    else if (w - z).re < 0 then
      ((closed_square w δ ∩ K).Nonempty ∧ ¬(closed_square (w - δ * I) δ ∩ K).Nonempty) ∨
      (¬(closed_square w δ ∩ K).Nonempty ∧ (closed_square (w - δ * I) δ ∩ K).Nonempty)
    else if (w - z).im > 0 then
      ((closed_square z δ ∩ K).Nonempty ∧ ¬(closed_square (z - δ) δ ∩ K).Nonempty) ∨
      (¬(closed_square z δ ∩ K).Nonempty ∧ (closed_square (z - δ) δ ∩ K).Nonempty)
    else if (w - z).im < 0 then
      ((closed_square w δ ∩ K).Nonempty ∧ ¬(closed_square (w - δ) δ ∩ K).Nonempty) ∨
      (¬(closed_square w δ ∩ K).Nonempty ∧ (closed_square (w - δ) δ ∩ K).Nonempty)
    else false
  else false


lemma one_common_square_symm_fwd {K : Set ℂ} [Gridable K] : one_common_square K z w δ → one_common_square K w z δ := by
  unfold one_common_square
  intro h
  by_cases h₁ : ‖w - z‖ = δ
  -- ‖w-z‖ = δ
  · simp [h₁] at h
    simp [h₁]
    by_cases h₂ : z.re < w.re
    -- z.re < w.re
    · simp [h₂] at h
      simp [h₂]
      constructor
      · rw [← neg_sub, norm_neg]
        exact h₁
      · have h₃ : ¬ (w.re < z.re) := by linarith
        simp [h₃]
        exact h

    -- ¬z.re < w.re
    · have h₃ : w.re < z.re ∨ w.re = z.re := by
        apply LE.le.lt_or_eq
        apply le_of_not_gt
        linarith
      cases h₃ with
      | inl h₃ =>
        simp [h₃, h₂] at h
        simp [h₁, h₂, h₃]
        constructor
        · rw [← neg_sub, norm_neg]
          exact h₁
        · exact h
      | inr h₃ =>
        have h' : ¬w.re < z.re := by linarith
        simp [h₁, h₂, h₃] at h
        simp [h₁, h₂, h₃]
        constructor
        · rw [← neg_sub, norm_neg]
          exact h₁
        · by_cases h₄ : z.im < w.im
          -- z.im < w.im
          · simp [h₄] at h
            have h₅ : ¬w.im < z.im := by linarith
            simp [h₄, h₅]
            exact h

          -- ¬z.im < w.im
          · have h₄ : w.im < z.im ∨ w.im = z.im := by
              apply LE.le.lt_or_eq
              apply le_of_not_gt
              linarith
            have h' : ¬z.im < w.im := by linarith
            cases h₄ with
            | inl h₄ =>
              simp [h₄, h'] at h
              simp [h₄, h']
              exact h

            | inr h₄ =>
              simp [h₄, h']  at h

  -- ‖w-z‖ ≠ δ
  ·  simp [h₁] at h

theorem one_common_square_symm {K : Set ℂ} [Gridable K] : one_common_square K z w δ ↔ one_common_square K w z δ := by
  constructor
  · exact one_common_square_symm_fwd

  · intro h
    exact one_common_square_symm_fwd h

/-- **Contour Graph** is a function that represents the contour, of a compact set `K` approximated by axis-aligned
line segemnts using a grid of resolution `δ`, as a simple graph with adjacency given by the conjuction of `‖z-w‖=δ` and
the proposition that only one square with edge `z w` intersects K
-/
noncomputable def ContourGraph (K : Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) (V : Finset ℂ) : SimpleGraph ℂ :=
{ Adj := fun z w ↦ (‖z-w‖ = δ) ∧ (one_common_square K z w δ),
  symm := by
    intros z w h
    constructor
    · rw [← neg_sub, norm_neg]
      exact h.1

    · rw [one_common_square_symm]
      exact h.2

  loopless := by
    intros z h
    rw [sub_self] at h
    rw [norm_zero] at h
    have h' : 0 ≠ δ := by linarith
    exact h' h.1
   }

--Fix this later (if possible). It's very ugly
noncomputable instance {K : Set ℂ} [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  DecidableRel fun z w ↦ one_common_square K z w δ := by
  intro z w
  simp [one_common_square]
  by_cases h : ‖w- z‖ = δ

  · by_cases h' : z.re < w.re
    -- z.re < w.re
    · simp [h, h']
      by_cases h₁ : (closed_square z δ ∩ K).Nonempty
      -- z square touches K
      · by_cases h₂ : (closed_square (z - ↑δ * I) δ ∩ K).Nonempty
        · apply isFalse; simp [h₁, h₂]
        · apply isTrue; simp [h₁, h₂]
      -- z square does not touch K
      · by_cases h₂ : (closed_square (z - ↑δ * I) δ ∩ K).Nonempty
        · apply isTrue; simp [h₁, h₂]
        · apply isFalse; simp [h₁, h₂]

    -- z.re ≤ w.re
    · by_cases h'' : w.re < z.re
      -- w.re < z.re
      · simp [h, h', h'']
        by_cases h₁ : (closed_square w δ ∩ K).Nonempty
        -- w square touches K
        · by_cases h₂ : (closed_square (w - ↑δ * I) δ ∩ K).Nonempty
          · apply isFalse; simp [h₁, h₂]
          · apply isTrue; simp [h₁, h₂]
        -- w square does not touch K
        · by_cases h₂ : (closed_square (w - ↑δ * I) δ ∩ K).Nonempty
          · apply isTrue; simp [h₁, h₂]
          · apply isFalse; simp [h₁, h₂]

      -- ¬w.re = z.re
      · by_cases h_im : z.im < w.im
        -- z.im < w.im
        · simp [h, h', h'', h_im]
          by_cases h₁ : (closed_square z δ ∩ K).Nonempty
          -- z square touches K
          · by_cases h₂ : (closed_square (z - ↑δ) δ ∩ K).Nonempty
            · apply isFalse; simp [h₁, h₂]
            · apply isTrue; simp [h₁, h₂]
          -- z square does not touch K
          · by_cases h₂ : (closed_square (z - ↑δ) δ ∩ K).Nonempty
            · apply isTrue; simp [h₁, h₂]
            · apply isFalse; simp [h₁, h₂]

        -- ¬z.im < w.im
        · by_cases h_im' : w.im < z.im
          -- w.im < z.im
          · simp [h, h', h'', h_im, h_im']
            by_cases h₁ : (closed_square w δ ∩ K).Nonempty
            -- w square touches K
            · by_cases h₂ : (closed_square (w - ↑δ) δ ∩ K).Nonempty
              · apply isFalse; simp [h₁, h₂]
              · apply isTrue; simp [h₁, h₂]
            -- w square does not touch K
            · by_cases h₂ : (closed_square (w - ↑δ) δ ∩ K).Nonempty
              · apply isTrue; simp [h₁, h₂]
              · apply isFalse; simp [h₁, h₂]

          -- ¬w.im < z.im
          · apply isFalse; simp [h, h', h'', h_im, h_im']

  · apply isFalse
    apply not_and_or.mpr
    exact Or.inl h

noncomputable instance {K : Set ℂ} [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  DecidableRel fun (z w : ℂ) ↦ (ContourGraph K hδ V).Adj z w := by
  intro z w
  unfold ContourGraph
  simp
  by_cases h : ‖z - w‖ = δ
  · by_cases h' : one_common_square K z w δ
    · exact isTrue ⟨h, h'⟩
    · apply isFalse
      apply not_and_or.mpr
      exact Or.inr h'

  · by_cases h' : one_common_square K z w δ
    · apply isFalse
      apply not_and_or.mpr
      exact Or.inl h
    · apply isFalse
      apply not_and_or.mpr
      exact Or.inl h

noncomputable instance {K : Set ℂ} [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  DecidablePred fun (p : ℂ × ℂ) ↦ (ContourGraph K hδ V).Adj p.1 p.2 := inferInstance


/--**Grid Contour** Is a function that approximates the contour of a compact set `K` using a grid of resolution `δ`.
  This approximate grid contour is represented as a `SimpleGraph` with vertices in the complex plane.
-/
noncomputable def GridContour (K : Set ℂ) [Gridable K] {δ : ℝ } (hδ : 0 < δ) :=
  let ε := 2 * δ
  have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
  let Box := Box K hε
  let Mesh : Finset ℂ := Mesh Box hδ
  let vertices : Finset ℂ := { v ∈ Mesh | ((closed_square v δ) ∩ K).Nonempty }
  ContourGraph K hδ vertices

noncomputable def Orient (K : Set ℂ) [Gridable K] {δ : ℝ}
    (hδ : 0 < δ) (x : ℂ × ℂ) : (ℂ × ℂ) :=
  let (z, w) := x
  if z.re < w.re then
    if (closed_square z δ ∩ K).Nonempty then (z, w) else (w, z)
  else if w.re <  z.re then
    if (closed_square w δ ∩ K).Nonempty then (w, z) else (z, w)
  else if z.im < w.im then
    if (closed_square (z - δ) δ ∩ K).Nonempty then (z, w) else (w, z)
  else if w.im < z.im then
    if (closed_square (w - δ) δ ∩ K).Nonempty then (w, z) else (z, w)
  else x

lemma orient_canonical (K: Set ℂ) [Gridable K] {δ : ℝ}
    (hδ : 0 < δ) (p : ℂ × ℂ) (h_orient : Orient K hδ p = (z,w)) : p = (z,w) ∨ p = (w,z) := by
    let (a,b) := p
    unfold Orient at h_orient
    by_cases h₁ : a.re < b.re
    -- a.re < b.re
    · by_cases h₂ : (closed_square a δ ∩ K).Nonempty
      -- a square touches K
      · simp [h₁, h₂] at h_orient
        left
        simp
        exact h_orient

      · simp [h₁, h₂] at h_orient
        right
        simp
        exact ⟨h_orient.2, h_orient.1⟩

    -- ¬a.re < b.re
    · have h₁' : b.re < a.re ∨ b.re = a.re := by
        apply LE.le.lt_or_eq
        apply le_of_not_gt
        linarith
      cases h₁' with
      | inl h₁' =>
        by_cases h₂ : (closed_square b δ ∩ K).Nonempty
        -- b square touches K
        · simp [h₁, h₁', h₂] at h_orient
          right
          simp
          exact ⟨h_orient.2, h_orient.1⟩
        -- b square does not touch K
        · simp [h₁, h₁', h₂] at h_orient
          left
          simp
          exact h_orient

      | inr h₁' =>
        have h₁'' : ¬b.re < a.re := by linarith
        by_cases h₃ : a.im < b.im
        -- a.im < b.im
        · by_cases h₄ : (closed_square (a - ↑δ) δ ∩ K).Nonempty
          -- a square touches K
          · simp [h₁, h₁'', h₃, h₄] at h_orient
            left
            simp
            exact h_orient
          · simp [h₁, h₁'', h₃, h₄] at h_orient
            right
            simp
            exact ⟨h_orient.2, h_orient.1⟩

        · have h₃' : b.im < a.im ∨ b.im = a.im := by
            apply LE.le.lt_or_eq
            apply le_of_not_gt
            linarith
          cases h₃' with
          | inl h₃' =>
            by_cases h₄ : (closed_square (b - ↑δ) δ ∩ K).Nonempty
            · simp [h₁, h₁'', h₃, h₃', h₄] at h_orient
              right
              simp
              exact ⟨h_orient.2, h_orient.1⟩
            · simp [h₁, h₁'', h₃, h₃', h₄] at h_orient
              left
              simp
              exact h_orient

          | inr h₃' =>
            have h₄ : ¬b.im < a.im := by linarith
            simp [h₁, h₁'', h₃, h₄] at h_orient
            left
            simp
            exact h_orient

noncomputable def DirectedEdgeSetOriented (K : Set ℂ) [Gridable K] {δ : ℝ}
    (hδ : 0 < δ) (V :Finset ℂ): Finset (ℂ × ℂ) :=
    ((V.product V).filter (fun p ↦ (ContourGraph K hδ V).Adj p.1 p.2)).image (Orient K hδ)

lemma mem_directed_edge_set (K : Set ℂ) [Gridable K] {δ : ℝ}
    (hδ : 0 < δ) (V :Finset ℂ): (z,w) ∈ DirectedEdgeSetOriented K hδ V → (ContourGraph K hδ V).Adj z w := by
    intro h
    unfold DirectedEdgeSetOriented at h
    obtain ⟨p, hp_mem, hp_eq⟩ := Finset.mem_image.mp h --This works but obtain ⟨(a,b), hp_mem, hp_eq⟩ := Finset.mem_image.mp h doesn't
    obtain ⟨hp_mem', hp_adj⟩ := Finset.mem_filter.mp hp_mem
    have h₁ : p = (z,w) ∨ p = (w,z) := orient_canonical K hδ p hp_eq
    cases h₁ with
    | inl h₁ =>
      rw [h₁] at hp_adj
      exact hp_adj
    | inr h₁ =>
      simp [h₁] at hp_adj
      apply (ContourGraph K hδ V).symm
      exact hp_adj

/-- This function evaluates the integral of a function `f` on a horizontal or vertical edge `(z,w)`-/
noncomputable def EdgeIntegral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (e : ℂ × ℂ) : E :=
    let (z,w) := e
    if z.re = w.re then
      (∫ y : ℝ in z.im..w.im, f (z.re + y * I))     -- By defn, evaluates to - ∫ y : ℝ in w.im..z.im, f (w.re + y * I) if z.im > w.im
    else if z.im = w.im then
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I))
    else 0

/-- Given a `Gridable K` and `δ > 0`, along with function `f : ℂ → E`, this function evaluates the integral of `f`
over the `GridContour` of `K`, with resolution `δ`. -/
noncomputable def GridContourIntegral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (K: Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) : E :=
    let ε := 2 * δ
    have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
    let V := (Mesh (Box K hε) hδ).filter (fun v ↦ ((closed_square v δ) ∩ K).Nonempty)
    let edges := DirectedEdgeSetOriented K hδ V
    edges.sum (fun e ↦ EdgeIntegral f e)

-- Auxiliary function to convert an edge into an interval
noncomputable def edgeInterval (e : ℂ × ℂ) : Set ℂ :=
    let (z,w) := e
    if z.re = w.re then
      {z.re} ×ℂ Icc (min z.im w.im) (max z.im w.im)
    else if z.im = w.im then
      Icc (min z.re w.re) (max z.re w.re) ×ℂ {z.im}
    else ∅

#check Norm ℂ

-- Edge Intervals don't touch K
lemma edge_interval_inter_empty (K : Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) (h : one_common_square K z w δ):
     edgeInterval (z,w) ∩ K = ∅ := by
    by_contra h_contra
    rw [←ne_eq, ←Set.nonempty_iff_ne_empty] at h_contra
    unfold one_common_square at h
    by_cases h₁ : z.re < w.re

    -- z.re < w.re
    · simp [h₁] at h
      let ⟨ha, hb⟩ := h
      have h' : ¬z.re = w.re := by linarith
      unfold edgeInterval at h_contra
      by_cases h₂ : z.im = w.im
      · simp [h', h₁, h₂] at h_contra
        unfold closed_square at h
        have hzw : w.re = z.re + δ := by
          rw [norm_def (w - z), normSq_apply, sub_im, h₂, sub_self] at ha
          simp at ha
          rw [Real.sqrt_mul_self] at ha
          linarith
          simp [h₁]
          exact LT.lt.le h₁
        rw [min_eq_left_of_lt h₁, max_eq_right_of_lt h₁, ← h₂, hzw] at h_contra
        have h_sub : (Icc (z.re) (z.re + δ) ×ℂ {z.im} ∩ K) ⊆ (closed_square z δ ∩ K) := by
          apply Set.inter_subset_inter
          · unfold closed_square
            apply reProdIm_subset_iff.mpr
            apply prod_mono_right
            apply Set.singleton_subset_iff.mpr
            simp
            exact LT.lt.le hδ
          · rfl
        have h_sub' : (Icc (z.re) (z.re + δ) ×ℂ {z.im} ∩ K) ⊆ (closed_square (z - δ * I) δ ∩ K) := by
          apply Set.inter_subset_inter
          · unfold closed_square
            simp
            apply reProdIm_subset_iff.mpr
            rw [← hzw]
            apply prod_mono_right
            apply Set.singleton_subset_iff.mpr
            simp
            exact LT.lt.le hδ
          · rfl
        have h_final' := Set.Nonempty.mono h_sub h_contra
        have h_final := Set.Nonempty.mono h_sub' h_contra
        simp [h_final, h_final'] at hb

      · simp [h', h₁, h₂] at h_contra

    · have h₁' : w.re < z.re ∨ w.re = z.re := by
        apply LE.le.lt_or_eq
        apply le_of_not_gt
        linarith
      cases h₁' with

      -- w.re < z.re
      | inl h₁' =>
        simp [h₁, h₁'] at h
        let ⟨ha, hb⟩ := h
        have h' : ¬z.re = w.re := by linarith
        unfold edgeInterval at h_contra
        by_cases h₂ : z.im = w.im
        · simp [h', h₁, h₂] at h_contra
          unfold closed_square at h
          have hzw : z.re = w.re + δ := by
            rw [norm_def (w - z), normSq_apply, sub_im, h₂, sub_self] at ha
            simp at ha
            rw [Real.sqrt_mul_self_eq_abs, abs_eq] at ha
            cases ha
            · linarith
            · linarith
            exact LT.lt.le hδ
          rw [min_comm, min_eq_left_of_lt h₁', max_comm, max_eq_right_of_lt h₁', hzw] at h_contra
          have h_sub : (Icc (w.re) (w.re + δ) ×ℂ {w.im} ∩ K) ⊆ (closed_square w δ ∩ K) := by
            apply Set.inter_subset_inter
            · unfold closed_square
              apply reProdIm_subset_iff.mpr
              apply prod_mono_right
              apply Set.singleton_subset_iff.mpr
              simp
              exact LT.lt.le hδ
            · rfl
          have h_sub' : (Icc (w.re) (w.re + δ) ×ℂ {w.im} ∩ K) ⊆ (closed_square (w - δ * I) δ ∩ K) := by
            apply Set.inter_subset_inter
            · unfold closed_square
              simp
              apply reProdIm_subset_iff.mpr
              rw [← hzw]
              apply prod_mono_right
              apply Set.singleton_subset_iff.mpr
              simp
              exact LT.lt.le hδ
            · rfl
          have h_final' := Set.Nonempty.mono h_sub h_contra
          have h_final := Set.Nonempty.mono h_sub' h_contra
          simp [h_final, h_final'] at hb

        · simp [h', h₁, h₂] at h_contra

      -- w.re = z.re
      | inr h₁' =>
        have h' : ¬w.re < z.re := by linarith
        simp [h₁, h'] at h
        by_cases h₃ : z.im < w.im

        -- z.im < w.im
        · simp [h₃] at h
          let ⟨ha, hb⟩ := h
          have h'' : ¬w.im = z.im := by linarith
          unfold edgeInterval at h_contra
          simp [h₁', h''] at h_contra
          unfold closed_square at h
          have hzw : w.im = z.im + δ := by
            rw [norm_def (w - z), normSq_apply, sub_re, h₁'] at ha
            simp at ha
            rw [Real.sqrt_mul_self] at ha
            linarith
            simp [h₃]
            exact LT.lt.le h₃
          rw [min_eq_left_of_lt h₃, max_eq_right_of_lt h₃, ← h₁', hzw] at h_contra
          have h_sub : ({w.re} ×ℂ Icc (z.im) (z.im + δ) ∩ K) ⊆ (closed_square z δ ∩ K) := by
            apply Set.inter_subset_inter
            · unfold closed_square
              apply reProdIm_subset_iff.mpr
              rw [h₁']
              apply prod_mono_left
              apply Set.singleton_subset_iff.mpr
              simp
              exact LT.lt.le hδ
            · rfl
          have h_sub' : ({w.re} ×ℂ Icc (z.im) (z.im + δ) ∩ K) ⊆ (closed_square (z - δ) δ ∩ K) := by
            apply Set.inter_subset_inter
            · unfold closed_square
              simp
              apply reProdIm_subset_iff.mpr
              rw [h₁']
              apply prod_mono_left
              apply Set.singleton_subset_iff.mpr
              simp
              exact LT.lt.le hδ
            · rfl
          have h_final := Set.Nonempty.mono h_sub h_contra
          have h_final' := Set.Nonempty.mono h_sub' h_contra
          simp [h_final, h_final'] at hb

        · have h₃' : w.im < z.im ∨ w.im = z.im := by
            apply LE.le.lt_or_eq
            apply le_of_not_gt
            linarith
          cases h₃' with

          -- w.im < z.im
          | inl h₃' =>
            simp [h₃', h₁, h₁', h₃] at h
            let ⟨ha, hb⟩ := h
            have h'' : ¬w.im = z.im := by linarith
            unfold edgeInterval at h_contra
            simp [h₁', h₃, h''] at h_contra
            unfold closed_square at h
            have hzw : z.im = w.im + δ := by
              rw [norm_def (w - z), normSq_apply, sub_re, h₁'] at ha
              simp at ha
              rw [Real.sqrt_mul_self_eq_abs, abs_eq] at ha
              cases ha
              · linarith
              · linarith
              exact LT.lt.le hδ
            rw [min_comm, min_eq_left_of_lt h₃', max_comm, max_eq_right_of_lt h₃', hzw] at h_contra
            have h_sub : ({z.re} ×ℂ Icc (w.im) (w.im + δ) ∩ K) ⊆ (closed_square w δ ∩ K) := by
              apply Set.inter_subset_inter
              · unfold closed_square
                apply reProdIm_subset_iff.mpr
                rw [h₁']
                apply prod_mono_left
                apply Set.singleton_subset_iff.mpr
                simp
                exact LT.lt.le hδ
              · rfl
            have h_sub' : ({z.re} ×ℂ Icc (w.im) (w.im + δ) ∩ K) ⊆ (closed_square (w - δ) δ ∩ K) := by
              apply Set.inter_subset_inter
              · unfold closed_square
                simp
                apply reProdIm_subset_iff.mpr
                rw [h₁']
                apply prod_mono_left
                apply Set.singleton_subset_iff.mpr
                simp
                exact LT.lt.le hδ
              · rfl
            have h_final := Set.Nonempty.mono h_sub h_contra
            have h_final' := Set.Nonempty.mono h_sub' h_contra
            simp [h_final, h_final'] at hb

          -- w.im = z.im
          | inr h₃' =>
            have h'' : ¬w.im < z.im := by linarith
            simp [h₁, h₁', h₃, h'' ] at h


-- This function is used to convert the edges of the contour graph into intervals
noncomputable def GridContourSet (K: Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) : Set ℂ :=
    let ε := 2 * δ
    have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
    let V := (Mesh (Box K hε) hδ).filter (fun v ↦ ((closed_square v δ) ∩ K).Nonempty)
    let edges := (DirectedEdgeSetOriented K hδ V)
    ⋃ e ∈ edges, edgeInterval e
