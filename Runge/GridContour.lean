import Mathlib

open Complex Set Finset SimpleGraph Set

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
  hDec : ∀ v δ, Decidable (open_square v δ ∩ K).Nonempty

instance (K : Set ℂ) [Gridable K] : DecidablePred fun v ↦ (open_square v δ ∩ K).Nonempty :=
  fun v ↦ Gridable.hDec v δ

/-- This function is used to generate the slightly larger than minimal box that contains a compact set K-/
noncomputable def box (K : Set ℂ) [Gridable K] {ε : ℝ} (hε : 0 < ε) : ℂ × ℂ :=
  let max_re : ℝ := sSup (re '' K)
  let min_re : ℝ := sInf (re '' K)
  let max_im : ℝ := sSup (im '' K)
  let min_im : ℝ := sInf (im '' K)
  ⟨(min_re - ε + I * (min_im - ε)), (max_re + ε + I * (max_im + ε))⟩

-- This function is used to generate the lattice points in the box
noncomputable def mesh (s : ℂ × ℂ) {δ : ℝ} (hδ : 0 < δ): Finset ℂ :=
  let (z, w) := s
  let N : ℕ := Nat.ceil ((w.re - z.re) / δ)
  let M : ℕ := Nat.ceil ((w.im - z.im) / δ)
  let NM := Finset.product (range N) (range M)
  NM.image (fun (i, j) => (z.re + i * δ) + I * (z.im + j * δ))

/-- This function tells me when the edge between z and w has only one square that intersects K-/
noncomputable def one_common_square (K : Set ℂ) [Gridable K] (z w : ℂ) (δ : ℝ) : Prop :=
  if ‖w-z‖ = δ then
    if (w - z).re > 0 then
      ((open_square z δ ∩ K).Nonempty ∧ ¬(open_square (z - δ * I) δ ∩ K).Nonempty) ∨
      (¬(open_square z δ ∩ K).Nonempty ∧ (open_square (z - δ * I) δ ∩ K).Nonempty)
    else if (w - z).re < 0 then
      ((open_square w δ ∩ K).Nonempty ∧ ¬(open_square (w - δ * I) δ ∩ K).Nonempty) ∨
      (¬(open_square w δ ∩ K).Nonempty ∧ (open_square (w - δ * I) δ ∩ K).Nonempty)
    else if (w - z).im > 0 then
      ((open_square z δ ∩ K).Nonempty ∧ ¬(open_square (z - δ) δ ∩ K).Nonempty) ∨
      (¬(open_square z δ ∩ K).Nonempty ∧ (open_square (z - δ) δ ∩ K).Nonempty)
    else if (w - z).im < 0 then
      ((open_square w δ ∩ K).Nonempty ∧ ¬(open_square (w - δ) δ ∩ K).Nonempty) ∨
      (¬(open_square w δ ∩ K).Nonempty ∧ (open_square (w - δ) δ ∩ K).Nonempty)
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
noncomputable def contour_graph (K : Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) (V : Finset ℂ) : SimpleGraph ℂ :=
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
      by_cases h₁ : (open_square z δ ∩ K).Nonempty
      -- z square touches K
      · by_cases h₂ : (open_square (z - ↑δ * I) δ ∩ K).Nonempty
        · apply isFalse; simp [h₁, h₂]
        · apply isTrue; simp [h₁, h₂]
      -- z square does not touch K
      · by_cases h₂ : (open_square (z - ↑δ * I) δ ∩ K).Nonempty
        · apply isTrue; simp [h₁, h₂]
        · apply isFalse; simp [h₁, h₂]

    -- z.re ≤ w.re
    · by_cases h'' : w.re < z.re
      -- w.re < z.re
      · simp [h, h', h'']
        by_cases h₁ : (open_square w δ ∩ K).Nonempty
        -- w square touches K
        · by_cases h₂ : (open_square (w - ↑δ * I) δ ∩ K).Nonempty
          · apply isFalse; simp [h₁, h₂]
          · apply isTrue; simp [h₁, h₂]
        -- w square does not touch K
        · by_cases h₂ : (open_square (w - ↑δ * I) δ ∩ K).Nonempty
          · apply isTrue; simp [h₁, h₂]
          · apply isFalse; simp [h₁, h₂]

      -- ¬w.re = z.re
      · by_cases h_im : z.im < w.im
        -- z.im < w.im
        · simp [h, h', h'', h_im]
          by_cases h₁ : (open_square z δ ∩ K).Nonempty
          -- z square touches K
          · by_cases h₂ : (open_square (z - ↑δ) δ ∩ K).Nonempty
            · apply isFalse; simp [h₁, h₂]
            · apply isTrue; simp [h₁, h₂]
          -- z square does not touch K
          · by_cases h₂ : (open_square (z - ↑δ) δ ∩ K).Nonempty
            · apply isTrue; simp [h₁, h₂]
            · apply isFalse; simp [h₁, h₂]

        -- ¬z.im < w.im
        · by_cases h_im' : w.im < z.im
          -- w.im < z.im
          · simp [h, h', h'', h_im, h_im']
            by_cases h₁ : (open_square w δ ∩ K).Nonempty
            -- w square touches K
            · by_cases h₂ : (open_square (w - ↑δ) δ ∩ K).Nonempty
              · apply isFalse; simp [h₁, h₂]
              · apply isTrue; simp [h₁, h₂]
            -- w square does not touch K
            · by_cases h₂ : (open_square (w - ↑δ) δ ∩ K).Nonempty
              · apply isTrue; simp [h₁, h₂]
              · apply isFalse; simp [h₁, h₂]

          -- ¬w.im < z.im
          · apply isFalse; simp [h, h', h'', h_im, h_im']

  · apply isFalse
    apply not_and_or.mpr
    exact Or.inl h

noncomputable instance {K : Set ℂ} [Gridable K] {δ : ℝ} (hδ : 0 < δ) :
  DecidableRel fun (z w : ℂ) ↦ (contour_graph K hδ V).Adj z w := by
  intro z w
  unfold contour_graph
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
  DecidablePred fun (p : ℂ × ℂ) ↦ (contour_graph K hδ V).Adj p.1 p.2 := inferInstance


/--**Grid Contour** Is a function that approximates the contour of a compact set `K` using a grid of resolution `δ`.
  This approximate grid contour is represented as a `SimpleGraph` with vertices in the complex plane.
-/
noncomputable def grid_contour (K : Set ℂ) [Gridable K] {δ : ℝ } (hδ : 0 < δ) :=
  let ε := 2 * δ
  have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
  let box := box K hε
  let mesh : Finset ℂ := mesh box hδ
  let vertices : Finset ℂ := { v ∈ mesh | ((open_square v δ) ∩ K).Nonempty }
  contour_graph K hδ vertices

noncomputable def orient (K : Set ℂ) [Gridable K] {δ : ℝ}
    (hδ : 0 < δ) (x : ℂ × ℂ) : (ℂ × ℂ) :=
  let (z, w) := x
  if z.re < w.re then
    if (open_square z δ ∩ K).Nonempty then (z, w) else (w, z)
  else if w.re <  z.re then
    if (open_square w δ ∩ K).Nonempty then (w, z) else (z, w)
  else if z.im < w.im then
    if (open_square (z - δ) δ ∩ K).Nonempty then (z, w) else (w, z)
  else if w.im < z.im then
    if (open_square (w - δ) δ ∩ K).Nonempty then (w, z) else (z, w)
  else x

noncomputable def directedEdgeSet_oriented (K : Set ℂ) [Gridable K] {δ : ℝ}
    (hδ : 0 < δ) (V :Finset ℂ): Finset (ℂ × ℂ) :=
    ((V.product V).filter (fun p ↦ (contour_graph K hδ V).Adj p.1 p.2)).image (orient K hδ)

/-- This function evaluates the integral of a function `f` on a horizontal or vertical edge `(z,w)`-/
noncomputable def edge_integral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (e : ℂ × ℂ) : E :=
    let (z,w) := e
    if z.re = w.re then
      (∫ y : ℝ in z.im..w.im, f (z.re + y * I))     -- By defn, evaluates to - ∫ y : ℝ in w.im..z.im, f (w.re + y * I) if z.im > w.im
    else if z.im = w.im then
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I))
    else 0

/-- Given a `Gridable K` and `δ > 0`, along with function `f : ℂ → E`, this function evaluates the integral of `f`
over the `Grid_Contour` of `K`, with resolution `δ`. -/
noncomputable def grid_contour_integral {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (f : ℂ → E) (K: Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) : E :=
    let ε := 2 * δ
    have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
    let V := (mesh (box K hε) hδ).filter (fun v ↦ ((open_square v δ) ∩ K).Nonempty)
    let edges := directedEdgeSet_oriented K hδ V
    edges.sum (fun e ↦ edge_integral f e)

-- Auxiliarry function to convert a list of edges to a set of intervals
noncomputable def edge_to_interval (l : List (ℂ × ℂ)) : Set ℂ :=
    match l with
  | [] => ∅
  | (z,w)::xs =>
    if z.re = w.re then
      {z.re} ×ℂ Icc (min z.im w.im) (max z.im w.im) ∪ edge_to_interval xs
    else if z.im = w.im then
      Icc (min z.re w.re) (max z.re w.re) ×ℂ {z.im} ∪ edge_to_interval xs
    else ∅

-- This function is used to convert the edges of the contour graph into intervals
noncomputable def grid_contour_as_set (K: Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) : Set ℂ :=
    let ε := 2 * δ
    have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
    let V := (mesh (box K hε) hδ).filter (fun v ↦ ((open_square v δ) ∩ K).Nonempty)
    let edges := (directedEdgeSet_oriented K hδ V).toList
    edge_to_interval edges

--Move this to a new file soon
/-- **Separation Lemma**: Given a compact set `K` and a function `f : ℂ → ℂ` that is complex differentiable on
an open set `Ω`, containing `K`, there exists a `δ > 0` such that the integral of `(z - a)⁻¹ • f(z)` over the
grid contour of `K` is equal to `2 * π * I * f(a)`, where `a` is a point in `K` and the grid contour is
contained in `Ω \ K`.
-/
theorem seperation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} (hΩ : IsOpen Ω) (hΩK : K ⊆ Ω) [Gridable K]
  (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∃ (δ : ℝ), (∀ a ∈ K, grid_contour_integral (fun z ↦ (z - a)⁻¹ • f z) K hδ = 2 * π * I * f a) ∧
  (grid_contour_as_set K hδ ⊆ Ω \ K) := by
  let d : ℝ := sorry
  have hδ : d > 0 := by sorry
  use d
  constructor
  · intro a ha
    sorry
  · sorry

-- Two approaches to prove separation theorem
-- TODO: Every connected component of grid_contour is a cycle => need this to show that grid_contour is a "Path"
-- TODO: Every grid_contour is a union of squares => need this for CIF on Grid_Contour

-- TODO : Need some way to say that Γ ⊆ Ω \ K
/- TO do this, I need:
1. Show that no edge intersects `K`
2. Show that every edge is contained in `Ω` => The argument is that `d(K, Γ)` is less than  `d(K, Ωᶜ)`
-/
