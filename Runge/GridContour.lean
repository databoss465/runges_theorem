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

-- TODO: CIF for the complex square (after proven for the rectangle)

-- Grid contour
structure Grid where
  squares : Finset ℂ    -- Bottom left corners of the squares
  vertices : List ℂ     -- ccw Vertex list of total contour
  side : ℝ              -- Side length of the squares
  h₁ : side > 0
  h₂ : squares.Nonempty

-- TODO: function to add squares and update vertex list

--TODO: Define Grid Contour as an Inductive Type (maybe inductive type is better?)
--TODO: Recursive(?) Vertex Updating algorithm







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

/--If ‖w-z‖ ≠ δ return none
   If (w -z).re > 0 : return ((open_square z δ ∩ K).Nonempty ∧ ¬(open_square (z- δ * I) δ ∩ K).Nonempty) ∨ (¬(open_square z δ ∩ K).Nonempty ∧ (open_square (z- δ * I) δ ∩ K).Nonempty)
   If (w -z).re < 0 : return ((open_square w δ ∩ K).Nonempty ∧ ¬(open_square (w- δ * I) δ ∩ K).Nonempty) ∨ (¬(open_square w δ ∩ K).Nonempty ∧ (open_square (w- δ * I) δ ∩ K).Nonempty)
   If (w -z).im > 0 : return ((open_square z δ ∩ K).Nonempty ∧ ¬(open_square (z - δ) δ ∩ K).Nonempty) ∨ (¬(open_square z δ ∩ K).Nonempty ∧ (open_square (z - δ) δ ∩ K).Nonempty)
   If (w -z).im < 0 : return ((open_square w δ ∩ K).Nonempty ∧ ¬(open_square (w - δ) δ ∩ K).Nonempty) ∨ (¬(open_square w δ ∩ K).Nonempty ∧ (open_square (w - δ) δ ∩ K).Nonempty)
-/
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

/--**Grid Contour** Is a function that takes a compact set `K` and gives me all the edges that bound it-/
noncomputable def Grid_Contour (K : Set ℂ) [Gridable K] {δ : ℝ } (hδ : 0 < δ) : SimpleGraph ℂ :=
  let ε := 2 * δ
  have hε : 0 < ε := by apply mul_pos; linarith; exact hδ
  let box := box K hε
  let mesh := mesh box hδ
  let vertices := { v ∈ mesh | ((open_square v δ) ∩ K).Nonempty }
  contour_graph K hδ vertices

-- TODO: Every connected component of Grid_Contour is a cycle
-- We need this because later we will show that any

-- TODO: fun SimpleGraph ℂ ↦ E [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (Integration along the edges)

-- TODO: Integral of union of squares?

-- TODO: This function is same as summing over integral of all the squares!
