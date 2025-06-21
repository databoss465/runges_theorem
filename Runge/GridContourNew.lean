import mathlib

open Complex Set Finset List
-- open Classical

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

def closed_square (z : ℂ) (δ : ℝ) : Set ℂ := Icc z.re (z.re + δ) ×ℂ Icc z.im (z.im + δ)

def open_square (z : ℂ) (δ : ℝ) : Set ℂ := Ioo z.re (z.re + δ) ×ℂ Ioo z.im (z.im + δ)

-- [Btm_Lft, Btm_Rt, Top_Rt, Top_Lft]
def squareVertices (z : ℂ) (δ : ℝ) : List ℂ :=
  [z, z + δ, z + I * δ + δ, z + δ * I]

-- [Btm, Rt, Top, Lft]
def squareEdges (z : ℂ) (δ : ℝ) : List (ℂ × ℂ) :=
  (squareVertices z δ).zip ((squareVertices z δ).rotate 1)

def L := [1,2,3,4]
#eval L.zip (L.rotate 1)

/--A typeclass for non-empty compact sets where we can decide if a given square intersects it or not-/
class Gridable (K : Set ℂ) where
  hK : IsCompact K
  hNon : K.Nonempty
  hDec : ∀ v δ, Decidable (closed_square v δ ∩ K).Nonempty

-- Declare variables, compact set `K` which is an instance of `Gridable` and a positive real `δ`
variable (K : Set ℂ) [Gridable K] (δ : ℝ) (hδ : 0 < δ)

instance: DecidablePred fun v ↦ (closed_square v δ ∩ K).Nonempty :=
  fun v ↦ Gridable.hDec v δ

#check List.range (⌊(sSup (re ''K) - sInf (re ''K)) / δ⌋₊ + 2)


/-
Creates lists of x(Re) and y(Im) coordinates of lattice points and then
takes product of the two, finally mapping to complex numbers.
-/
def meshLattice : List ℂ :=
  (List.product (List.range (⌊(sSup (re ''K) - sInf (re ''K)) / δ⌋₊ + 2)) (List.range (⌊(sSup (im ''K) - sInf (im ''K)) / δ⌋₊ + 2))).map fun (n, m) ↦
    Complex.mk (sInf (re ''K) - δ + n * δ) (sInf (im ''K) - δ + m * δ)

def coveringSquares : List ℂ :=
  (meshLattice K δ).filter fun v ↦ ((closed_square v δ) ∩ K).Nonempty

def GridContourArea : Set ℂ :=
  ⋃ v ∈ coveringSquares K δ, closed_square v δ

/-Suppose s := closed_square z δ, intersects K.
square edges z δ = [Btm, Rt, Top, Lft]
B is bdry if the square below (-δI) it doesn't touch K
R if the square to its right(+δ) doesn't touch K
T if the square above (+δI) it doesn't touch K
L if the square to its left(-δ) doesn't touch K
-/

abbrev bdry_offset_fns : List (ℂ × ℂ → ℂ) :=
  [fun e ↦ e.1 - I * δ,
    fun e ↦ e.1 + δ,
    fun e ↦ e.1 + I * δ,
    fun e ↦ e.1 - δ]

def testPoints (z : ℂ) (δ : ℝ) : List ℂ :=
  ((squareEdges z δ).zip (bdry_offset_fns δ)).map fun e ↦ e.2 e.1

def filteredSquareEdges (z : ℂ) : List (ℂ × ℂ) :=
  ((squareEdges z δ).zip (testPoints z δ)).filterMap fun (e, v) ↦
  if ((closed_square v δ) ∩ K).Nonempty then some e else none

#check List.bind
#check List.partition

def boundaryEdges : List (ℂ × ℂ) :=
  (coveringSquares K δ).flatMap (filteredSquareEdges K δ)

-- Assuming Simple Connectedness of K, Γ must be a simple closed curve
def nextEdge (e : ℂ × ℂ) (es : List (ℂ × ℂ)) : List (ℂ × ℂ) :=
  match es.find? fun e' ↦ e'.1 = e.2 with
  | none => es
  | some e' =>
    match es.partition (· ≠ e') with
    | ⟨rest, head⟩ => head ++ rest

#check List.length_append
#check List.length_eq_length_filter_add
#check funext

def EdgeSort : List (ℂ × ℂ) → List (ℂ × ℂ)
  | [] => []
  | [e] => [e]
  | [e1, e2] => if e1.2 = e2.1 then [e1, e2] else [e2, e1]
  | e :: es =>
    have : (nextEdge e es).length = es.length := by
      unfold nextEdge
      cases h : es.find? (fun e' ↦ decide (e'.1 = e.2)) with --whether I write `decide` or not, it's there
      | none => rfl
      | some e' =>
        simp only [h, partition_eq_filter_filter, length_append]
        have : (not ∘ fun x ↦ decide (x ≠ e')) = fun x ↦ !decide (x ≠ e') := by --Is this in mathlib??
          funext x
          rfl
        rw [this, add_comm, ← List.length_eq_length_filter_add]

    e :: EdgeSort (nextEdge e es)
termination_by Γ => Γ.length

/-
This functions gives me the list of edges of the GridCountourBoundary ordered in the ccw direction
-/
def GridContourEdges : List (ℂ × ℂ) :=
  EdgeSort (boundaryEdges K δ)

/-
This function gives me the list of vertices of the GridCountourBoundary ordered in the ccw direction
-/
def GridContourVertices : List ℂ :=
  (GridContourEdges K δ).map fun e ↦ e.1

#check Set.Icc_self
#check List.getD

def edgeInterval (e : ℂ × ℂ) : Set ℂ :=
  Icc e.1.re e.2.re ×ℂ Icc e.1.im e.2.im

def GridContourBoundary : Set ℂ :=
  ⋃ e ∈ GridContourEdges K δ, edgeInterval e

def parametrization (Γ' : List ℂ) :=
  fun (t : ℝ) (ht : t ∈ Icc (0 : ℝ)  1) ↦
    let n := Γ'.length
    let t' := t * n
    let k := Nat.floor t'
    let τ := t' - k
    let i := k % n
    let j := (i + 1) % n
    Γ'[i]! + τ * (Γ'[j]! - Γ'[i]!)
