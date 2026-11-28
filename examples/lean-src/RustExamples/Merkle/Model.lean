module

/-! # A pure model of the Merkle tree

A level of the tree is a list of digests, and the node hash is a function
`nd : D → D → D`. `nextLevel` builds the level above a level,
`levelsFrom` lists every level from the leaves up, `topOf` is the top
level and `proofFrom` the siblings on a leaf's path. `innerRootF` is what
the verifier computes from a node and a proof.

Nothing here mentions the extracted code. The other modules show that the
Rust functions compute these functions. The Merkle argument for completeness
is `innerRootF_proofFrom`, a statement about lists alone.
-/

@[expose] public section

namespace examples.merkle
namespace Model

variable {D : Type _}

/-- The level above `l`: adjacent pairs are hashed with `nd` and an odd last
node moves up unchanged. -/
def nextLevel (nd : D → D → D) : List D → List D
  | [] => []
  | [a] => [a]
  | a :: b :: rest => nd a b :: nextLevel nd rest

@[grind =] theorem nextLevel_length (nd : D → D → D) (l : List D) :
    (nextLevel nd l).length = (l.length + 1) / 2 := by
  fun_induction nextLevel nd l <;> grind

theorem nextLevel_of_length_le (nd : D → D → D) (l : List D) (h : l.length ≤ 1) :
    nextLevel nd l = l := by
  fun_cases nextLevel nd l <;> grind

/-- The levels from `l` up to the top, as `Tree::new` builds them. -/
def levelsFrom (nd : D → D → D) (l : List D) : List (List D) :=
  if 1 < l.length then l :: levelsFrom nd (nextLevel nd l) else [l]
termination_by l.length
decreasing_by grind

/-- The top level above `l`. -/
def topOf (nd : D → D → D) (l : List D) : List D :=
  if 1 < l.length then topOf nd (nextLevel nd l) else l
termination_by l.length
decreasing_by grind

/-- The sibling of the node at `i` on level `l`, if it has one. -/
def sib (l : List D) (i : Nat) : Option D :=
  if i % 2 = 1 then l[i - 1]? else l[i + 1]?

/-- The siblings on the path of the node at `i` on level `l` up to the top. -/
def proofFrom (nd : D → D → D) (l : List D) (i : Nat) : List D :=
  if 1 < l.length then (sib l i).toList ++ proofFrom nd (nextLevel nd l) (i / 2) else []
termination_by l.length
decreasing_by grind

/-- Hashes `acc`, the node at `i`, with its sibling `s`. -/
def stepF (nd : D → D → D) (i : Nat) (acc s : D) : D :=
  if i % 2 = 1 then nd s acc else nd acc s

/-- What the loop of `inner_root` computes from the node `acc` at `i` on a
level of `w` nodes and the remaining proof `p`: the node at the top of the
path, or `none` if `p` is too short or too long. -/
def innerRootF (nd : D → D → D) (w i : Nat) (acc : D) (p : List D) : Option D :=
  if 1 < w then
    if i % 2 = 1 ∨ i + 1 < w then
      match p with
      | [] => none
      | s :: p => innerRootF nd ((w + 1) / 2) (i / 2) (stepF nd i acc s) p
    else innerRootF nd ((w + 1) / 2) (i / 2) acc p
  else if p = [] then some acc else none
termination_by w
decreasing_by all_goals grind

/-- One step of `innerRootF` on the suffix `p.drop j`, stated with `p[j]` and
`p.drop (j + 1)` as the loops read the proof: by index. -/
theorem innerRootF_drop (nd : D → D → D) (w i : Nat) (acc : D) (p : List D) (j : Nat)
    (hj : j ≤ p.length) :
    innerRootF nd w i acc (p.drop j) =
      if 1 < w then
        if i % 2 = 1 ∨ i + 1 < w then
          if h : j < p.length then
            innerRootF nd ((w + 1) / 2) (i / 2) (stepF nd i acc p[j]) (p.drop (j + 1))
          else none
        else innerRootF nd ((w + 1) / 2) (i / 2) acc (p.drop j)
      else if j = p.length then some acc else none := by
  rw [innerRootF.eq_def]
  grind [List.drop_eq_getElem_cons, List.drop_eq_nil_iff]

/-- The parent of the node `a` at `i`: `a` hashed with its sibling, or `a`
itself if it has none. -/
theorem nextLevel_getElem? (nd : D → D → D) (l : List D) (i : Nat) (a : D)
    (h : l[i]? = some a) :
    (nextLevel nd l)[i / 2]? = some ((sib l i).elim a (stepF nd i a)) := by
  fun_induction nextLevel nd l generalizing i
  · simp at h
  · grind [sib]
  · match i with
    | 0 => simp_all [sib, stepF]
    | 1 => simp_all [sib, stepF]
    | j + 2 => grind [sib, stepF]

theorem levelsFrom_getLast (nd : D → D → D) (l : List D) :
    (levelsFrom nd l).getLast? = some (topOf nd l) := by
  fun_induction levelsFrom nd l <;> grind [topOf, levelsFrom]

theorem levelsFrom_getElem?_zero (nd : D → D → D) (l : List D) :
    (levelsFrom nd l)[0]? = some l := by
  grind [levelsFrom]

theorem levelsFrom_getElem?_last (nd : D → D → D) (l : List D) :
    (levelsFrom nd l)[(levelsFrom nd l).length - 1]? = some (topOf nd l) := by
  rw [← List.getLast?_eq_getElem?]; exact levelsFrom_getLast nd l

theorem levelsFrom_length_pos (nd : D → D → D) (l : List D) :
    0 < (levelsFrom nd l).length := by
  grind [levelsFrom]

theorem topOf_length (nd : D → D → D) (l : List D) :
    (topOf nd l).length = min l.length 1 := by
  fun_induction topOf nd l <;> grind

/-- **Completeness of the model.** From the node `a` at `i` on level `l` and
the honest proof for it, `innerRootF` recomputes the first node of the top
level. -/
theorem innerRootF_proofFrom (nd : D → D → D) (l : List D) (i : Nat) (a : D)
    (h : l[i]? = some a) :
    innerRootF nd l.length i a (proofFrom nd l i) = (topOf nd l).head? := by
  fun_induction proofFrom nd l i generalizing a
  · rename_i l i hl ih
    rw [topOf]
    simp only [hl, ↓reduceIte]
    rw [← ih _ (nextLevel_getElem? nd l i a h), innerRootF.eq_def]
    grind [sib]
  · rw [innerRootF.eq_def, topOf]
    grind [List.head?_eq_getElem?]

end Model
end examples.merkle
