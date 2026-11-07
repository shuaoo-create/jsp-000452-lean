import StarHost
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Fin.Embedding

namespace JSP452Audit.StarHost
open SimpleGraph

/-- It is enough to check the designated center-to-leaf edges of the forest. -/
private theorem map_star_edges {I X : Type*} {n : I → ℕ} {R : SimpleGraph X}
    (g : Vertices n → X)
    (ok : ∀ l : Leaves n, R.Adj (g (center n l.1)) (g (leaf n l)))
    {a b : Vertices n} (h : (forest n).Adj a b) : R.Adj (g a) (g b) := by
  let edge : (forest n).edgeSet := ⟨s(a,b),(forest n).mem_edgeSet.mpr h⟩
  obtain ⟨l, eq⟩ := (edgeEquiv n).surjective edge
  have val := congrArg Subtype.val eq
  change s(center n l.1,leaf n l) = s(a,b) at val
  rcases Sym2.eq_iff.mp val with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ok l
  · exact (ok l).symm

/-- Removing a matching from the available colors can cost at most one leaf at
every center. The star indices, including isolated centers, are retained. -/
theorem trim_matching_copy {I X : Type*} {G R : SimpleGraph X} (M : G.Subgraph)
    (matchM : M.IsMatching) (n : I → ℕ)
    (copy : (forest (fun i => n i + 1)).IsContained (R ⊔ M.spanningCoe)) :
    (forest n).IsContained R := by
  classical
  let sizes := fun i => n i + 1
  obtain ⟨f⟩ := copy
  let red (i : I) (a : Fin (n i + 1)) :=
    R.Adj (f (center sizes i)) (f (leaf sizes ⟨i,a⟩))
  have lost (i : I) (a : Fin (n i + 1)) (bad : ¬ red i a) :
      M.Adj (f (center sizes i)) (f (leaf sizes ⟨i,a⟩)) :=
    (f.toHom.map_adj (starEdge sizes ⟨i,a⟩)).resolve_left bad
  have unique (i : I) (a b : Fin (n i + 1)) (ha : ¬ red i a) (hb : ¬ red i b) : a = b := by
    have same := f.injective (matchM.eq_of_adj_left (lost i a ha) (lost i b hb))
    exact Fin.ext (Nat.succ.inj (congrArg (fun z : Vertices sizes => z.2.val) same))
  have pivot (i : I) : ∃ x : Fin (n i + 1), ∀ a, a ≠ x → red i a := by
    by_cases ex : ∃ a, ¬ red i a
    · obtain ⟨x,hx⟩ := ex
      exact ⟨x,fun a neq => by_contra (fun ha => neq (unique i a x ha hx))⟩
    · exact ⟨0,fun a _ => by_contra (fun ha => ex ⟨a,ha⟩)⟩
  choose skip good using pivot
  let keep : Vertices n ↪ Vertices sizes :=
    Function.Embedding.sigmaMap (Function.Embedding.refl I) (fun i => (skip i).succ.succAboveEmb)
  have atCenter (i : I) : keep (center n i) = center sizes i := by
    change (⟨i, (skip i).succ.succAbove 0⟩ : Vertices sizes) = ⟨i, 0⟩
    rw [Fin.succ_succAbove_zero]
  have atLeaf (i : I) (a : Fin (n i)) :
      keep (leaf n ⟨i,a⟩) = leaf sizes ⟨i,(skip i).succAbove a⟩ := by
    change (⟨i, (skip i).succ.succAbove a.succ⟩ : Vertices sizes) = ⟨i, ((skip i).succAbove a).succ⟩
    rw [Fin.succ_succAbove_succ]
  refine ⟨{ toHom := { toFun := fun a => f (keep a), map_rel' := ?_ },
            injective' := f.injective.comp keep.injective }⟩
  apply map_star_edges
  rintro ⟨i,a⟩
  rw [atCenter,atLeaf]
  exact good i _ (Fin.succAbove_ne (skip i) a)

#print axioms trim_matching_copy
end JSP452Audit.StarHost
