import TailIndexSelect
import TouchedStars
import UniformSubforest
import SuffixRows

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Removing an edge color with matching number at most x leaves the complete
suffix starting x stars later. Its vertices retain the original copy's labels,
and the statement includes empty tails and stars with zero leaves. -/
theorem trim_touched_forest {X : Type*} [Finite X] (R K : SimpleGraph X)
    (n : ℕ → ℕ) (hn : Antitone n) (i x l : ℕ) (rank : matchingEdges K ≤ x)
    (copy : (suffixStars n i (x+l)).IsContained (R ⊔ K)) :
    (suffixStars n (i+x) l).IsContained R := by
  classical
  obtain ⟨f⟩ := copy
  let old (j : Fin (x+l)) := n (i+j.val)
  let tail (a : Fin l) := n (i+x+a.val)
  let bad := touchedStars R K old f
  have bound : bad.toFinite.toFinset.card ≤ x :=
    calc
      _ = bad.ncard := (Set.ncard_eq_toFinset_card _ _).symm
      _ ≤ x := (touchedStars_le_matchingEdges R K old f).trans rank
  obtain ⟨label,_,spec⟩ := select_good_tail_indices x l bad.toFinite.toFinset bound
  have fit (a : Fin l) : tail a ≤ old (label a) := by
    apply hn
    have offset := (spec a).2
    omega
  let sel := subforestCopy tail old label fit
  refine ⟨{ toHom := { toFun := fun z => f (sel z), map_rel' := ?_ },
            injective' := f.injective.comp sel.injective }⟩
  intro a b edge
  have survives : (sel a).1 ∉ bad := by
    change label a.1 ∉ bad
    exact fun hit => (spec a.1).1 ((Set.Finite.mem_toFinset _).mpr hit)
  exact untouched_star_adjacency R K old f survives (sel.toHom.map_adj edge)

#print axioms trim_touched_forest
end JSP452Audit.StarHost
