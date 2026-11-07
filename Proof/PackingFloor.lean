import RowPotential
import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

/-- Taking one leaf in each component of an actual copy gives a real
    matching of size at least the number of stars, even in a non-induced copy. -/
theorem forest_copy_matching {I X : Type*} [Fintype I] [Finite X] (G : SimpleGraph X)
    (n : I → ℕ) (pn : ∀ i, 1≤n i) (copy : (forest n).IsContained G) :
    Fintype.card I ≤ matchingEdges G := by
  classical
  obtain ⟨f⟩ := copy
  let idx (i : I) : Fin (n i) := ⟨0,pn i⟩
  let L : I ↪ X := ⟨fun i => f (center n i), fun _ _ h => congrArg Sigma.fst (f.injective h)⟩
  let R : I ↪ X := ⟨fun i => f (leaf n ⟨i,idx i⟩), fun _ _ h => congrArg Sigma.fst (f.injective h)⟩
  have edge (i : I) : G.Adj (L i) (R i) := f.toHom.map_adj (starEdge n ⟨i,idx i⟩)
  have dis : Disjoint (Set.range L) (Set.range R) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i,rfl⟩ ⟨j,eq⟩
    exact leaf_ne_center n ⟨j,idx j⟩ i (f.injective eq)
  let M := pairFamily G L R edge
  have matchM := pairFamily_isMatching G L R edge dis
  let pairs (i : I) : M.edgeSet := ⟨s(L i,R i),Or.inl ⟨i,rfl,rfl⟩⟩
  have inject : Function.Injective pairs := by
    intro a b eq
    have e := congrArg Subtype.val eq
    change s(L a,R a) = s(L b,R b) at e
    rcases Sym2.eq_iff.mp e with ⟨h,_⟩ | ⟨h,_⟩
    · exact L.injective h
    · exact False.elim (dis.ne_of_mem (Set.mem_range_self a) (Set.mem_range_self b) h)
  have count := Nat.card_le_card_of_injective pairs inject
  rw [Nat.card_eq_fintype_card (α := I), Nat.card_coe_set_eq] at count
  exact count.trans (le_matchingEdges matchM)

/-- All-red and all-blue colorings ensure both underlying original forests occur. -/
theorem forcing_matching_floor {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (forced : Forces G (forest n) (forest m)) :
    max s t ≤ matchingEdges G := by
  have notBot {k : ℕ} (hk : 0<k) (x : Fin k → ℕ) (px : ∀ i, 1≤x i) :
      ¬(forest x).IsContained (⊥ : SimpleGraph X) := by
    let i : Fin k := ⟨0,hk⟩
    intro copy
    exact positive_star_not_in_bot (px i) ((oneStar_in_forest x i).trans copy)
  have red := forces_swap forced ⊥ bot_le
  have blue := forced ⊥ bot_le
  have cr : (forest n).IsContained G := by simpa using red.resolve_left (notBot ht m pm)
  have cb : (forest m).IsContained G := by simpa using blue.resolve_left (notBot hs n pn)
  exact max_le (by simpa using forest_copy_matching G n pn cr)
    (by simpa using forest_copy_matching G m pm cb)

#print axioms forcing_matching_floor
end JSP452Audit.StarHost
