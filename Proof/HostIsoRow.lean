import SuffixRows

namespace JSP452Audit.StarHost

open SimpleGraph

/-- Pull a red coloring back along a host isomorphism, then transport the resulting
monochromatic copy forward. The two target graphs remain fixed throughout. -/
theorem forces_of_iso {X Y A B : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    {T : SimpleGraph A} {S : SimpleGraph B} (e : G ≃g H) (h : Forces G T S) :
    Forces H T S := by
  intro R hR
  let C := R.comap e
  have sub : C ≤ G := by
    intro x y hxy
    exact e.map_rel_iff.mp (hR hxy)
  rcases h C sub with red | blue
  · exact Or.inl (red.trans (SimpleGraph.Iso.comap e.toEquiv R).isContained)
  · have pullBlue : G \ C = (H \ R).comap e := by
      ext x y
      change (G.Adj x y ∧ ¬ R.Adj (e x) (e y)) ↔
        (H.Adj (e x) (e y) ∧ ¬ R.Adj (e x) (e y))
      rw [e.map_rel_iff]
    rw [pullBlue] at blue
    exact Or.inr (blue.trans (SimpleGraph.Iso.comap e.toEquiv (H \ R)).isContained)

theorem forcingRow_of_iso {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    {s t r : ℕ} {n m : ℕ → ℕ} (e : G ≃g H) (h : ForcingRow G s t n m r) :
    ForcingRow H s t n m r := by
  intro i j l q hr hl hq pl pq
  exact forces_of_iso e (h i j l q hr hl hq pl pq)

/-- Removing the empty set from a labeled graph preserves every vertex and edge. -/
def induce_delete_empty_iso {X : Type*} (G : SimpleGraph X) :
    G ≃g G.induce {x | x ∉ (∅ : Finset X)} where
  toFun x := ⟨x, Finset.notMem_empty _⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Flatten the nested legal-vertex subtype without changing the original labels. -/
def induce_delete_insert_iso {X : Type*} [DecidableEq X] (G : SimpleGraph X)
    (U : Finset X) (v : X) (hv : v ∉ U) :
    ((G.induce {x | x ∉ U}).induce {z | z ≠ (⟨v, hv⟩ : {x : X // x ∉ U})}) ≃g
      G.induce {x | x ∉ insert v U} where
  toFun x := ⟨x.val.val, fun hx => (Finset.mem_insert.mp hx).elim
    (fun he => x.property (Subtype.ext he)) x.val.property⟩
  invFun x := ⟨⟨x.val, fun hx => x.property (Finset.mem_insert_of_mem hx)⟩,
    fun he => x.property (Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val he)))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

#print axioms forces_of_iso
#print axioms forcingRow_of_iso
#print axioms induce_delete_empty_iso
#print axioms induce_delete_insert_iso
end JSP452Audit.StarHost
