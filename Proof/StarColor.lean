import StarHost
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

namespace JSP452Audit.StarHost
open SimpleGraph
variable {I J : Type*} (n : I → ℕ) (L : J → ℕ)

/-- Indices of the leaves joined to this host center in the specified color. -/
abbrev Colored (C : SimpleGraph (Vertices L)) (j : J) :=
  {a : Fin (L j) // C.Adj (center L j) (leaf L ⟨j,a⟩)}

private def withCenter {a b : ℕ} (e : Fin a ↪ Fin b) : Fin (a+1) ↪ Fin (b+1) where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  inj' := by
    intro x y
    refine Fin.cases ?_ (fun i => ?_) x <;> refine Fin.cases ?_ (fun j => ?_) y
    · simp
    · simp [Ne.symm (Fin.succ_ne_zero (e j))]
    · simp
    · simp [e.injective.eq_iff]

/-- Enough same-color leaves at distinct specified host centers give a genuine
    non-induced copy of the entire required forest, including isolated centers. -/
theorem contained_of_center_counts (C : SimpleGraph (Vertices L)) (f : I ↪ J)
    (enough : ∀ i, n i ≤ Nat.card (Colored L C (f i))) :
    (forest n).IsContained C := by
  classical
  let pick (i : I) : Fin (n i) ↪ Colored L C (f i) :=
    (Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact enough i)).some
  let idx (i : I) : Fin (n i) ↪ Fin (L (f i)) := (pick i).trans (Function.Embedding.subtype _)
  let vmap : Vertices n ↪ Vertices L := Function.Embedding.sigmaMap f (fun i => withCenter (idx i))
  refine ⟨⟨⟨vmap,?_⟩,vmap.injective⟩⟩
  intro x y h
  let e : (forest n).edgeSet := ⟨s(x,y),(forest n).mem_edgeSet.mpr h⟩
  obtain ⟨⟨i,l⟩,eq⟩ := (edgeEquiv n).surjective e
  have ends : s(center n i, leaf n ⟨i,l⟩) = s(x,y) := congrArg Subtype.val eq
  have selected : C.Adj (vmap (center n i)) (vmap (leaf n ⟨i,l⟩)) := (pick i l).property
  rcases Sym2.eq_iff.mp ends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact selected
  · exact selected.symm

/-- Every leaf of a host center is red or blue exactly once. -/
theorem colors_partition (R : SimpleGraph (Vertices L)) (j : J) :
    Nat.card (Colored L R j) + Nat.card (Colored L (forest L \ R) j) = L j := by
  classical
  let pred (a : Fin (L j)) := R.Adj (center L j) (leaf L ⟨j,a⟩)
  have equiv : Colored L (forest L \ R) j ≃ {a : Fin (L j) // ¬ pred a} :=
    Equiv.subtypeEquivRight fun a =>
      ⟨fun h => h.2,fun h => ⟨starEdge L ⟨j,a⟩,h⟩⟩
  rw [Nat.card_congr equiv]
  change Nat.card {a // pred a} + Nat.card {a // ¬ pred a} = L j
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_fin]
  have b : Fintype.card {a // pred a} ≤ L j := by
    simpa using Fintype.card_le_of_injective (fun a : {a // pred a} => a.val) Subtype.val_injective
  omega

#print axioms contained_of_center_counts
#print axioms colors_partition
end JSP452Audit.StarHost
